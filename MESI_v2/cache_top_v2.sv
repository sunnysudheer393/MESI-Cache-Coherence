// =============================================================================
// cache_top_v2.sv  (parameterized)
//
// Top-Level: N caches + Shared Bus with cache-to-cache data transfers
//
// Parameters (set once here, propagated to all sub-modules):
//   ADDR_WIDTH   â€“ CPU address width        (default 8)
//   INDEX_BITS   â€“ cache line index bits    (default 2 â†’ 4 lines)
//   OFFSET_BITS  â€“ block offset bits        (default 2 â†’ 4 words / line)
//   DATA_WIDTH   â€“ word width               (default 8 â†’ 1 byte / word)
//   N_CACHES     â€“ number of cache/CPU pairs (default 2)
//
// Scaling examples:
//   32-bit address, 6-bit index (64 lines), 4-bit offset (16 words), 32-bit data:
//     ADDR_WIDTH=32, INDEX_BITS=6, OFFSET_BITS=4, DATA_WIDTH=32
//
// Cache-to-Cache Transfer Flow (unchanged from non-parameterized version):
//   1. CPU[i] reads address X â†’ cache[i] misses â†’ issues BusRd
//   2. bus_v2 broadcasts BusRd + X to all caches
//   3. Cache[j] (jâ‰ i) snoops, checks line_tag[snoop_index]==snoop_tag
//      â†’ asserts supply_valid + supply_data (full BUS_DATA_W block)
//   4. bus_v2 muxes supply_data[j] â†’ data_out / data_valid
//   5. cache[i] (bus_owner) sees bus_data_valid â†’ loads full line into storage
//   6. cache[j] transitions its MESI state (Mâ†’S, Eâ†’S, etc.)
// =============================================================================

`include "mesi_types.sv"
import mesi_types::*;

module cache_top_v2 #(
    parameter int ADDR_WIDTH  = 8,
    parameter int INDEX_BITS  = 2,
    parameter int OFFSET_BITS = 2,
    parameter int DATA_WIDTH  = 8,
    parameter int N_CACHES    = 2
)(
    input  logic                            clk,
    input  logic                            rst,

    // ----------  CPU Interface (N_CACHES CPUs)  ----------
    input  logic                            cpu_read       [N_CACHES],
    input  logic                            cpu_write      [N_CACHES],
    input  logic [ADDR_WIDTH-1:0]           address,
    input  logic [DATA_WIDTH-1:0]           cpu_write_data,

    // ----------  Outputs to CPUs  ----------
    output logic [DATA_WIDTH-1:0]           data_out       [N_CACHES],
    output logic                            cache_hit      [N_CACHES]
);

    // =========================================================================
    // Derived Constants (computed at top; passed to sub-modules)
    // =========================================================================
    localparam int BUS_DATA_W = DATA_WIDTH * (1 << OFFSET_BITS);

    // =========================================================================
    // Internal Bus Wires
    // =========================================================================

    // Cache â†’ Bus
    bus_request                     bus_cmd_in  [N_CACHES];
    logic [ADDR_WIDTH-1:0]          bus_addr_in [N_CACHES];

    // Bus â†’ Caches (broadcast)
    bus_request                     bus_cmd_out;
    logic [ADDR_WIDTH-1:0]          bus_addr_out;
    logic [N_CACHES-1:0]            bus_owner;        // one-hot
    logic [N_CACHES-1:0]            exclusive;

    // Data bus (bus data mux â†’ all caches)
    logic [BUS_DATA_W-1:0]          bus_data_out;
    logic                           bus_data_valid;

    // =========================================================================
    // Cache-to-Cache Supply Wires (each cache â†’ bus mux)
    // =========================================================================
    logic [BUS_DATA_W-1:0]          supply_data  [N_CACHES];
    logic                           supply_valid [N_CACHES];

    //Memory signals
    logic [BUS_DATA_W-1:0]          mem_data_in;
    logic mem_data_valid;

    //Dirty Eviction and cpu stall signals
    logic [N_CACHES-1:0] dirty_eviction;
    logic [N_CACHES-1:0] cpu_stall;

    // mem_req_active: one-shot FF that arms when a bus transaction starts and
    // disarms when memory delivers data.  Without this gate, mem_read would stay
    // high for 2 cycles (grant cycle AND fill cycle) because bus_cmd_out is a
    // registered FF that doesn't clear until the cycle AFTER data_valid asserts.
    // The result would be a spurious second memory read and a false mem_ready
    // pulse that can trigger ghost fills on back-to-back bus transactions.
    logic mem_read;
    logic mem_req_active, any_supply_valid;
    assign any_supply_valid = supply_valid[0] || supply_valid[1];

    always_ff @(posedge clk or posedge rst) begin
        if (rst)
            mem_req_active <= 1'b0;
        // Arm: new transaction started (bus owner just granted, data not here yet)
        else if (|bus_owner && !mem_data_valid && !any_supply_valid)
            mem_req_active <= 1'b1;
        // Disarm: memory has delivered its response
        else if (mem_data_valid || any_supply_valid) // P0-fix: also disarm if a cache supplies data (no mem response expected)
            mem_req_active <= 1'b0;
    end

    // One-shot: active only while a request is in-flight and data hasn't arrived.
    assign mem_read = mem_req_active && !mem_data_valid;

    // =========================================================================
    // Generate N_CACHES cache instances
    // =========================================================================
    genvar i;
    generate
        for (i = 0; i < N_CACHES; i++) begin : gen_caches
            cache_mem_v2 #(
                .ADDR_WIDTH  (ADDR_WIDTH),
                .INDEX_BITS  (INDEX_BITS),
                .OFFSET_BITS (OFFSET_BITS),
                .DATA_WIDTH  (DATA_WIDTH)
            ) cache_inst (
                .clk            (clk),
                .rst            (rst),
                // CPU
                .cpu_read       (cpu_read[i]),
                .cpu_write      (cpu_write[i]),
                .address        (address),
                .cpu_write_data (cpu_write_data),
                // Bus control
                .bus_cmd_in     (bus_cmd_out),
                .bus_addr_in    (bus_addr_out),
                .bus_owner      (bus_owner[i]),
                .exclusive  (exclusive[i]),
                // Bus data (fill)
                .bus_data_in    (bus_data_out),
                .bus_data_valid (bus_data_valid),
                // CPU outputs
                .data_out       (data_out[i]),
                .cache_hit      (cache_hit[i]),
                // Bus command outputs
                .bus_cmd_out    (bus_cmd_in[i]),
                .bus_addr_out   (bus_addr_in[i]),
                // Cache-to-cache supply
                .supply_data    (supply_data[i]),
                .supply_valid   (supply_valid[i]),
                .dirty_eviction (dirty_eviction[i]),
                .cpu_stall      (cpu_stall[i])
            );
        end
    endgenerate

    // =========================================================================
    // Shared Bus
    // =========================================================================
    bus_v2 #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .BUS_DATA_W (BUS_DATA_W),
        .N_CACHES   (N_CACHES)
    ) shared_bus (
        .clk          (clk),
        .rst          (rst),
        // Command / address
        .cmd_in       (bus_cmd_in),
        .bus_addr     (bus_addr_in),
        // Supply
        .supply_data  (supply_data),
        .supply_valid (supply_valid),
        // Broadcast
        .cmd_out      (bus_cmd_out),
        .addr_out     (bus_addr_out),
        .bus_owner    (bus_owner),
        .exclusive(exclusive),

        //Memory signals
        .mem_data_in (mem_data_in),
        .mem_data_valid (mem_data_valid),

        // Data bus
        .data_out     (bus_data_out),
        .data_valid   (bus_data_valid)
    );



    // =========================================================================
    // Memory (single shared memory for all caches)
    // =========================================================================
    data_memory #(
        .ADDR_WIDTH(ADDR_WIDTH), 
        .BUS_DATA_W(BUS_DATA_W)
    ) mem_model (
        .clk(clk), .rst(rst),
        .read(mem_read),
        .write(1'b0), // This simple model does not support memory writes
        .address(bus_addr_out),
        .data_in({BUS_DATA_W{1'b0}}), // No data input for reads
        .data_out(mem_data_in),  // â† wire in cache_top_v2 scope
        .mem_ready(mem_data_valid) // â† wire in cache_top_v2 scope
    );

endmodule
