// =============================================================================
// bus_v2.sv  (parameterized)
//
// Shared Bus with Cache-to-Cache Data Mux
//
// Parameters
//   ADDR_WIDTH    â€“ address bus width          (must match cache_mem_v2)
//   BUS_DATA_W    â€“ data bus width = DATA_WIDTH * 2^OFFSET_BITS
//                   (passed from cache_top_v2 to stay in sync)
//   N_CACHES      â€“ number of caches on the bus (default 2)
//
// Key features:
//   - Priority arbitration (Cache 0 > Cache 1 > ... > Cache N-1)
//   - Combinational data mux: first cache to assert supply_valid wins;
//     its full-block data goes onto data_out immediately
//   - Registered cmd/addr outputs break any combinational loop
// =============================================================================

`include "mesi_types.sv"
import mesi_types::*;

module bus_v2 #(
    parameter int ADDR_WIDTH = 8,
    parameter int BUS_DATA_W = 32,    // DATA_WIDTH * BLOCK_SIZE, set by top
    parameter int N_CACHES   = 2
)(
    input  logic                    clk,
    input  logic                    rst,

    // ----------  Command / Address from each cache  ----------
    input  bus_request              cmd_in      [N_CACHES],
    input  logic [ADDR_WIDTH-1:0]   bus_addr    [N_CACHES],

    // ----------  Cache-to-Cache Supply (from each cache)  ----------
    input  logic [BUS_DATA_W-1:0]   supply_data  [N_CACHES],
    input  logic                    supply_valid [N_CACHES],


    input logic [BUS_DATA_W-1:0]   mem_data_in,
    input logic                    mem_data_valid,
    
    // ----------  Broadcast Bus Outputs  ----------
    output bus_request              cmd_out,
    output logic [ADDR_WIDTH-1:0]   addr_out,
    output logic [N_CACHES-1:0]     bus_owner,   // one-hot: which cache owns the bus
    output logic [N_CACHES-1:0]     exclusive,

    // ----------  Data Bus Output (combinational mux)  ----------
    output logic [BUS_DATA_W-1:0]   data_out,    // block on data bus
    output logic                    data_valid   // data_out is valid this cycle
);
    // =========================================================================
    // MEMORY MODEL NOTE:
    // mem_data_in / mem_data_valid are INPUT ports  â€” they cannot be driven
    // from inside this module.  Drive them from cache_top_v2 instead:
    //
    //   In cache_top_v2:
    //     1. Expose mem_data_in / mem_data_valid as top-level ports  OR
    //        declare internal wires and drive them from a data_memory instance.
    //     2. Instantiate:
    //          data_memory #(.ADDR_WIDTH(ADDR_WIDTH), .BUS_DATA_W(BUS_DATA_W))
    //          mem_model (
    //              .clk(clk), .rst(rst),
    //              .read(bus_cmd_out == BusRd || bus_cmd_out == BusRdX),
    //              .address(bus_addr_out),
    //              .data_out(mem_data_in),   â† wire in cache_top_v2 scope
    //              .mem_ready(mem_data_valid) â† wire in cache_top_v2 scope
    //          );
    //     3. Pass mem_data_in / mem_data_valid into shared_bus instance.
    // =========================================================================

    // =========================================================================
    // Combinational Data Mux
    //   Scan supply_valid[0..N-1] in priority order.
    //   In a correctly operating MESI system at most one cache will supply
    //   for any given bus transaction, so the priority here is a safety guard.
    // =========================================================================
    always_comb begin : comb_data_mux
        int j;
        data_out   = {BUS_DATA_W{1'b0}};
        data_valid = 1'b0;
        for (j = 0; j < N_CACHES; j++) begin
            if (supply_valid[j] && !data_valid) begin
                data_out   = supply_data[j];
                data_valid = 1'b1;
            end
        end
        // If no cache is supplying, check for memory response
        if (mem_data_valid && !data_valid) begin
                data_out   = mem_data_in;
                data_valid = 1'b1;
        end
    end

    // supply_seen removed â€” it was one cycle stale.
    // comb_exclusive now reads |supply_valid directly (safe: supply_valid is
    // derived from registered line_state, so no same-cycle combinational loop).

    always_comb begin : comb_exclusive
        int j;
        exclusive = {N_CACHES{1'b0}};
        //logic supply;
        //supply = supply_valid[0] or supply_valid[1];
        for (j = 0; j < N_CACHES; j++) begin
            // Exclusive iff: this cache owns the bus AND no peer cache is
            // supplying data THIS cycle.  |supply_valid is safe here because
            // supply_valid â† line_state (FF) â€” no combinational cycle.
            if (bus_owner[j] && !(supply_valid[0] || supply_valid[1])) begin
                exclusive[j] = 1'b1;
            end
        end
    end
    // =========================================================================
    // Sequential Arbitration & Broadcast
    //   Fixed-priority: cache 0 wins over cache 1 etc.
    //   Registered to break any combinational path from cache output -> bus
    //   output -> same cache input.
    // =========================================================================

    
    always_ff @(posedge clk or posedge rst) begin : seq_arb
        if (rst) begin
            cmd_out   <= No_OP;
            addr_out  <= {ADDR_WIDTH{1'b0}};
            bus_owner <= {N_CACHES{1'b0}};
        end else begin
            // P0-fix: HOLD the current grant while a bus transaction is in
            // progress (bus_owner != 0 AND data hasn't arrived yet).
            // Without this hold, bus_owner is cleared on cycle N+2 while
            // memory only delivers on cycle N+2, making Block [B] in
            // cache_mem_v2 (bus_owner && bus_data_valid) permanently false.
            if (|bus_owner && !data_valid) begin
                // Sustain: cmd_out, addr_out, bus_owner retain their FF values.
                // No assignment needed â€” always_ff FFs hold automatically.
            end else begin
                automatic logic granted;
                // Transaction complete (data_valid=1) or bus idle â€” clear grant
                // and re-arbitrate for the highest-priority requesting cache.
                granted = 1'b0;
                cmd_out   <= No_OP;
                addr_out  <= {ADDR_WIDTH{1'b0}};
                bus_owner <= {N_CACHES{1'b0}};
                for (int k = 0; k < N_CACHES; k++) begin
                    if (cmd_in[k] != No_OP && !granted) begin
                        cmd_out      <= cmd_in[k];
                        addr_out     <= bus_addr[k];
                        bus_owner[k] <= 1'b1;
                        granted        = 1'b1;
                    end
                end
            end
        end
    end

endmodule
