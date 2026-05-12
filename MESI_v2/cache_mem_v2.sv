// =============================================================================
// cache_mem_v2.sv  (parameterized)
//
// Parameterized Direct-Mapped Cache with Physical Storage
//
// Parameters
//   ADDR_WIDTH   ÃƒÂ¢Ã‚Â€Ã‚Â“ full CPU address width (default 8)
//   INDEX_BITS   ÃƒÂ¢Ã‚Â€Ã‚Â“ bits used for set/line index  (default 2  ÃƒÂ¢Ã‚Â†Ã‚Â’ 4 lines)
//   OFFSET_BITS  ÃƒÂ¢Ã‚Â€Ã‚Â“ bits used for block offset    (default 2  ÃƒÂ¢Ã‚Â†Ã‚Â’ 4 words)
//   DATA_WIDTH   ÃƒÂ¢Ã‚Â€Ã‚Â“ width of one data word        (default 8  ÃƒÂ¢Ã‚Â†Ã‚Â’ 1 byte)
//
// Derived (localparams)
//   TAG_BITS      = ADDR_WIDTH - INDEX_BITS - OFFSET_BITS
//   NUM_LINES     = 2 ** INDEX_BITS
//   BLOCK_SIZE    = 2 ** OFFSET_BITS   (words per cache line)
//   BUS_DATA_W    = DATA_WIDTH * BLOCK_SIZE   (full block on data bus)
//
// Address layout (MSB ÃƒÂ¢Ã‚Â†Ã‚Â’ LSB):
//   [ TAG_BITS | INDEX_BITS | OFFSET_BITS ]
//
// Key features:
//   - Tag/index/offset decode driven entirely by parameters
//   - Per-line MESI state, tag, and data arrays sized by localparams
//   - CPU read  ÃƒÂ¢Ã‚Â†Ã‚Â’ data_out = line_data[cpu_index][cpu_offset]   (on hit)
//   - CPU write ÃƒÂ¢Ã‚Â†Ã‚Â’ line_data[cpu_index][cpu_offset] = cpu_write_data (on hit)
//   - Bus fill  ÃƒÂ¢Ã‚Â†Ã‚Â’ loads complete block from bus_data_in (on bus_data_valid)
//   - supply_data / supply_valid ÃƒÂ¢Ã‚Â†Ã‚Â’ cache-to-cache block transfer
// =============================================================================

//`include "mesi_types.sv"
import mesi_types::*;

module cache_mem_v2 #(
    parameter int ADDR_WIDTH  = 8,
    parameter int INDEX_BITS  = 2,
    parameter int OFFSET_BITS = 2,
    parameter int DATA_WIDTH  = 8
)(
    input  logic                            clk,
    input  logic                            rst,

    // ----------  CPU Interface  ----------
    input  logic                            cpu_read,
    input  logic                            cpu_write,
    input  logic [ADDR_WIDTH-1:0]           address,         // full CPU address
    input  logic [DATA_WIDTH-1:0]           cpu_write_data,  // word to write

    // ----------  Bus Control Interface  ----------
    input  logic                            exclusive,       // only requester on bus
    input  bus_request                      bus_cmd_in,      // snooped bus command
    input  logic [ADDR_WIDTH-1:0]           bus_addr_in,     // snooped bus address
    input  logic                            bus_owner,       // this cache owns bus txn

    // ----------  Bus Data Interface  ----------
    // Full block width = DATA_WIDTH * 2^OFFSET_BITS
    input  logic [DATA_WIDTH*(1<<OFFSET_BITS)-1:0]  bus_data_in,    // block from bus
    input  logic                                    bus_data_valid,  // bus_data_in valid

    // ----------  CPU Output  ----------
    output logic [DATA_WIDTH-1:0]           data_out,        // word to CPU
    output logic                            cache_hit,       // hit indicator

    // ----------  Bus Command Outputs  ----------
    output bus_request                      bus_cmd_out,     // command to bus
    output logic [ADDR_WIDTH-1:0]           bus_addr_out,    // address to bus
    // NOTE: bus_data_out / bus_data_valid_out are REMOVED.
    // The correct full-block supply mechanism is supply_data / supply_valid below.
    // supply_data is BUS_DATA_W wide (all BLOCK_SIZE words packed), routed through
    // bus_v2's combinational data mux, and broadcast back as bus_data_in to the
    // requesting cache.  A single-word bus_data_out would be too narrow and is
    // not wired into the bus topology at all.

    output logic dirty_eviction,

    // ----------  Cache-to-Cache Supply  ----------
    output logic [DATA_WIDTH*(1<<OFFSET_BITS)-1:0]  supply_data,   // full line to give
    output logic                                    supply_valid,  // we are supplying
    output logic                                    cpu_stall        // new output: stall CPU when we have a snoop hit that conflicts with the CPU's current access
);

    // =========================================================================
    // Derived Constants
    // =========================================================================
    localparam int TAG_BITS   = ADDR_WIDTH - INDEX_BITS - OFFSET_BITS;
    localparam int NUM_LINES  = 1 << INDEX_BITS;   // 2^INDEX_BITS cache lines
    localparam int BLOCK_SIZE = 1 << OFFSET_BITS;  // 2^OFFSET_BITS words per line


    // =========================================================================
    // Address Decode ÃƒÂ¢Ã‚Â€Ã‚Â“ CPU
    // =========================================================================
    logic [TAG_BITS-1:0]    cpu_tag;
    logic [INDEX_BITS-1:0]  cpu_index;
    logic [OFFSET_BITS-1:0] cpu_offset;

    assign cpu_offset = address[OFFSET_BITS-1:0];
    assign cpu_index  = address[OFFSET_BITS +: INDEX_BITS];
    assign cpu_tag    = address[ADDR_WIDTH-1:OFFSET_BITS+INDEX_BITS];

    // =========================================================================
    // Address Decode ÃƒÂ¢Ã‚Â€Ã‚Â“ Snoop (bus_addr_in)
    // =========================================================================
    logic [TAG_BITS-1:0]    snoop_tag;
    logic [INDEX_BITS-1:0]  snoop_index;
    logic [OFFSET_BITS-1:0] snoop_offset;

    assign snoop_index = bus_addr_in[OFFSET_BITS +: INDEX_BITS];
    assign snoop_tag   = bus_addr_in[ADDR_WIDTH-1:OFFSET_BITS+INDEX_BITS];
    assign snoop_offset = bus_addr_in[OFFSET_BITS-1:0];

    // =========================================================================
    // Cache Storage Arrays
    //   line_state [NUM_LINES]               ÃƒÂ¢Ã‚Â€Ã‚Â“ MESI state per line
    //   line_tag   [NUM_LINES][TAG_BITS]      ÃƒÂ¢Ã‚Â€Ã‚Â“ stored tag per line
    //   line_data  [NUM_LINES][BLOCK_SIZE]    ÃƒÂ¢Ã‚Â€Ã‚Â“ [line][word_offset]
    // =========================================================================
    cache_state                line_state [NUM_LINES];
    logic [TAG_BITS-1:0]       line_tag   [NUM_LINES];
    logic [DATA_WIDTH-1:0]     line_data  [NUM_LINES][BLOCK_SIZE];

    // =========================================================================
    // Hit Detection (CPU)
    // =========================================================================
    logic hit;
    assign hit       = (line_state[cpu_index] != Invalid) &&
                       (line_tag[cpu_index]   == cpu_tag);
    assign cache_hit = hit;

    // =========================================================================
    // CPU Read Data Output ÃƒÂ¢Ã‚Â€Ã‚Â“ select word with offset
    // =========================================================================
    assign data_out = (hit && cpu_read) ? line_data[cpu_index][cpu_offset]
                          : {DATA_WIDTH{1'b0}};

    // =========================================================================
    // Snoop Hit Detection
    //   Another cache is initiating a bus transaction that targets a line
    //   we currently hold.
    // =========================================================================
    logic snoop_line_hit;
    assign snoop_line_hit = (!bus_owner)                          &&  // we are not the initiator
                            (bus_cmd_in != No_OP)                 &&  // real bus request
                            (line_state[snoop_index] != Invalid)  &&  // we hold the line
                            (line_tag[snoop_index]   == snoop_tag);   // tags match

    // =========================================================================
    // Cache-to-Cache Supply
    //   Drive supply_data as a concatenation of all words in the targeted line.
    //   supply_valid only on BusRd (not BusRdX ÃƒÂ¢Ã‚Â€Ã‚Â“ that invalidates, so we still
    //   supply the data but will move to Invalid in the sequential block).
    // =========================================================================
    // Build supply_data by packing words [BLOCK_SIZE-1:0] MSB-first
    genvar w;
    generate
        for (w = 0; w < BLOCK_SIZE; w++) begin : gen_supply
            assign supply_data[DATA_WIDTH*(w+1)-1 -: DATA_WIDTH] =
                       line_data[snoop_index][w];
        end
    endgenerate

    // supply_valid pulses for exactly one cycle on BusRdX ÃƒÂ¢Ã‚Â€Ã‚Â” bus must latch supply_data
    // on the same cycle supply_valid is asserted
    // assign supply_valid = snoop_line_hit &&
    //                       (bus_cmd_in == BusRd || bus_cmd_in == BusRdX) &&
    //                       (line_state[snoop_index] == Modified || line_state[snoop_index] == Exclusive);


    // supply_valid: only assert when we are actually allowed to drive the bus
    assign supply_valid = snoop_line_hit &&
                      ((bus_cmd_in == BusRd  &&
                        (line_state[snoop_index] == Modified ||
                         line_state[snoop_index] == Exclusive)) ||
                       (bus_cmd_in == BusRdX &&
                        (line_state[snoop_index] == Modified ||
                         line_state[snoop_index] == Exclusive))) ; // ||
                        //  (bus_owner && (bus_cmd_in == BusWB || bus_cmd_out == BusWB)); // also assert supply_valid when we are writing back a dirty line to memory

    logic snoop_conflicts_cpu;
    assign snoop_conflicts_cpu = snoop_line_hit && (snoop_index == cpu_index);

    // New signal: stall the CPU if we have a snoop hit that conflicts with the CPU's current access
    assign cpu_stall = ((cpu_read || cpu_write ) && !hit) ||
                         (cpu_write && hit && line_state[cpu_index] == Shared) ||
                         (snoop_conflicts_cpu);

    // =========================================================================
    // Bus Command Generation (miss / upgrade only)
    // =========================================================================
    always_comb begin
        if(dirty_eviction)
            bus_cmd_out = BusWB;
        else if (cpu_read  && !hit)
            bus_cmd_out = BusRd;
        else if (cpu_write && !hit)
            bus_cmd_out = BusRdX;
        else if (cpu_write && hit && (line_state[cpu_index] == Shared))
            bus_cmd_out = BusUpgr;
        else
            bus_cmd_out = No_OP; //for exclusive state we don't need to do anything
    end

    assign bus_addr_out = address;
    // assign bus_addr_out = dirty_eviction? {line_tag[cpu_index],cpu_index, {OFFSET_BITS{1'b0}}} : address;
    // Data supply is handled entirely by supply_data / supply_valid above.
    // supply_data packs all BLOCK_SIZE words into one BUS_DATA_W vector.
    // bus_v2 muxes supply_data onto its data_out line when supply_valid is
    // asserted, delivering the complete block to the requesting cache.

    // =========================================================================
    // BusUpgr Pending Context
    //   When a CPU write to a Shared line issues BusUpgr on cycle N, the bus
    //   only broadcasts BusUpgr back on cycle N+1 (registered arbitration).
    //   By then, cpu_offset and cpu_write_data reflect the CPU's cycle-N+1
    //   request, NOT the original write.  Latch the context at issue time.
    // =========================================================================
    
    logic req_in_flight; // Optional: track whether we have an outstanding BusUpgr request
    logic [OFFSET_BITS-1:0]  pending_offset;
    logic [TAG_BITS-1:0]    pending_tag;
    logic [DATA_WIDTH-1:0]   pending_write_data;
    logic [INDEX_BITS-1:0]  pending_index, pending_evict_index; // Optional: if you want to verify the upgrade is still targeting the same line at commit time

    always_ff @(posedge clk or posedge rst) begin : latch_pending
        if (rst) begin
            pending_offset     <= {OFFSET_BITS{1'b0}};
            pending_write_data <= {DATA_WIDTH{1'b0}};
            pending_index      <= {INDEX_BITS{1'b0}};
            pending_tag        <= {TAG_BITS{1'b0}};
            req_in_flight      <= 1'b0;
            pending_evict_index <= {INDEX_BITS{1'b0}};
        end else if (!req_in_flight && (!bus_owner || (bus_cmd_out != bus_cmd_in)) && (bus_cmd_out != No_OP)) begin
            // LATCH: capture at the exact cycle BusUpgr is issued (combinational)
           // else if( !bus_owner && (bus_cmd_out == BusRdX || bus_cmd_out == BusUpgr)) begin
            req_in_flight <= 1'b1; // Track if we have an outstanding BusUpgr request
            pending_offset     <= cpu_offset;
            pending_write_data <= cpu_write_data;
            pending_index      <= cpu_index;
            pending_tag        <= cpu_tag;
            if(!hit && line_state[cpu_index] == Modified)
                pending_evict_index <= cpu_index;
        end else if (bus_owner) begin
            if(((bus_cmd_in == BusRd || bus_cmd_in == BusRdX) && bus_data_valid)|| //) begin//|| 
                (bus_cmd_in == BusUpgr || bus_cmd_in == BusWB)) begin
                // Clear pending context on bus fill completion, since the upgrade is effectively committed at that point. The bus fill will update our cache line with the new data and state (E or S), so we won't need the pending context anymore to complete the upgrade.
                req_in_flight <= 1'b0; // Clear outstanding request flag
                pending_offset     <= {OFFSET_BITS{1'b0}};
                pending_write_data <= {DATA_WIDTH{1'b0}};
                pending_index      <= {INDEX_BITS{1'b0}};
                pending_tag        <= {TAG_BITS{1'b0}};
                pending_evict_index <= {INDEX_BITS{1'b0}};
            end
            // // CLEAR: fires on the same posedge as Block [C] in seq_updates.
            // // Both blocks see the PRE-EDGE pending values (NBA semantics), so
            // // Block [C] commits correctly before this clear takes effect.
            // // Do NOT use a blanket else-clear ÃƒÂ¢Ã‚Â€Ã‚Â” that would erase pending_index
            // // on cycle N+1 (one cycle before Block [C] consumes it on N+2).
            // pending_offset     <= {OFFSET_BITS{1'b0}};
            // pending_write_data <= {DATA_WIDTH{1'b0}};
            // pending_index      <= {INDEX_BITS{1'b0}};
            // pending_tag        <= {TAG_BITS{1'b0}};
        end
        // No else: HOLD pending values while waiting for BusUpgr to be broadcast
    end

    

    //logic dirty_eviction;
    assign dirty_eviction = !hit && (cpu_read || cpu_write) && (line_state[cpu_index] == Modified);


    // =========================================================================
    // Sequential: State & Data Updates
    // =========================================================================
    always_ff @(posedge clk or posedge rst) begin : seq_updates
        if (rst) begin
            for (int i = 0; i < NUM_LINES; i++) begin
                line_state[i] <= Invalid;
                line_tag[i]   <= {TAG_BITS{1'b0}};
                for (int j = 0; j < BLOCK_SIZE; j++)
                    line_data[i][j] <= {DATA_WIDTH{1'b0}};
            end
        end else begin
            // -----------------------------------------------------------------
            // [A] Snoop ÃƒÂ¢Ã‚Â€Ã‚Â“ MESI state transitions for the snooped line
            // -----------------------------------------------------------------
            if (snoop_line_hit) begin
                case (line_state[snoop_index])
                    Shared: begin
                        if (bus_cmd_in == BusRdX || bus_cmd_in == BusUpgr) begin
                            line_state[snoop_index] <= Invalid;
                            line_tag[snoop_index]   <= {TAG_BITS{1'b0}};
                        end
                    end
                    Exclusive: begin
                        if      (bus_cmd_in == BusRdX || bus_cmd_in == BusUpgr) begin
                            line_state[snoop_index] <= Invalid;
                            line_tag[snoop_index]   <= {TAG_BITS{1'b0}};
                        end
                        else if (bus_cmd_in == BusRd)  line_state[snoop_index] <= Shared;
                    end
                    Modified: begin
                        // Supply data, then transition
                        if      (bus_cmd_in == BusRd)  begin
                            line_state[snoop_index] <= Shared;
                            //line_data[snoop_index][snoop_offset] <= cpu_write_data;
                        end else if (bus_cmd_in == BusRdX || bus_cmd_in == BusUpgr) begin
                            line_state[snoop_index] <= Invalid;
                            line_tag[snoop_index]   <= {TAG_BITS{1'b0}};
                            //line_data[snoop_index][snoop_offset] <= cpu_write_data;
                        end
                    end
                endcase
            end

            //If the urrent line has Exclusive acces it can go to Modified if cpu_write occured
            else if(bus_owner && (line_state[pending_index] == Exclusive) && cpu_write && !snoop_line_hit) begin
                   line_state[pending_index] <= Modified; // Handle the case where we have an exclusive line and a CPU write comes in on the same cycle as the bus fill. We can silently upgrade to Modified here since we know we are the only owner of the line and the CPU is writing to it.
            end 

            // -----------------------------------------------------------------
            // [B] Bus Fill ÃƒÂ¢Ã‚Â€Ã‚Â“ this cache is the bus owner; data arrived
            //     Unpack bus_data_in into individual words
            // -----------------------------------------------------------------
            //if (bus_owner && bus_data_valid) begin
            else if (bus_owner && bus_data_valid && (bus_cmd_in == BusRd || bus_cmd_in == BusRdX)) begin
                line_tag[pending_index] <= pending_tag;
                for (int k = 0; k < BLOCK_SIZE; k++) begin
                    line_data[pending_index][k] <=
                        bus_data_in[DATA_WIDTH*(k+1)-1 -: DATA_WIDTH];
                end
                if      (bus_cmd_in == BusRd  &&  exclusive) line_state[pending_index] <= Exclusive;
                else if (bus_cmd_in == BusRd  && !exclusive) line_state[pending_index] <= Shared;
                else if (bus_cmd_in == BusRdX) begin
                    line_state[pending_index] <= Modified;
                    // If this is a write miss (BusRdX), we can optimistically update the targeted word with the CPU's write data, since the bus transaction will grant us ownership and the opportunity to modify the line on the same cycle. This also allows us to avoid a separate write after the fill completes.
                    line_data[pending_index][pending_offset] <= pending_write_data; // P1-fix: use latched values from pending context, not cpu_offset/cpu_write_data which may have
                end 
                
                           
            end

            // -----------------------------------------------------------------
            // [C] BusUpgr ÃƒÂ¢Ã‚Â€Ã‚Â“ own the upgrade: Shared ÃƒÂ¢Ã‚Â†Ã‚Â’ Modified (no data fill)
            //     Use REGISTERED pending_offset / pending_write_data because
            //     Block [C] fires 1 cycle after the original write request.
            //     If we used cpu_offset/cpu_write_data here, we would write the
            //     CPU's cycle-N+1 inputs, not the intended cycle-N write.
            // -----------------------------------------------------------------
            else if (bus_owner && (bus_cmd_in == BusUpgr) && line_tag[pending_index] == pending_tag && line_state[pending_index] == Shared) begin
                line_state[pending_index]                  <= Modified;
                line_data[pending_index][pending_offset]   <= pending_write_data; // P1-fix: use latched values
            end

            // if (bus_owner && (bus_cmd_in == BusUpgr) && line_state[cpu_index] != Invalid) begin
            //     line_state[cpu_index]                  <= Modified;
            //     line_data[cpu_index][cpu_offset]   <= cpu_write_data; // P1-fix: use latched values
            // end

            // -----------------------------------------------------------------
            // [D] CPU Write Hit ÃƒÂ¢Ã‚Â€Ã‚Â“ update the targeted word; silent EÃƒÂ¢Ã‚Â†Ã‚Â’M upgrade
            // -----------------------------------------------------------------
            else if (cpu_write && hit && !snoop_conflicts_cpu) begin
                if(line_state[cpu_index] == Modified) begin
                    line_data[cpu_index][cpu_offset] <= cpu_write_data;
                end else if (line_state[cpu_index] == Exclusive ) begin // removed this condition because we can silently upgrade E to M on a write hit without issuing BusUpgr&& !snoop_line_hit
                    line_state[cpu_index] <= Modified;
                    line_data[cpu_index][cpu_offset] <= cpu_write_data;
                end
                else if (line_state[cpu_index] == Shared) begin
                    // Issue BusUpgr in combinational logic, but also update state/data here on the same cycle.
                    // The bus will broadcast BusUpgr back on the next cycle, but we can already commit the upgrade locally.
                    //line_state[cpu_index] <= Modified;
                    //line_data[cpu_index][cpu_offset] <= cpu_write_data;
                end
            end    

            // -----------------------------------------------------------------
            // [E] CPU Read Miss or Write Miss ÃƒÂ¢Ã‚Â€Ã‚Â“ handled by
            //     bus command generation and bus fill in Blocks [A] and [B]
            //     No state update here ÃƒÂ¢Ã‚Â€Ã‚Â“ wait for bus fill to update
            // -----------------------------------------------------------------
            else if(bus_owner && (bus_cmd_in == BusWB)) begin
                // On a dirty eviction, we need to invalidate the line after writing it back to memory. The bus transaction is already committed at this point, so we just need to update our state and tag arrays.
                line_state[pending_evict_index] <= Invalid;
                line_tag[pending_evict_index]   <= {TAG_BITS{1'b0}};
            end
   
        end
    end

endmodule
