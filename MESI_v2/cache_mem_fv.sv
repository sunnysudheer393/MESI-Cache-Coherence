// =============================================================================
// cache_mem_fv.sv
//
// Formal Verification Property Module ÃƒÂ¢Ã‚Â€Ã‚Â” cache_mem_v2 (Unit Level)
//
// PHASES COVERED:
//   Phase 1 ÃƒÂ¢Ã‚Â€Ã‚Â” Address decode, hit/miss, bus command, snoop, supply, reset
//   Phase 2 ÃƒÂ¢Ã‚Â€Ã‚Â” Full MESI state transition lattice (legal + illegal arcs +
//              stability + simultaneous-event corner cases)
//
// HOW TO USE (BIND APPROACH):
//   This module is NOT instantiated manually. Instead the bind statement at
//   the bottom of this file inserts it into every cache_mem_v2 instance
//   automatically. This means:
//     - Zero RTL modification required (non-invasive)
//     - All ports labelled as 'input' here connect to the same-named
//       signals in the DUT's own scope (ports AND internal wires)
//     - The formal tool sees DUT internals like line_state, hit, etc.
//       without needing wrapper changes
//
// WHY BIND INSTEAD OF WRAPPING:
//   A wrapper would require forking the RTL. Bind lets the property module
//   "live inside" the DUT scope post-elaboration, so each cache instance
//   gets its own assertion set. Property failures point directly at the
//   offending instance with no extra indirection.
//
// KEY MESI PROPERTIES TO VERIFY:
//   1. No illegal state encoding (only I/S/E/M are valid)
//   2. Every transition must have a valid MESI trigger
//   3. Illegal state pairs (M+M, M+S, E+E) cannot coexist for same block
//   4. Miss always drives a bus command; hit in M/E drives No_OP
//   5. supply_valid ÃƒÂ¢Ã‚Â†Ã‚Â” Modified state snooping (current design restriction)
//   6. Bus commands faithfully reflect the cpu address
// =============================================================================

//`include "mesi_types.sv"
import mesi_types::*;

module cache_mem_fv #(
    parameter int ADDR_WIDTH  = 8,
    parameter int INDEX_BITS  = 2,
    parameter int OFFSET_BITS = 2,
    parameter int DATA_WIDTH  = 8,
    parameter int TAG_BITS   = ADDR_WIDTH - INDEX_BITS - OFFSET_BITS
)(
    // -------------------------------------------------------------------------
    // Mirror ALL ports of cache_mem_v2 as inputs.
    // DUT output ports become inputs here because we OBSERVE, never drive.
    // The bind (.*) auto-connects everything by name.
    // -------------------------------------------------------------------------
    input  logic                                    clk,
    input  logic                                    rst,

    // CPU Interface (DUT inputs)
    input  logic                                    cpu_read    [N_CACHES],
    input  logic                                    cpu_write   [N_CACHES],
    input  logic [ADDR_WIDTH-1:0]                   address,
    input  logic [DATA_WIDTH-1:0]                   cpu_write_data,

    // Bus Control (DUT inputs)
    input  logic                                    exclusive   [N_CACHES],
    input  bus_request                              bus_cmd_in  [N_CACHES],
    input  logic [ADDR_WIDTH-1:0]                   bus_addr_in [N_CACHES],
    input  logic                                    bus_owner   [N_CACHES],

    // Bus Data (DUT inputs)
    input  logic [DATA_WIDTH*(1<<OFFSET_BITS)-1:0]  bus_data_in,
    input  logic                                    bus_data_valid,

    // DUT Outputs (observed as inputs)
    input  logic [DATA_WIDTH-1:0]                   data_out    [N_CACHES],
    input  logic                                    cache_hit    [N_CACHES],
    input  bus_request                              bus_cmd_out,
    input  logic [ADDR_WIDTH-1:0]                   bus_addr_out,
    input  logic [DATA_WIDTH*(1<<OFFSET_BITS)-1:0]  supply_data  [N_CACHES],
    input  logic                                    supply_valid [N_CACHES],

    // -------------------------------------------------------------------------
    // DUT INTERNAL signals ÃƒÂ¢Ã‚Â€Ã‚Â” connected via bind .* from the DUT scope.
    // WHY expose internals: state transitions happen on internal registers.
    // Without these ports, properties can only observe outputs, missing bugs
    // where internal state diverges from what outputs imply.
    // -------------------------------------------------------------------------
    // Decoded address fields (combinational, same name as DUT internals)
    input  logic [ADDR_WIDTH-INDEX_BITS-OFFSET_BITS-1:0] cpu_tag,
    input  logic [INDEX_BITS-1:0]                         cpu_index,
    input  logic [OFFSET_BITS-1:0]                        cpu_offset,
    input  logic [ADDR_WIDTH-INDEX_BITS-OFFSET_BITS-1:0] snoop_tag,
    input  logic [INDEX_BITS-1:0]                         snoop_index,

    // Physical storage arrays ÃƒÂ¢Ã‚Â€Ã‚Â” the ground truth for MESI state
    input  cache_state  line_state [0:(1<<INDEX_BITS)-1],
    input  logic [ADDR_WIDTH-INDEX_BITS-OFFSET_BITS-1:0]
                        line_tag   [0:(1<<INDEX_BITS)-1],
    input  logic [DATA_WIDTH-1:0]
                        line_data  [0:(1<<INDEX_BITS)-1][0:(1<<OFFSET_BITS)-1],


    input logic dirty_eviction [N_CACHES],

    // Combinational signals reused in multiple properties
    input  logic  hit [N_CACHES],
    input  logic  snoop_line_hit [N_CACHES],
    //input  logic cpu_stall,

    //Pending Index/tag signals
//    input logic [OFFSET_BITS-1:0] pending_offset,
    input logic [TAG_BITS-1:0] pending_tag [N_CACHES],
    input logic [INDEX_BITS-1:0] pending_index [N_CACHES],// pending_evict_index,
    input logic [DATA_WIDTH-1:0] pending_write_data [N_CACHES]
);

    // =========================================================================
    // Derived locals ÃƒÂ¢Ã‚Â€Ã‚Â” same calculation as DUT
    // =========================================================================
    //localparam int TAG_BITS   = ADDR_WIDTH - INDEX_BITS - OFFSET_BITS;
    localparam int NUM_LINES  = 1 << INDEX_BITS;
    localparam int BLOCK_SIZE = 1 << OFFSET_BITS;

    logic symb0 [N_CACHES];
    logic symb1 [N_CACHES];

    //Assumption for symbolic variables to prevent combinational loops in the tool
    assume property( @(posedge clk) disable iff(rst) $stable(symb0) && $stable(symb1) && symb0 == symb1);


    // =========================================================================
    // Symbolic tracked address
    // WHY anyconst: Rather than checking one specific address, we let the tool
    // pick an arbitrary-but-fixed value. This is equivalent to universal
    // quantification over all addresses without exploding state space.
    // =========================================================================
    (* anyconst *) logic [ADDR_WIDTH-1:0] tracked_addr0, tracked_addr1;

    //Assumption to prevent combinational loops in the tool
    assume property( @(posedge clk) disable iff(rst) $stable(tracked_addr0) && $stable(tracked_addr1));

    // =========================================================================
    // Decomposed fields of the tracked address
    // WHY: This makes properties easier to write and understand (e.g. "if index matches but tag doesn't, then...") without needing to write the same
    logic [TAG_BITS-1:0]    t_tag0, t_tag1;
    logic [INDEX_BITS-1:0]  t_idx0, t_idx1;
    logic [OFFSET_BITS-1:0] t_off0, t_off1;
    logic [DATA_WIDTH-1:0] t_data0, t_data1;

    assign t_tag0 = tracked_addr0[ADDR_WIDTH-1:OFFSET_BITS+INDEX_BITS];
    assign t_tag1 = tracked_addr1[ADDR_WIDTH-1:OFFSET_BITS+INDEX_BITS];

    assign t_idx0 = tracked_addr0[OFFSET_BITS +: INDEX_BITS];
    assign t_idx1 = tracked_addr1[OFFSET_BITS +: INDEX_BITS];

    assign t_off0 = tracked_addr0[OFFSET_BITS-1:0];
    assign t_off1 = tracked_addr1[OFFSET_BITS-1:0];


    // Helper: CPU is operating on the tracked line
    wire cpu_on_tracked0 = (cpu_index == t_idx0) && (cpu_tag == t_tag0);
    wire cpu_on_tracked1 = (cpu_index == t_idx1) && (cpu_tag == t_tag1);

    // Helper: snoop targets the tracked line (same index AND same tag)
    wire snoop_on_tracked0 = (snoop_index == t_idx0) && (snoop_tag == t_tag0);
    wire snoop_on_tracked1 = (snoop_index == t_idx1) && (snoop_tag == t_tag1);

    // Helper: tracked line current state shorthand
    wire cache_state ts0 = line_state[t_idx0];
    wire cache_state ts1 = line_state[t_idx1];

    logic symb_line0 [NUM_LINES];
    logic symb_line1 [NUM_LINES];

    wire same_address = (t_tag0 == t_tag1) && (t_idx0 == t_idx1);

    assign t_data0 = line_data[t_idx0][t_off0];
    assign t_data1 = line_data[t_idx1][t_off1];

    logic [DATA_WIDTH-1:0] track_data;
    assume property( @(posedge clk) disable iff(rst) $stable(track_data) && track_data ==t_data0);

    //Assumption for symbolic variables to prevent combinational loops in the tool
    assume property( @(posedge clk) disable iff(rst) $stable(symb_line0) && $stable(symb_line1) && symb_line0 == symb_line1);


    // Helper: tracked line is valid and tagged correctly
    wire tracked_hit0  = (ts0 != Invalid) && (line_tag[t_idx0] == t_tag0);
    wire tracked_hit1  = (ts1 != Invalid) && (line_tag[t_idx1] == t_tag1);

    //Helper pending tracker
    wire pending_on_tracked0 = (pending_index == t_idx0) && (pending_tag == t_tag0);
    wire pending_on_tracked1 = (pending_index == t_idx1) && (pending_tag == t_tag1);

    //=========================================================================
    //===========================ASSUMPTIONS===================================
    //=========================================================================

    //Both write and read cannot be asserted at the same time for the same cache
    assume property( @(posedge clk) disable iff(rst) !(cpu_read[symb0] && cpu_write[symb0]));    

    // CPU must hold its request steady until it becomes bus owner (if it ever does). 
    //This is a reasonable assumption because typical CPU interfaces are blocking/stall until request is accepted, and the cache interface to the bus is combinational (no need for the CPU to change its request mid-flight).
    assume property( @(posedge clk) disable iff(rst) cpu_read[symb0] && !bus_owner[symb0] |=> cpu_read[symb0]);
    assume property( @(posedge clk) disable iff(rst) cpu_write[symb0] && !bus_owner[symb0] |=> cpu_write[symb0]);

    //Address must be stable until the transaction completes (no new transaction started). 
    //This is also reasonable because typical CPU interfaces are blocking/stall until request is accepted, and the bus interface is combinational (no need for the CPU to change its address mid-flight).
    assume property( @(posedge clk) disable iff(rst) (cpu_write[symb0] || cpu_read[symb0]) |=> $stable(address));

    //Address must be stable until state reaches the required MESI state for the transaction. 
    //This is a stronger version of the previous assumption, but still reasonable because the CPU can simply hold the request and address steady until the cache responds with a hit or the appropriate bus command, at which point the transaction is effectively complete from the CPU's perspective.
    assume property( @(posedge clk) disable iff(rst) (cpu_write[symb0]) && !bus_owner[symb0] |=> $stable(address) s_until_with(ts0 == Modified));
    assume property( @(posedge clk) disable iff(rst) (cpu_read[symb0]) && !bus_owner[symb0] |=> $stable(address) s_until_with(ts0 == Shared ||ts0 == Exclusive));

    // Bus owner must hold the bus until data is valid (if a read) or until the MESI state reflects ownership (if a write). 
    //This prevents combinational loops in the tool where the bus command and data valid signals could change mid-transaction, which would be unrealistic and could lead to false failures.
    assume property( @(posedge clk) disable iff(rst) cpu_write[symb0] && bus_owner[symb0] && ts0 != Modified |=> $stable(bus_owner));
    assume property( @(posedge clk) disable iff(rst) cpu_write[symb0] && bus_owner[symb0] && ts0 == Invalid |=> $stable(bus_owner));
    assume property( @(posedge clk) disable iff(rst) cpu_read[symb0] && bus_owner[symb0] && ts0 == Invalid |=> $stable(bus_owner));
    
    //Stable tag, index and offset
    assume property( @(posedge clk) disable iff(rst) $stable(t_tag0) && $stable(t_idx0) && $stable(t_off0));
    assume property( @(posedge clk) disable iff(rst) $stable(t_tag1) && $stable(t_idx1) && $stable(t_off1));

    //Always address is stable to avoid unnecessary random values
    assume property( @(posedge clk) disable iff(rst) $stable(address));

    // Bus commands must be one of the defined enum values (prevents X-propagation issues in the tool)
    assume property( @(posedge clk) disable iff(rst) bus_cmd_in inside {No_OP, BusRd, BusRdX, BusUpgr, BusWB});
    assume property( @(posedge clk) disable iff(rst) bus_cmd_out inside {No_OP, BusRd, BusRdX, BusUpgr, BusWB});
   


    //============================ P H A S E:  4 ==========================================
    //=====================================================================================
    //=========================== M E S I  B U S  L O G I C ===============================
    //=====================================================================================

    //Single Write Multiple Reads: Two caches cannot both have the same line in Modified state at the same time. This is a fundamental MESI invariant that must hold for coherence to be maintained. If this fails, it indicates a severe bug where two caches believe they have exclusive ownership of the same line, leading to data corruption.
    SWMR1: assert property( @(posedge clk) disable iff(rst) same_address |-> !(ts0 == Modified && ts1 == Modified));

    //When in Modifed other cannot be Shared or Exclsuive
    SWMR2: assert property( @(posedge clk) disable iff(rst) same_address |-> !(ts0 == Modified && (ts1 == Shared || ts1 == Exclusive)));

    //When in Exclsuive other cannot be Exclusive
    SWMR3: assert property( @(posedge clk) disable iff(rst) same_address |-> !(ts0 == Exclusive && ts1 == Exclusive));

    //All Shared states must have the same data (no write without bus)
    COH1: assert property( @(posedge clk) disable iff(rst) same_address && (ts0 == Shared && ts1 == Shared) |-> (t_data0 == t_data1)));

    //Write on Modified gives the same data as the line data (no silent data corruption)
    COH2: assert property( @(posedge clk) disable iff(rst) ts0 == Modified |-> pending_write_data == t_data0);
    COH3: assert property( @(posedge clk) disable iff(rst) ts1 == Modified |-> pending_write_data == t_data1);
    COH4: assert property( @(posedge clk) disable iff(rst) same_address && ts0 == Modified |-> t_data0 == pending_write_data);
    COH5: assert property( @(posedge clk) disable iff(rst) same_address && ts1 == Modified |-> t_data1 == pending_write_data);



    //============================ P H A S E:  5 ==========================================
    //=====================================================================================
    //============================ B U S  L O G I C =======================================
    //=====================================================================================

    //At most one bus owner at a time (one-hot)
    BUS1: assert property( @(posedge clk) disable iff(rst) $onehot(bus_owner));

    //Grant Implies request
    BUS2: assert property( @(posedge clk) disable iff(rst) bus_owner[symb0] |-> bus_cmd_in[symb0] != No_OP);

    //Fairness/starvation
    BUS3: assert property( @(posedge clk) disable iff(rst) (cpu_read[symb0] || cpu_write[symb0]) && !bus_owner[symb0] |-> eventually(bus_owner[symb0]));

    //Self_snoop prevention
    BUS4: assert property( @(posedge clk) disable iff(rst) bus_owner[symb0] |-> !snoop_line_hit[symb0]);



    //============================ P H A S E:  6 ==========================================
    //=====================================================================================
    //============================ E V I C T I O N ========================================
    //=====================================================================================

    //Dirty Eviction writeback must be issued when evicting a Modified line
    EVICT1: assert property( @(posedge clk) disable iff(rst) dirty_eviction[symb0] |-> ts0 == Modified && bus_cmd_out == BusWB);

    //Writeback data
    EVICT2: assert property( @(posedge clk) disable iff(rst) bus_cmd_in[symb0] == BusWB |-> supply_data[symb0] == t_data0);

    //Post-Eviction Invalidation must occur when evicting a Modified line
    EVICT3: assert property( @(posedge clk) disable iff(rst) dirty_eviction[symb0] |=> ts0 == Invalid);






    // =========================================================================
    // ==========================  PHASE 1 PROPERTIES  ========================
    // =========================================================================

    // -------------------------------------------------------------------------
    // P1.1  Address Decode Correctness
    // WHY: Any parameter mismatch in the bit-select expressions
    //      ({tag, index, offset} ÃƒÂ¢Ã‚Â‰Ã‚Â  address) would produce wrong hits.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk)
        {cpu_tag, cpu_index, cpu_offset} == address)
        else $error("P1.1: Address decode mismatch ÃƒÂ¢Ã‚Â€Ã‚Â” fields don't reconstruct address");

    assert property (@(posedge clk)
        {snoop_tag, snoop_index} == bus_addr_in[ADDR_WIDTH-1:OFFSET_BITS])
        else $error("P1.2: Snoop address decode mismatch");

    // -------------------------------------------------------------------------
    // P1.3  Hit Detection Correctness (combinational must be consistent)
    // WHY: cache_hit is used by the CPU and bus_cmd_out logic. If it doesn't
    //      match the actual storage state, every downstream decision is wrong.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk)
        cache_hit == (line_state[cpu_index] != Invalid &&
                      line_tag[cpu_index]   == cpu_tag))
        else $error("P1.3: cache_hit inconsistent with line_state/line_tag");

    // -------------------------------------------------------------------------
    // P1.4  Data Output Correctness
    // WHY: The whole point of the cache is to return the right word.
    //      Offset selection bug would return wrong bytes.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk)
        hit && cpu_read |-> data_out == line_data[cpu_index][cpu_offset])
        else $error("P1.4: data_out wrong on hit");

    assert property (@(posedge clk)
        !hit |-> data_out == {DATA_WIDTH{1'b0}})
        else $error("P1.4b: data_out should be 0 on miss");

    // -------------------------------------------------------------------------
    // P1.5  Bus Address Faithfulness
    // WHY: If bus_addr_out ÃƒÂ¢Ã‚Â‰Ã‚Â  address, the bus will snoop the wrong line in
    //      other caches ÃƒÂ¢Ã‚Â€Ã‚Â” a silent coherence violation.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk)
        bus_addr_out == address)
        else $error("P1.5: bus_addr_out must always equal cpu address");

    // -------------------------------------------------------------------------
    // P1.6  Bus Command Generation ÃƒÂ¢Ã‚Â€Ã‚Â” All 6 cases
    // WHY: Wrong bus command is the most direct path to protocol violation.
    //      Each case here corresponds exactly to one arc in the MESI FSM.
    // -------------------------------------------------------------------------

    // Read miss ÃƒÂ¢Ã‚Â†Ã‚Â’ BusRd (fetch line, potentially shared)
    assert property (@(posedge clk)
        (cpu_read && !hit && !dirty_eviction) |-> bus_cmd_out == BusRd)
        else $error("P1.6a: Read miss must issue BusRd");

    // Write miss ÃƒÂ¢Ã‚Â†Ã‚Â’ BusRdX (fetch + exclusive ownership)
    assert property (@(posedge clk)
        (cpu_write && !hit && !dirty_eviction) |-> bus_cmd_out == BusRdX)
        else $error("P1.6b: Write miss must issue BusRdX");

    // Write hit in Shared ÃƒÂ¢Ã‚Â†Ã‚Â’ BusUpgr (no data fetch, just invalidate others)
    assert property (@(posedge clk)
        (cpu_write && hit && line_state[cpu_index] == Shared) |-> bus_cmd_out == BusUpgr)
        else $error("P1.6c: Write hit on Shared must issue BusUpgr");

    // Write hit in Modified ÃƒÂ¢Ã‚Â†Ã‚Â’ No_OP (already has exclusive ownership)
    assert property (@(posedge clk)
        (cpu_write && hit && line_state[cpu_index] == Modified) && !dirty_eviction |-> bus_cmd_out == No_OP)
        else $error("P1.6d: Write hit on Modified must NOT issue bus command");

    // Write hit in Exclusive ÃƒÂ¢Ã‚Â†Ã‚Â’ No_OP (silent upgrade, no bus needed)
    // WHY: EÃƒÂ¢Ã‚Â†Ã‚Â’M is the only MESI transition that requires zero bus traffic.
    //      If BusUpgr were issued here it would unnecessarily stall the bus.
    assert property (@(posedge clk)
        (cpu_write && hit && line_state[cpu_index] == Exclusive) |-> bus_cmd_out == No_OP)
        else $error("P1.6e: Write hit on Exclusive must NOT issue bus command (silent E->M)");

    // No access ÃƒÂ¢Ã‚Â†Ã‚Â’ No_OP
    assert property (@(posedge clk)
        (!cpu_read && !cpu_write) |-> bus_cmd_out == No_OP)
        else $error("P1.6f: No CPU access must produce No_OP");

    // -------------------------------------------------------------------------
    // P1.7  Snoop Hit Detection Correctness
    // WHY: snoop_line_hit gates ALL snoop-based state transitions. If it fires
    //      when it shouldn't (false positive) or misses (false negative), the
    //      MESI state machine diverges from the protocol.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk)
        snoop_line_hit |->
            (!bus_owner && bus_cmd_in != No_OP &&
             line_state[snoop_index] != Invalid &&
             line_tag[snoop_index]   == snoop_tag))
        else $error("P1.7a: snoop_line_hit fired without valid snoop conditions");

    // Owner must never self-snoop ÃƒÂ¢Ã‚Â€Ã‚Â” the bus broadcasts back the owner's own
    // request, so bus_owner gates out the self-loop.
    // WHY: Without this guard, a cache would invalidate its own line immediately
    //      after requesting it ÃƒÂ¢Ã‚Â€Ã‚Â” an infinite miss loop.
    assert property (@(posedge clk)
        bus_owner |-> !snoop_line_hit)
        else $error("P1.7b: Bus owner must never trigger snoop_line_hit on itself");

    // Same index but different tag must NOT produce snoop_line_hit
    // WHY CORNER CASE C2: Two addresses sharing an index (conflict) must
    //      not cross-invalidate each other.
    assert property (@(posedge clk)
        (snoop_index == cpu_index && snoop_tag != line_tag[cpu_index]) |->
            !snoop_line_hit)
        else $error("P1.7c: Snoop to same index but different tag must not fire");

    // -------------------------------------------------------------------------
    // P1.8  Supply Logic
    // WHY: supply_valid tells bus_v2 to mux this cache's block onto data_out.
    //      If it asserts incorrectly, data corruption occurs; if it never
    //      asserts for a Modified line, that line can never be shared (liveness).
    // -------------------------------------------------------------------------
    assert property (@(posedge clk)
        supply_valid |-> snoop_line_hit &&
                         (bus_cmd_in == BusRd || bus_cmd_in == BusRdX) &&
                         (line_state[snoop_index] == Modified || line_state[snoop_index] == Exclusive))
        else $error("P1.8a: supply_valid asserted without correct snoop conditions");

    assert property (@(posedge clk)
        !snoop_line_hit |-> !supply_valid)
        else $error("P1.8b: supply_valid must deassert when no snoop hit");
 
    // -------------------------------------------------------------------------
    // P1.9  Reset Correctness
    // WHY: Post-reset state that is non-Invalid would cause phantom hits and
    //      false data returns without any CPU ever loading the line.
    // -------------------------------------------------------------------------
    generate
        genvar r;
        for (r = 0; r < NUM_LINES; r++) begin : gen_reset_check
            assert property (@(posedge clk)
                $fell(rst) |-> line_state[r] == Invalid)
                else $error("P1.9a: line_state[%0d] not Invalid after reset", r);

            assert property (@(posedge clk)
                $fell(rst) |-> line_tag[r] == {TAG_BITS{1'b0}})
                else $error("P1.9b: line_tag[%0d] not zero after reset", r);
        end
    endgenerate

    assert property (@(posedge clk)
        $fell(rst) |-> !cache_hit)
        else $error("P1.9c: cache_hit must be 0 on first cycle after reset");

    assert property (@(posedge clk)
        $fell(rst) |-> !supply_valid)
        else $error("P1.9d: supply_valid must be 0 on first cycle after reset");

    // =========================================================================
    // ==========================  PHASE 2 PROPERTIES  ========================
    //
    // MESI State Transition Lattice ÃƒÂ¢Ã‚Â€Ã‚Â” ALL 12 legal arcs
    //
    // WHY approach: We write forward implications (trigger |=> next_state).
    // This flushes out: (a) missing transitions, (b) wrong target state,
    // (c) transitions suppressed by else-if bugs (see Bug #4 / #5 from review).
    // The 'disable iff (rst)' clause prevents false failures during reset.
    // =========================================================================

    // -------------------------------------------------------------------------
    // Arc 1: Invalid ÃƒÂ¢Ã‚Â†Ã‚Â’ Exclusive  (CPU Read, bus fill, exclusive=1)
    // WHY this arc: When only one cache requests a line, it gets exclusive
    //               ownership. E-state allows a silent EÃƒÂ¢Ã‚Â†Ã‚Â’M write without bus.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)
        (ts == Invalid && pending_on_tracked &&
         bus_owner && bus_data_valid && exclusive &&
         bus_cmd_in == BusRd)
        |=> ts == Exclusive)
        else $error("P2.1: Arc I->E not taken on read fill with exclusive=1");

    // -------------------------------------------------------------------------
    // Arc 2: Invalid ÃƒÂ¢Ã‚Â†Ã‚Â’ Shared  (CPU Read, bus fill, exclusive=0)
    // WHY: Another cache also has/had the line ÃƒÂ¢Ã‚Â†Ã‚Â’ go Shared.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)
        (ts == Invalid && pending_on_tracked &&
         bus_owner && bus_data_valid && !exclusive &&
         bus_cmd_in == BusRd)
        |=> ts == Shared)
        else $error("P2.2: Arc I->S not taken on read fill with exclusive=0");

    // -------------------------------------------------------------------------
    // Arc 3: Invalid ÃƒÂ¢Ã‚Â†Ã‚Â’ Modified  (CPU Write, BusRdX fill)
    // WHY: Write miss fetches the line with exclusive intent; directly Modified.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)
        (ts == Invalid && pending_on_tracked &&
         bus_owner && bus_data_valid &&
         bus_cmd_in == BusRdX)
        |=> ts == Modified)
        else $error("P2.3: Arc I->M not taken on write fill");

    // -------------------------------------------------------------------------
    // Arc 4: Shared ÃƒÂ¢Ã‚Â†Ã‚Â’ Modified  (BusUpgr, bus_owner)
    // WHY BUG CATCH: This arc is suppressed by the else-if chain (Bug #4/#5)
    //      when a concurrent snoop_line_hit fires for a DIFFERENT index.
    //      The property correctly expects M next cycle whenever the upgrade
    //      condition is met ÃƒÂ¢Ã‚Â€Ã‚Â” the bug will produce a failing CEX.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)
        (ts == Shared && pending_on_tracked && line_tag[t_idx] == t_tag &&
         bus_owner && bus_cmd_in == BusUpgr &&
         !(snoop_line_hit && snoop_index == t_idx))   // no conflict on same line
        |=> ts == Modified)
        else $error("P2.4: Arc S->M (BusUpgr) not taken ÃƒÂ¢Ã‚Â€Ã‚Â” check else-if Bug #4");

    // -------------------------------------------------------------------------
    // Arc 5: Shared ÃƒÂ¢Ã‚Â†Ã‚Â’ Invalid  (Snoop BusRdX ÃƒÂ¢Ã‚Â€Ã‚Â” another cache wants exclusive)
    // WHY: A BusRdX means another CPU is writing; Shared lines must be killed.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)
        (ts == Shared && snoop_line_hit && snoop_on_tracked && bus_cmd_in == BusRdX)
        |=> ts == Invalid)
        else $error("P2.5: Arc S->I on BusRdX snoop not taken");

    // -------------------------------------------------------------------------
    // Arc 6: Shared ÃƒÂ¢Ã‚Â†Ã‚Â’ Invalid  (Snoop BusUpgr ÃƒÂ¢Ã‚Â€Ã‚Â” another cache upgrades)
    // WHY: BusUpgr is another cache going from SÃƒÂ¢Ã‚Â†Ã‚Â’M; all other S copies die.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)
        (ts == Shared && snoop_line_hit && snoop_on_tracked && bus_cmd_in == BusUpgr)
        |=> ts == Invalid)
        else $error("P2.6: Arc S->I on BusUpgr snoop not taken");

    // -------------------------------------------------------------------------
    // Arc 7: Exclusive ÃƒÂ¢Ã‚Â†Ã‚Â’ Modified  (Silent CPU Write ÃƒÂ¢Ã‚Â€Ã‚Â” no bus command)
    // WHY BUG CATCH (Bug #4 again): If a snoop_line_hit fires for a DIFFERENT
    //      line, block [A] fires and [D] (EÃƒÂ¢Ã‚Â†Ã‚Â’M write) is skipped entirely.
    //      This is the most common use case: while this CPU writes to its E line,
    //      another CPU snoops a completely unrelated address.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)//getting error now
        (ts == Exclusive && pending_on_tracked && cpu_write && hit && line_tag[t_idx] == t_tag &&
         !(snoop_line_hit && snoop_on_tracked))   // no same-line conflict
        |=> ts == Modified)
        else $error("P2.7: Arc E->M (silent write) blocked ÃƒÂ¢Ã‚Â€Ã‚Â” check else-if Bug #4");

    // Data must also be written on EÃƒÂ¢Ã‚Â†Ã‚Â’M
    // WHY BUG CATCH (Bug #5): Even if state transitions to M, if data_out
    //      is stale the write was lost. This catches the 'state M but wrong data'.
    // assert property (@(posedge clk) disable iff (rst)
    //     (ts == Exclusive && cpu_on_tracked && cpu_write && hit &&
    //      !(snoop_line_hit && snoop_index == t_idx))
    //     |=> line_data[t_idx][$past(t_off)] == $past(cpu_write_data))
    //     else $error("P2.7b: Data not written on E->M transition (Bug #5)");

    // -------------------------------------------------------------------------
    // Arc 8: Exclusive ÃƒÂ¢Ã‚Â†Ã‚Â’ Shared  (Snoop BusRd)
    // WHY: Another CPU read comes in; exclusive becomes shared, data supplied.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)
        (ts == Exclusive && snoop_line_hit && snoop_on_tracked && bus_cmd_in == BusRd)
        |=> ts == Shared)
        else $error("P2.8: Arc E->S on BusRd snoop not taken");

    // -------------------------------------------------------------------------
    // Arc 9: Exclusive ÃƒÂ¢Ã‚Â†Ã‚Â’ Invalid  (Snoop BusRdX)
    // Arc 10: Exclusive ÃƒÂ¢Ã‚Â†Ã‚Â’ Invalid  (Snoop BusUpgr)
    // WHY: Another cache wants to write ÃƒÂ¢Ã‚Â†Ã‚Â’ our E line must be killed.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)
        (ts == Exclusive && snoop_line_hit && snoop_on_tracked && bus_cmd_in == BusRdX)
        |=> ts == Invalid)
        else $error("P2.9: Arc E->I on BusRdX snoop not taken");

    assert property (@(posedge clk) disable iff (rst)
        (ts == Exclusive && snoop_line_hit && snoop_on_tracked && bus_cmd_in == BusUpgr)
        |=> ts == Invalid)
        else $error("P2.10: Arc E->I on BusUpgr snoop not taken");

    // -------------------------------------------------------------------------
    // Arc 11: Modified ÃƒÂ¢Ã‚Â†Ã‚Â’ Shared  (Snoop BusRd ÃƒÂ¢Ã‚Â€Ã‚Â” writeback + share)
    // WHY: Another cache reads a line we own dirty. We supply, then share.
    //      supply_valid should also be high this cycle.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)
        (ts == Modified && snoop_line_hit && snoop_on_tracked && bus_cmd_in == BusRd)
        |=> ts == Shared)
        else $error("P2.11: Arc M->S on BusRd snoop not taken");

    // supply_valid must be high when Modified snoops BusRd
    assert property (@(posedge clk) disable iff (rst)
        (ts == Modified && snoop_line_hit && snoop_on_tracked && bus_cmd_in == BusRd)
        |-> supply_valid)
        else $error("P2.11b: supply_valid must be high when M line is snooped on BusRd");

    // assert property (@(posedge clk) disable iff (rst)
    //     (ts == Modified && cpu_write && hit && cpu_on_tracked)
    //     |=> line_data[cpu_index][cpu_offset] == $past(cpu_write_data))
    //     else $error("P2.11c: line_data must be updated when M line is written");

    assert property (@(posedge clk) disable iff (rst)
        (ts == Modified && cpu_write && cpu_on_tracked) 
        |-> ts == Modified)
        else $error("P2.11d: ts must remain Modified when M line is written");

    // -------------------------------------------------------------------------
    // Arc 12: Modified ÃƒÂ¢Ã‚Â†Ã‚Â’ Invalid  (Snoop BusRdX ÃƒÂ¢Ã‚Â€Ã‚Â” writeback + evict)
    // WHY: Another cache writes; our dirty copy becomes stale, must evict.
    // -------------------------------------------------------------------------
    assert property (@(posedge clk) disable iff (rst)
        (ts == Modified && snoop_line_hit && snoop_on_tracked && bus_cmd_in == BusRdX)
        |=> ts == Invalid)
        else $error("P2.12: Arc M->I on BusRdX snoop not taken");

        

    // =========================================================================
    // Illegal Transition Properties (MUST NEVER HAPPEN)
    // WHY: These are the non-edges in the MESI transition graph. If any fires,
    //      the protocol has been violated without a valid trigger.
    // =========================================================================

    // No legal path reaches E from S (S can only go to M or I)
    assert property (@(posedge clk) disable iff (rst)
        $past(ts == Shared) |-> ts != Exclusive)
        else $error("P2.13: Illegal transition S->E ÃƒÂ¢Ã‚Â€Ã‚Â” no such arc in MESI");

    // No legal path reaches E from M
    assert property (@(posedge clk) disable iff (rst)
        $past(ts == Modified) |-> ts != Exclusive)
        else $error("P2.14: Illegal transition M->E ÃƒÂ¢Ã‚Â€Ã‚Â” no such arc in MESI");

    // E must always leave E on a snoop (never stay E after seeing another request)
    assert property (@(posedge clk) disable iff (rst) //getting error now
        ($past(ts == Exclusive) && $past(snoop_on_tracked) && $past(snoop_line_hit)) |-> ts != Exclusive)
        else $error("P2.15: State stayed E after snoop ÃƒÂ¢Ã‚Â€Ã‚Â” must transition E->S or E->I");

    // S must leave S on BusRdX/BusUpgr snoop (never stay S)
    assert property (@(posedge clk) disable iff (rst)
        ($past(ts == Shared) && $past(snoop_on_tracked) && $past(snoop_line_hit) &&
         ($past(bus_cmd_in == BusRdX) || $past(bus_cmd_in == BusUpgr)))
        |-> ts != Shared)
        else $error("P2.16: Shared stayed Shared after BusRdX/BusUpgr snoop");

    // =========================================================================
    // Stability Properties
    // WHY: If no relevant event touches a line, its state must be stable.
    //      This catches spurious state changes from unrelated bus traffic.
    // =========================================================================
    assert property (@(posedge clk) disable iff (rst)
        (cpu_on_tracked && !snoop_on_tracked && !cpu_write && !cpu_read && 
         !bus_owner && !bus_data_valid && !snoop_line_hit)
        |=> $stable(ts))
        else $error("P2.17: Tracked line state changed with no valid trigger");







    //ASSUMPTIONS FOR DATA CORRECTNESS PROPERTIES
    assume property( @(posedge clk) disable iff(rst) bus_owner && bus_data_valid |-> !hit);

    assume property( @(posedge clk) disable iff(rst) (cpu_index == t_idx) |-> (cpu_tag == t_tag));


    assert property (@(posedge clk) disable iff(rst) //getting error now
                (cpu_write && hit && (address == tracked_addr) && (cpu_write_data == track_data) && 
                (ts == Modified || ts == Exclusive) &&!snoop_line_hit ) |=> 
                (line_data[t_idx][t_off] == track_data))
                else $error("Data correctness failed: CPU write did not update line_data correctly");

    // =========================================================================
    // Corner Case: Dirty Eviction Detection
    // WHY (C1): Conflict miss on a Modified line is the most dangerous bug.
    //           Current design has NO writeback logic ÃƒÂ¢Ã‚Â€Ã‚Â” it silently overwrites
    //           the dirty line. This assertion will FAIL, flagging the gap.
    //           The failure is INTENTIONAL to document the missing writeback.
    // =========================================================================
    assert property (@(posedge clk) disable iff (rst)
        ((cpu_read || cpu_write) && bus_owner && bus_data_valid &&
         line_state[cpu_index] == Modified &&
         line_tag[cpu_index]   != cpu_tag)   // conflict miss on dirty line
        |-> dirty_eviction)
        else $error("C1: DIRTY EVICTION ÃƒÂ¢Ã‚Â€Ã‚Â” Modified line overwritten without writeback! RTL gap.");

    // // =========================================================================
    // // ===================Data Correctness======================================
    // // =========================================================================

    
    // DC2: Bus Fill Data Capture
    // Proves that when the bus fills a line, the correct word from the wide bus_data_in is extracted.
    assert property (@(posedge clk) disable iff (rst) //getting error now
        (bus_owner && bus_data_valid && (address == tracked_addr) &&
         (bus_cmd_in == BusRd || bus_cmd_in == BusRdX)) |=> 
        (line_data[t_idx][t_off] == $past(bus_data_in[DATA_WIDTH*(t_off+1)-1 -: DATA_WIDTH])))
        else $error("DC2: Bus fill failed to extract the correct word offset into line_data.");

    //DS1: Strict Data Stability
    assert property (@(posedge clk) disable iff(rst)
        (!cpu_write &&!bus_data_valid && !bus_owner &&!(address == tracked_addr)) |=> 
        $stable(line_data[t_idx][t_off]))
        else $error("Data stability failed: line_data changed without a valid write or bus fill");

    //DU1: Ugrade Data Correctness(S->M) 
    assert property (@(posedge clk) disable iff(rst) //getting error now
        (cpu_write && hit &&(line_state[cpu_index] == Shared) && 
        (address == tracked_addr) && (cpu_write_data == track_data)) |->
        s_eventually (bus_owner && bus_cmd_in ==BusUpgr && line_data[t_idx][t_off] == track_data) )
        else $error("Upgrade data correctness failed: S->M write did not update line_data correctly");



    // DC3: Supply Data Correctness
    assert property (@(posedge clk) disable iff (rst)
        (snoop_line_hit && snoop_on_tracked && bus_cmd_in == BusRd && ts == Modified)
        |-> (line_data[t_idx][t_off] == supply_data[DATA_WIDTH*(t_off+1)-1 -: DATA_WIDTH]))
        else $error("DC3: Supply data did not match line_data on M->S snoop");

    //DC4: CPU read returns previously written data (after any necessary bus transactions)
    property cpu_write_then_read;
         @(posedge clk) disable iff(rst)
        cpu_write && hit && (address == tracked_addr) && (cpu_write_data == track_data) ##1
        (!cpu_write &&!bus_data_valid && !bus_owner) [*0:$] &&
        (cpu_read && hit && (address == tracked_addr)) |-> (data_out == track_data);
    endproperty

    assert property (@(posedge clk) disable iff(rst) cpu_write_then_read)
        else $error("DC4: CPU read did not return correct data from line_data");

    
    //DC5 BusRdX fill write pending write_data to correct offset in line_data
    assert property (@(posedge clk) disable iff(rst) //getting error now
        (bus_owner && bus_data_valid && (address == tracked_addr) &&
         bus_cmd_in == BusRdX && pending_on_tracked) |=>
        (line_data[t_idx][t_off] == pending_write_data))
        else $error("DC5: BusRdX fill did not write pending_write_data to correct offset in line_data.");

    

    //========================================================================================
    //================== S W M R & C O H E R E N C E    I N V A R I A N T S ==================
    //========================================================================================





endmodule

// =============================================================================
// BIND STATEMENT
// WHY here (not in top-level): Placing the bind in the same file as the
// property module keeps them co-located. Any tool that compiles this file
// gets both the property module and the binding atomically.
// The parameterization uses the DUT's own parameter values, so any instance
// (8-bit, 32-bit, etc.) automatically gets the right-sized assertions.
// =============================================================================
bind cache_mem_v2 cache_mem_fv #(
    .ADDR_WIDTH  (ADDR_WIDTH),
    .INDEX_BITS  (INDEX_BITS),
    .OFFSET_BITS (OFFSET_BITS),
    .DATA_WIDTH  (DATA_WIDTH)
) fv_unit_inst (.*);
