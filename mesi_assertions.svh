`include "mesi_types.sv"
import mesi_types::*;


module mesi_fv_tb(
    input logic clk, rst,
    input cache_state state_0, state_1,
    input logic [7:0] addr_0, addr_1,
    input logic cpu_write[2],
	input logic cpu_read[2],
	input logic exclusive_0, exclusive_1,
	// input logic [7:0] cpu_addr[2],
	input logic [1:0] bus_owner,
    input bus_request bus_cmd
);


// Constraint: A CPU cannot perform a Read and a Write in the same cycle
assume property (@(posedge clk) disable iff(rst) !(cpu_read[0] && cpu_write[0]));
assume property (@(posedge clk) disable iff(rst) !(cpu_read[1] && cpu_write[1]));

//when in Modified, other bus owner shouldn't be granted
assume property (@(posedge clk) disable iff(rst) (state_0 == Modified && addr_0 == addr_1) |-> !bus_owner[1]);
assume property (@(posedge clk) disable iff(rst) (state_1 == Modified && addr_0 == addr_1) |-> !bus_owner[0]);

//atmost only one bus owner active at a time
assume property (@(posedge clk) disable iff(rst) $onehot0(bus_owner));

// Constraint: Address must remain stable while a request is pending
// This ensures the CPU doesn't change the address before the bus can respond
assume property (@(posedge clk) disable iff(rst) 
    (cpu_read[0] || cpu_write[0]) && !bus_owner[0] |=> $stable(addr_0));

assume property (@(posedge clk) disable iff(rst) 
    (cpu_read[1] || cpu_write[1]) && !bus_owner[1] |=> $stable(addr_1));

//address stable for Invalid
// Constraint: Address must remain stable while a request is pending
// or until the cache has reached a stable state (Shared, Exclusive, or Modified)
assume property (@(posedge clk) disable iff(rst) 
    (cpu_read[0] || cpu_write[0]) && (state_0 == Invalid) |=> $stable(addr_0));

assume property (@(posedge clk) disable iff(rst) 
    (cpu_read[1] || cpu_write[1]) && (state_1 == Invalid) |=> $stable(addr_1));

//if addr matches only one exclusive
assume property (@(posedge clk) disable iff(rst)  (addr_0 == addr_1) |=> !(exclusive_0 && exclusive_1));

//exclusive only if other invalid
assume property (@(posedge clk) disable iff(rst) (exclusive_0 == 1'b1) |-> (state_1 == Invalid));
assume property (@(posedge clk) disable iff(rst) (exclusive_1 == 1'b1) |-> (state_0 == Invalid));

//valid bus owner
assume property (@(posedge clk) disable iff(rst) bus_owner == 2'b00 || bus_owner == 2'b10 || bus_owner == 2'b01);

//Bus tied to requester
assume property (@(posedge clk) disable iff(rst) (bus_cmd == BusRdX) |-> bus_owner);

//valid transition on bus ownership only\
assume property (@(posedge clk) disable iff(rst) (state_0 == Invalid && !bus_owner[0])|=> state_0 == Invalid);
assume property (@(posedge clk) disable iff(rst) (state_1 == Invalid && !bus_owner[1])|=> state_1 == Invalid);

// assume property (@(posedge clk) disable iff(rst) addr_0 == addr_1 && cpu_write[0] |=> ##[1:5] state_1 == Invalid);
// assume property (@(posedge clk) disable iff(rst) addr_0 == addr_1 && cpu_write[1] |=> ##[1:5] state_0 == Invalid);

assume property (@(posedge clk) disable iff(rst) (state_0 == Invalid && state_1 == Invalid) && cpu_read[0] && bus_owner[0] |=> exclusive_0 == 1'b1);
assume property (@(posedge clk) disable iff(rst) (state_0 == Invalid && state_1 == Invalid) && cpu_read[1] && bus_owner[1] |=> exclusive_1 == 1'b1);
// Constraint: exclusive_0 should only be high if cache_1 does NOT have the data
// This models the 'C' (Copy) bit in many bus protocols

// assume property (@(posedge clk) disable iff(rst) (exclusive_0) |-> (state_1 == Invalid));
// assume property (@(posedge clk) disable iff(rst) (exclusive_1) |-> (state_0 == Invalid));
assume property (@(posedge clk) !(bus_owner[0] && bus_owner[1]));
assume property (@(posedge clk) bus_cmd == BusRdX |-> $onehot(bus_owner));
// Exclusive means the other cache must be Invalid for same address
assume property (@(posedge clk) disable iff(rst)
    exclusive_0 |-> (state_1 == Invalid || addr_0 != addr_1));

assume property (@(posedge clk) disable iff(rst)
    exclusive_1 |-> (state_0 == Invalid || addr_0 != addr_1));

// Once a transaction starts (Read or Write), the address must not change 
// until the cache reaches a stable state (Shared, Exclusive, or Modified).
assume property (@(posedge clk) disable iff(rst) 
    (cpu_read[0] || cpu_write[0]) && (state_0 != Invalid) |=> $stable(addr_0));
// Once a transaction starts (Read or Write), the address must not change 
// until the cache reaches a stable state (Shared, Exclusive, or Modified).
assume property (@(posedge clk) disable iff(rst) 
    (cpu_read[1] || cpu_write[1]) && (state_1 != Invalid) |=> $stable(addr_1));

assume property (@(posedge clk)disable iff(rst) (state_0 != Invalid && bus_cmd != No_OP) |=> $stable(addr_0));
assume property (@(posedge clk)disable iff(rst) (state_1 != Invalid && bus_cmd != No_OP) |=> $stable(addr_1));






//If a cache requests a bus, it's eventually granted
assume property (@(posedge clk) disable iff(rst) (cpu_read[0] || cpu_write[0]) && state_0 == Invalid |-> s_eventually bus_owner[0]);
assume property (@(posedge clk) disable iff(rst) (cpu_read[1] || cpu_write[1]) && state_1 == Invalid |-> s_eventually bus_owner[1]);

//Bus doesn't stay idle
assume property (@(posedge clk) disable iff(rst) 
    (cpu_read[0] || cpu_write[0] || cpu_read[1] || cpu_write[1]) |-> s_eventually (bus_cmd != No_OP));

//Requests hold until bus received
assume property (@(posedge clk) disable iff(rst) 
    (cpu_read[0] && !bus_owner[0]) |=> cpu_read[0]);
assume property (@(posedge clk) disable iff(rst) 
    (cpu_write[0] && !bus_owner[0]) |=> cpu_write[0]);

assume property (@(posedge clk) disable iff(rst) 
    (cpu_read[1] && !bus_owner[1]) |=> cpu_read[1]);
assume property (@(posedge clk) disable iff(rst) 
    (cpu_write[1] && !bus_owner[1]) |=> cpu_write[1]);

//when read/write, bus should be stable
//assume property(@(posedge clk) disable iff(rst)  (cpu_write[0] || cpu_write[1]) |=> $stable(bus_owner));
// Cache 0 must keep the bus until it reaches the Modified state
assume property (@(posedge clk) disable iff(rst) 
    (cpu_write[0] && bus_owner[0] && state_0 != Modified) |=> bus_owner[0]);

// Cache 1 must keep the bus until it reaches the Modified state
assume property (@(posedge clk) disable iff(rst) 
    (cpu_write[1] && bus_owner[1] && state_1 != Modified) |=> bus_owner[1]);







//no two caches in modified for same address
assert property ( @(posedge clk) disable iff(rst) (addr_0 == addr_1) |=> (!(state_0 == Modified && state_1 == Modified)));

//no two caches in Exclusive state for same address
assert property ( @(posedge clk) disable iff(rst) (addr_0 == addr_1) |=> (!(state_0 == Exclusive && state_1 == Exclusive)));

//if one in modified, other in invalid (for state_0)
assert property (@(posedge clk) disable iff(rst) (addr_0 == addr_1 && state_0 == Modified) |-> (state_1 == Invalid) );
assert property (@(posedge clk) disable iff(rst) (addr_0 == addr_1 && state_1 == Modified) |-> (state_0 == Invalid) );

//if one in exclusive, other invalid
assert property (@(posedge clk) disable iff(rst) (addr_0 == addr_1 && state_1 == Exclusive) |-> (state_0 == Invalid) );
assert property (@(posedge clk) disable iff(rst) (addr_0 == addr_1 && state_0 == Exclusive) |-> (state_1 == Invalid) );

//valid transtion to modifed and others to Invalid( state 1 and 0), for same addresses
assert property (@(posedge clk) disable iff(rst) addr_0 == addr_1 && cpu_write[0] |-> ##[1:$] state_0 == Modified && state_1 == Invalid);
assert property (@(posedge clk) disable iff(rst) addr_0 == addr_1 && cpu_write[1] |-> ##[1:$] state_1 == Modified && state_0 == Invalid);

//if address matches they should be either invalid or shared
//assert property ( @(posedge clk) disable iff(rst) addr_0 == addr_1 |=> (state_0 == Invalid || state_0 == Shared) && (state_1 == Invalid || state_1 == Shared) );

//valid states when address matches
assert property (@(posedge clk) disable iff(rst) (addr_0 == addr_1) |=>
                                                    ((state_0 == Invalid && state_1 == Invalid) ||
                                                    (state_0 == Invalid && state_1 == Shared) ||
                                                    (state_0 == Shared && state_1 == Invalid) ||
                                                    (state_0 == Shared && state_1 == Shared) ||
                                                    //only one exclusive, other Invalid
                                                    (state_0 == Exclusive && state_1 == Invalid) ||
                                                    (state_0 == Invalid && state_1 == Exclusive) ||
                                                    //one Modified, other Invalid
                                                    (state_0 == Modified && state_1 == Invalid) ||
                                                    (state_0 == Invalid && state_1 == Modified) 
                                                    ));

//Modifed to shared happens on BusRd
// assert property (@(posedge clk) disable iff(rst) (state_0 == Modified && addr_0 == addr_1) ##1 state_0 == Shared |->
                                                    //$past(bus_cmd == BusRd && bus_owner[1]));
// assert property (@(posedge clk) disable iff(rst) (state_1 == Modified && addr_0 == addr_1) ##1 state_1 == Shared |->
                                                    //$past(bus_cmd == BusRd && bus_owner[0]));


//Shared to Invalid requires invalidation(BusRdX or BusUpgr)
assert property (@(posedge clk) disable iff(rst) (state_0 == Shared && (addr_1 == addr_0) && (bus_cmd == BusRdX || bus_cmd == BusUpgr) && !bus_owner[0]) |=> (state_0 == Invalid) && $past(bus_owner[1] == 1'b1) );

assert property (@(posedge clk) disable iff(rst) (state_1 == Shared && (addr_1 == addr_0) && (bus_cmd == BusRdX || bus_cmd == BusUpgr) && !bus_owner[1]) |=> (state_1 == Invalid) && $past(bus_owner[0] == 1'b1) );

//assert property (@(posedge clk) disable iff(rst) (state_0 == Shared && addr_0 == addr_1) ##1 state_0 == Invalid |->
  //                                                  $past( (bus_cmd == BusRdX || bus_cmd == BusUpgr)) && $past(addr_0) == addr_0);
//assert property (@(posedge clk) disable iff(rst) (state_1 == Shared && addr_0 == addr_1) ##1 state_1 == Invalid |->
  //                                                  $past( (bus_cmd == BusRdX || bus_cmd == BusUpgr), 1) && $past(bus_owner[0], 1));
                                                
//Exclusive to Shared requires BusRd
assert property (@(posedge clk) disable iff(rst) (state_0 == Exclusive && addr_0 == addr_1) ##1 state_0 == Shared |->
                                                    $past( bus_cmd == BusRd, 2) && $past(bus_owner[1],2));
assert property (@(posedge clk) disable iff(rst) (state_1 == Exclusive && addr_0 == addr_1) ##1 state_1 == Shared |->
                                                    $past( bus_cmd == BusRd && bus_owner[0]));

//Exclusive to Invalid requires BusRdX
assert property (@(posedge clk) disable iff(rst) (state_0 == Exclusive) && (addr_1 == addr_0) && (bus_cmd == BusRdX) |=> (state_0 == Invalid) && $past(bus_owner[1] == 1'b1) );
assert property (@(posedge clk) disable iff(rst) (state_1 == Exclusive) && (addr_1 == addr_0) && (bus_cmd == BusRdX) |=> (state_1 == Invalid) && $past(bus_owner[0] == 1'b1) );


//assert property (@(posedge clk) disable iff(rst) (state_0 == Exclusive && addr_0 == addr_1) ##1 state_0 == Invalid |->
  //                                                  $past( bus_cmd == BusRdX && bus_owner[1]));
//assert property (@(posedge clk) disable iff(rst) (state_1 == Exclusive && addr_0 == addr_1) ##1 state_1 == Invalid |->
  //                                                  $past( bus_cmd == BusRdX && bus_owner[0]));

//Exclusive to Modified don't need any bus_cmd output(because current has exclusive access)
assert property (@(posedge clk) disable iff(rst) ((state_0 == Exclusive) && (addr_0 == addr_1) && cpu_write[0] && bus_owner[0]) |=> state_0 == Modified);
assert property (@(posedge clk) disable iff(rst) ((state_1 == Exclusive) && (addr_0 == addr_1) && cpu_write[1] && bus_owner[1]) |=> state_1 == Modified);

//State shouldn't change for own bus request
assert property (@(posedge clk) disable iff(rst) (bus_owner[0] && !cpu_write[0] && !cpu_read[0]) && !cache_0.snoop_hit  |=> $stable(state_0));
assert property (@(posedge clk) disable iff(rst) (bus_owner[1] && !cpu_write[1] && !cpu_read[1]) && !cache_1.snoop_hit |=> $stable(state_1));

//Invalid State shouldn't change without busownership


//Shared or Invalid eventually reaches to Modified on write
assert property ( @(posedge clk) disable iff(rst) (state_0 == Shared || state_0 == Invalid) && cpu_write[0] |-> ##[1:$] state_0 == Modified);
assert property ( @(posedge clk) disable iff(rst) (state_1 == Shared || state_1 == Invalid) && cpu_write[1] |-> ##[1:$] state_1 == Modified);

//Invalid to Shared or Exclusive
//assert property (@(posedge clk) disable iff(rst) (state_0 == Invalid && cpu_read[0]) |-> (state_0 == Shared || state_0 == Exclusive));
//assert property (@(posedge clk) disable iff(rst) (state_1 == Invalid && cpu_read[1]) |-> (state_1 == Shared || state_1 == Exclusive));


//only one gets M on Write
assert property (@(posedge clk) disable iff(rst) (cpu_write[0] && cpu_write[1] && addr_0 == addr_1) && bus_owner[0] |=> ##1 (state_0 == Modified && state_1 == Invalid) );
assert property (@(posedge clk) disable iff(rst) (cpu_write[0] && cpu_write[1] && addr_0 == addr_1) && bus_owner[1] |=> ##1 (state_1 == Modified && state_0 == Invalid) );

//on write, it goes to M eventually
assert property (@(posedge clk) disable iff(rst) cpu_write[0] && state_1 == Invalid && bus_owner[0] |-> ##[1:20] state_0 == Modified);
//assert property (@(posedge clk) disable iff(rst) cpu_write[1] && state_0 == Invalid && bus_owner[1] && (bus_cmd == BusRdX && bus_cmd == BusUpgr) && (cache_1. snoop_hit == 1'b0) |-> ##[1:20] state_1 == Modified);

//when both invalid, on read request, it goes to Exclusive
assert property (@(posedge clk) disable iff(rst) (state_0 == Invalid && state_1 == Invalid) && addr_0 == addr_1 && cpu_read[0] |=> ##[1:20] state_0 == Exclusive);
assert property (@(posedge clk) disable iff(rst) (state_0 == Invalid && state_1 == Invalid) && addr_0 == addr_1 && cpu_read[1] |=> ##[1:20] state_1 == Exclusive);

//When one in Exclusive, and other wants to read, both ends up in Shared
assert property (@(posedge clk) disable iff(rst) (state_0 == Exclusive && state_1 == Invalid) && addr_0 == addr_1 && cpu_read[1] |=> ##[1:3] (state_1 == Shared && state_0 == Shared));
assert property (@(posedge clk) disable iff(rst) (state_0 == Invalid && state_1 == Exclusive) && addr_0 == addr_1 && cpu_read[0] |=> ##[1:3] (state_1 == Shared && state_0 == Shared));

//When in Exclsuive other wants to write, it goes Invalid and other to modified
assert property (@(posedge clk) disable iff(rst) (state_0 == Exclusive && cpu_write[1] |=> (state_0 == Invalid && state_1 == Modified)));
assert property (@(posedge clk) disable iff(rst) (state_1 == Exclusive && cpu_write[0] |=> (state_1 == Invalid && state_0 == Modified)));






cover property (@(posedge clk) disable iff(rst) state_0 == Invalid);
cover property (@(posedge clk) disable iff(rst) state_1 == Invalid);
cover property (@(posedge clk) disable iff(rst) state_0 == Shared);
cover property (@(posedge clk) disable iff(rst) state_1 == Shared);
cover property (@(posedge clk) disable iff(rst) state_0 == Exclusive);
cover property (@(posedge clk) disable iff(rst) state_1 == Exclusive);
cover property (@(posedge clk) disable iff(rst) state_0 == Modified);
cover property (@(posedge clk) disable iff(rst) state_1 == Modified);

//both caches reaches Modified state
cover property (@(posedge clk) disable iff(rst) state_0 == Invalid |-> s_eventually state_0 == Modified);
cover property (@(posedge clk) disable iff(rst) state_1 == Invalid |-> s_eventually state_1 == Modified);



endmodule
