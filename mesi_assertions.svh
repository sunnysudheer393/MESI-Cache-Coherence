module mesi_assertions();


property no_two_modified;
    @(posedge clk) disable iff(rst)
    (addr1[0]==addr2[1]) |-> !(state_r_1 == Modified && state_r_2 == Modified);
endproperty
assert property ( no_two_modified);

property valid_state_transition_1;
    @(posedge clk) disable iff(rst)
    (state_r_1 == Invalid) |=> ($past(state_r_1 == Modified)||$past(state_r_1 == Shared)|| $past(state_r_1 == Exclusive)); 
endproperty
assert property (valid_state_transition_1);

property valid_state_transition_2;
    @(posedge clk) disable iff(rst)
    (state_r_2 == Invalid) |=> ($past(state_r_2 == Modified)||$past(state_r_2 == Shared)|| $past(state_r_2 == Exclusive)); 
endproperty
assert property (valid_state_transition_2);

property only_one_gnt_M_state;
    @(posedge clk) disable iff(rst)
    (cpu_write(0) && cpu_write(1)) |=> (cpu_state_0 == Modified || cpu_state_1 == Modified);
endproperty
assert property (only_one_gnt_M_state);

property only_one_gnt;
    @(posedge clk) disable iff(rst)
    $onehot0(gnt);
endproperty
assert property (only_one_gnt);

property valid_transition_0;
    @(posedge clk) disable iff(rst)
    (cpu_write(0) |=> state_r_1 == Modified && state_r_2 == Invalid );
endproperty
assert property (valid_transition_0);

property valid_transition_1;
    @(posedge clk) disable iff(rst)
    (cpu_write(1) |=> state_r_2 == Modified && state_r_1 == Invalid );
endproperty
assert property (valid_transition_1);

property one_M_other_I_0;
    @(posedge clk) disable iff(rst)
    (cpu_state_0 == Modified) |-> (cpu_state_1 == Invalid);
endproperty
assert property (one_M_other_I_0);

property one_M_other_I_1;
    @(posedge clk) disable iff(rst)
    (cpu_state_1 == Modified) |-> (cpu_state_0 == Invalid);
endproperty
assert property (one_M_other_I_1);

property one_hot_exclusive_0;
    @(posedge clk) disable iff(rst)
    (cpu_state_0 == Exclusive) |-> (cpu_state_1 == Invalid);
endproperty
assert property (one_hot_exclusive_0);

property one_hot_exclusive_0;
    @(posedge clk) disable iff(rst)
    (cpu_state_1 == Exclusive) |-> (cpu_state_0 == Invalid);
endproperty
assert property (one_hot_exclusive_1);

property valid_I_transition_0;
    @(posedge clk) disable iff(rst)
    (cpu_state_0== Modified || cpu_state_0== Exclusive || cpu_state_0== Shared) && $rose(cpu_write_1) |=> (cpu_state_0 == Invalid);
endproperty
assert property (valid_I_transition_0);

property valid_I_transition_1;
    @(posedge clk) disable iff(rst)
    (cpu_state_1== Modified || cpu_state_1== Exclusive || cpu_state_1== Shared) && $rose(cpu_write_0) |=> (cpu_state_1 == Invalid);
endproperty
assert property (valid_I_transition_1);

property eventually_gets_M_state(a);
    @(posedge clk) disable iff(rst)
    (cpu_write[a] |-> s_eventually cpu_state[a] == Modified);
endproperty
assert propoerty (eventually_gets_M_state(0));
assert propoerty (eventually_gets_M_state(1));

property invalid_transition_0;
    @(posedge clk) disable iff(rst)
    (cpu_state_0 == Modified || cpu_state_0 == Exclusive || cpu_state_0 == Shared) && cpu_write_1 |=> !(cpu_state_0 == Modified || cpu_state_0 == Exclusive || cpu_state_0 == Shared);
endproperty
assert property (invalid_transition_0);

property invalid_transition_1;
    @(posedge clk) disable iff(rst)
    (cpu_state_1 == Modified || cpu_state_1 == Exclusive || cpu_state_1 == Shared) && cpu_write_0 |=> !(cpu_state_1 == Modified || cpu_state_1 == Exclusive || cpu_state_1 == Shared);
endproperty
assert property (invalid_transition_1);

property valid_state_to_E_0;
     @(posedge clk) disable iff(rst)
    (cpu_state_1 == Invalid) && (cpu_state_0 == Invalid) && cpu_read_0 |=> cpu_state_0 == Exclusive ;
endproperty
assert property (valid_state_to_E_0);

property valid_state_to_E_1;
     @(posedge clk) disable iff(rst)
    (cpu_state_0 == Invalid) && (cpu_state_1 == Invalid) && cpu_read_1 |=> cpu_state_1 == Exclusive ;
endproperty
assert property (valid_state_to_E_1);

property valid_state_to_S_0;
    (cpu_state_0 == Exclusive && cpu_state_1 == Invalid) && cpu_write_1 |=> (cpu_state_1 == Shared && cpu_state_0 == Shared); 
endproperty
assert property (valid_state_to_S_0);

property valid_state_to_S_1;
    (cpu_state_1 == Exclusive && cpu_state_0 == Invalid) && cpu_write_0 |=> (cpu_state_1 == Shared && cpu_state_0 == Shared); 
endproperty
assert property (valid_state_to_S_0);

property valid_S_from_E_0;
    @(posedge clk) disable iff(rst)
    (cpu_state_0 == Exclusive && cpu_read_1) |=> cpu_state_0 == Shared && cpu_state_1 == Shared ; 
endproperty
assert property (valid_S_from_E_0);

property valid_S_from_E_1;
    @(posedge clk) disable iff(rst)
    (cpu_state_1 == Exclusive && cpu_read_0) |=> cpu_state_0 == Shared && cpu_state_1 == Shared ; 
endproperty
assert property (valid_S_from_E_1);

property valid_I_from_M_0;
    @(posedge clk) disable iff(rst)
    (cpu_state_0 == Modified && cpu_write_1) |=> cpu_state_0 == Invalid && cpu_state_1 == Modified ;
endproperty
assert property (valid_I_from_M_0);

property valid_I_from_M_1;
    @(posedge clk) disable iff(rst)
    (cpu_state_1 == Modified && cpu_write_0) |=> cpu_state_1 == Invalid && cpu_state_0 == Modified ;
endproperty
assert property (valid_I_from_M_0);

property valid_I_from_E_0;
    @(posedge clk) disable iff(rst)
    (cpu_state_0 == Exclusive && cpu_write_1) |=> cpu_state_0 == Invalid && cpu_state_1 == Modified ;
endproperty
assert property (valid_I_from_M_0);

property valid_I_from_E_1;
    @(posedge clk) disable iff(rst)
    (cpu_state_1 == Exclusive && cpu_write_0) |=> cpu_state_1 == Invalid && cpu_state_0 == Modified ;
endproperty
assert property (valid_I_from_M_0);

property valid_data_cache_mem_0;
    @(posedge clk) disable iff(rst)
    (cpu_state_0 == M) |=> (cache_mem[0] == data_mem[0]);
endproperty
assert property (valid_data_cache_mem_0);

property valid_data_cache_mem_1;
    @(posedge clk) disable iff(rst)
    (cpu_state_1 == M) |=> (cache_mem[1] == data_mem[1]);
endproperty
assert property (valid_data_cache_mem_1);

endmodule
