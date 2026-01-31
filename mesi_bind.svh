
bind cache_top mesi_fv_tb fv_tb (.clk(clk),
                        .rst(rst),
                        .state_0(cache_0.current_state),
                        .state_1(cache_1.current_state),
                        .addr_0(cpu_addr[0]),
			            .cpu_write(cpu_write),
			            .cpu_read(cpu_read),
			            .bus_owner(bus_owner),
			            .exclusive_0(exclusive_0),
			            .exclusive_1(exclusive_1),
                        .addr_1(cpu_addr[1]),
                        .bus_cmd(bus_cmd_out)
                        );
