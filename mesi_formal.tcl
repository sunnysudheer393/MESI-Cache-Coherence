clear -all

analyze -sv12  mesi_types.sv \
		cache_mem.sv \
		bus.sv \
		cache_top.sv

analyze -sv12 mesi_fv_tb.sv \ mesi_bind.sv

check_cov -init -type all -model {branch toggle statement} -toggle_ports_only

elaborate -top cache_top

clock clk

reset -expression {rst == 1'b1}

prove -all

check_cov -measure -type {coi stimuli proof bound} -time_limit 60s -bg