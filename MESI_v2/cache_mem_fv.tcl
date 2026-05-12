clear -all

analyze -sv12 mesi_types.sv \
            cache_mem_v2.sv \
            cache_mem_fv.sv 

check_cov -init -type all -model {branch toggle statement} -toggle_ports_only

elaborate -top cache_mem_v2

clock clk
reset -expression {rst == 1'b1}

prove -all

check_cov -measure -type {coi stimuli proof bound} -time_limit 60s -bg
