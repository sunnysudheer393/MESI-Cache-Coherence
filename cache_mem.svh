`include "mesi_types.sv"
import mesi_types::*;

module cache_mem(
    input logic clk, rst, cpu_read, cpu_write, exclusive,
    input bus_request bus_cmd_in, 
    input logic [7:0] address,
    input logic [7:0] bus_addr_in,
    input logic bus_owner,

    output logic [7:0] data_out,
    output bus_request bus_cmd_out,
    output logic [7:0] bus_addr_out

);

cache_state current_state, next_state;

always_comb begin
    if (cpu_read && current_state == Invalid)
        bus_cmd_out = BusRd;
    else if (cpu_write && current_state == Invalid)
        bus_cmd_out = BusRdX;
    else if (cpu_write && current_state == Shared)
        bus_cmd_out = BusUpgr;
    else
        bus_cmd_out = No_OP;
end

assign bus_addr_out = address;

// assign bus_addr_out = address;

//snoop only for other Bus request not current one
logic snoop_hit;
assign snoop_hit = (bus_addr_in == address) && (bus_cmd_in != No_OP) && !bus_owner;

always_ff @( posedge clk or posedge rst ) begin
    if (rst) begin
        current_state <= Invalid;
    end else begin
        current_state <= next_state;
    end
end

always_comb begin
        next_state = current_state;
	if(address != bus_addr_in && !bus_owner) begin
		next_state = Invalid;
		//next_state = current_state;
	end else begin
		case(current_state)
		    Invalid: begin
		        if(bus_owner) begin
		            if (cpu_read && bus_cmd_in == BusRd && exclusive) next_state = Exclusive;
		            else if(cpu_read && bus_cmd_in == BusRd && !exclusive) next_state = Shared;
		            else if (cpu_write && bus_cmd_in == BusRdX && bus_owner && !snoop_hit) next_state = Modified;
		            //else if (cpu_read && bus_cmd_in == BusRd && exclusive) next_state = Exclusive;
		        end
		    end
		    Shared: begin
		        if (snoop_hit && (bus_cmd_in == BusRdX || bus_cmd_in == BusUpgr)) next_state = Invalid;
			else if(cpu_write && bus_owner && bus_cmd_in == BusUpgr && !snoop_hit) next_state = Modified;
		    end
		    Exclusive: begin
		        if (snoop_hit && bus_cmd_in == BusRdX) next_state = Invalid;
			else if (snoop_hit && bus_cmd_in == BusRd) next_state = Shared;		
			else if(cpu_write && bus_owner && !snoop_hit) next_state = Modified;
		        
		    end
		    Modified: begin
		        if(snoop_hit && bus_cmd_in == BusRd) next_state = Shared; //current processor writes back
		        else if (snoop_hit && bus_cmd_in == BusRdX) next_state = Invalid;//current processor writes back
		    end
		endcase
	end
end

endmodule
