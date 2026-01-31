`include "mesi_types.sv"
import mesi_types::*;

module bus(
    input logic clk, rst,
    input bus_request cmd_in[2],
    input logic [7:0] bus_addr[2],

    output bus_request cmd_out,
    output logic [7:0] addr_out,
    output logic [1:0] bus_owner
);

    // Sequential Bus Arbitration
    // This breaks the combinational loop by registering the outputs
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            cmd_out     <= No_OP;
            addr_out    <= 8'h00;
            // 2'b00 means no one owns the bus
            bus_owner   <= 2'b00; 
        end else begin
            // Priority Arbitration: Cache 0 has priority over Cache 1
            if (cmd_in[0] != No_OP) begin
                cmd_out     <= cmd_in[0];
                addr_out    <= bus_addr[0];
                // Set bit 0 high so cache_0 sees it owns the bus
                bus_owner   <= 2'b01; 
            end else if (cmd_in[1] != No_OP) begin
                cmd_out     <= cmd_in[1];
                addr_out    <= bus_addr[1];
                // Set bit 1 high so cache_1 sees it owns the bus
                bus_owner   <= 2'b10; 
            end else begin
                // Default / Idle state
                cmd_out     <= No_OP;
                addr_out    <= 8'h00;
                bus_owner   <= 2'b00;
            end
        end
    end

endmodule
