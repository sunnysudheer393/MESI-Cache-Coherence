// typedef enum logic [1:0] { No_OP = 2'b00, BusRd = 2'b01, BusRdX = 2'b10, BusUpgr = 2'b11 } bus_request;
`include "mesi_types.svh"
import mesi_types::*;

module bus(
    input logic clk, rst,
    input bus_request cmd_in[2],
    input logic [7:0] bus_addr[2],

    output bus_request cmd_out,
    output logic [7:0] addr_out
);

always_comb begin
    if (rst) begin
        cmd_out = No_OP;
    end else if(cmd_in[0] != No_OP) begin
        cmd_out = cmd_in[0];
        addr_out = bus_addr[0];
    end else if (cmd_in[1] != No_OP) begin
        cmd_out = cmd_in[1];
        addr_out = bus_addr[1];
    end else begin
        cmd_out = No_OP;
        addr_out = 8'h00;
    end
end

endmodule

// module bus(
//     input logic clk, rst,
//     input bus_request cmd_in[2],
//     input logic [7:0] bus_addr[2],

//     output logic [1:0] granted_id,  // Optional: for debugging
//     output bus_request cmd_out,
//     output logic [7:0] addr_out
// );

// logic [1:0] owner;
// bus_request granted_cmd;
// logic [7:0] granted_addr;

// always_ff @(posedge clk or posedge rst) begin
//     if (rst) begin
//         owner <= 2'b11;  // No owner
//         granted_cmd <= No_OP;
//         granted_addr <= 8'h00;
//     end else begin
//         case (owner)
//             2'b00: begin
//                 if (cmd_in[0] == No_OP)
//                     owner <= 2'b11;
//                 granted_cmd <= cmd_in[0];
//                 granted_addr <= bus_addr[0];
//             end
//             2'b01: begin
//                 if (cmd_in[1] == No_OP)
//                     owner <= 2'b11;
//                 granted_cmd <= cmd_in[1];
//                 granted_addr <= bus_addr[1];
//             end
//             default: begin
//                 if (cmd_in[0] != No_OP) begin
//                     owner <= 2'b00;
//                     granted_cmd <= cmd_in[0];
//                     granted_addr <= bus_addr[0];
//                 end else if (cmd_in[1] != No_OP) begin
//                     owner <= 2'b01;
//                     granted_cmd <= cmd_in[1];
//                     granted_addr <= bus_addr[1];
//                 end else begin
//                     granted_cmd <= No_OP;
//                     granted_addr <= 8'h00;
//                 end
//             end
//         endcase
//     end
// end

// assign cmd_out = granted_cmd;
// assign addr_out = granted_addr;
// assign granted_id = owner;

// endmodule

