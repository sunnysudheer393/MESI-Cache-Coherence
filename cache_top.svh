`include "mesi_types.sv"
import mesi_types::*;

module cache_top(
    input logic clk, rst,
    input logic cpu_read[2], cpu_write[2],
    input logic [7:0] cpu_addr[2],
    input logic exclusive_1, exclusive_0

);

bus_request bus_cmd_in[2]; // from caches to Bus
bus_request bus_cmd_out; // from Bus to caches
logic [7:0] bus_addr_in[2]; // from caches to Bus
logic [7:0] bus_addr_out; // from Bus to caches
logic [1:0] bus_owner; // from Bus to Caches

//logic [7:0] addr_out;

// logic cpu_read[2], cpu_write[2];

// logic [7:0] cpu_addr[2];
logic [7:0] data_out[2];

cache_mem cache_0(
    .clk(clk), .rst(rst), .cpu_read(cpu_read[0]), .cpu_write(cpu_write[0]), .exclusive(exclusive_0),
    .bus_cmd_in(bus_cmd_out), 
    .address(cpu_addr[0]),
    .bus_addr_in(bus_addr_out),
    .bus_owner(bus_owner[0]),

    .data_out(data_out[0]),
    .bus_cmd_out(bus_cmd_in[0]),
    .bus_addr_out(bus_addr_in[0])

);

cache_mem cache_1(
    .clk(clk), .rst(rst), .cpu_read(cpu_read[1]), .cpu_write(cpu_write[1]), .exclusive(exclusive_1),
    .bus_cmd_in(bus_cmd_out), 
    .address(cpu_addr[1]),
    .bus_addr_in(bus_addr_out),
    .bus_owner(bus_owner[1]),

    .data_out(data_out[1]),
    .bus_cmd_out(bus_cmd_in[1]),
    .bus_addr_out(bus_addr_in[1])

);

bus shared_bus(
    .clk(clk), .rst(rst),
    .cmd_in(bus_cmd_in),
    .bus_addr(bus_addr_in),
    

    .cmd_out(bus_cmd_out),
    .addr_out(bus_addr_out),
    .bus_owner(bus_owner)
);


endmodule
