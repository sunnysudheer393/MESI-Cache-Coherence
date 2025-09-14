/*
// MESI Cache Coherence Protocol for 2 Cores
module mesi_2core (
    input logic clk,
    input logic reset,
    // Core 0 interface
    input logic core0_rd, core0_wr,
    input logic [31:0] core0_addr,
    input logic [31:0] core0_data_in,
    output logic [31:0] core0_data_out,
    output logic core0_ready,
    // Core 1 interface
    input logic core1_rd, core1_wr,
    input logic [31:0] core1_addr,
    input logic [31:0] core1_data_in,
    output logic [31:0] core1_data_out,
    output logic core1_ready
);

// MESI states
typedef enum logic [1:0] {
    INVALID = 2'b00,
    SHARED = 2'b01,
    EXCLUSIVE = 2'b10,
    MODIFIED = 2'b11
} mesi_state_t;

// Bus operations
typedef enum logic [1:0] {
    NO_OP = 2'b00,
    BUS_RD = 2'b01,
    BUS_RDX = 2'b10,
    INVALIDATE = 2'b11
} bus_op_t;

// Cache line structure
typedef struct packed {
    mesi_state_t state;
    logic [31:0] data;
    logic [31:0] addr;
} cache_line_t;

// Bus request structure
typedef struct packed {
    bus_op_t op;
    logic [31:0] addr;
} bus_request_t;

// Cache and bus signals
cache_line_t cache0, cache1;
bus_request_t bus_req0, bus_req1, bus_granted;
logic bus_busy;
logic [1:0] arb_grant; // 0: none, 1: core0, 2: core1

// Main memory (simplified)
logic [31:0] memory [0:255];

// Cache controller for core 0
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        cache0.state <= INVALID;
        cache0.data <= 0;
        cache0.addr <= 0;
        core0_ready <= 0;
        bus_req0 <= '{op: NO_OP, addr: 0};
    end else begin
        core0_ready <= 0;
        bus_req0 <= '{op: NO_OP, addr: 0};

        // Handle core0 requests
        if (core0_rd && cache0.addr == core0_addr && cache0.state != INVALID) begin
            // Cache hit (S, E, M)
            core0_data_out <= cache0.data;
            core0_ready <= 1;
        end else if (core0_rd) begin
            // Read miss
            bus_req0 <= '{op: BUS_RD, addr: core0_addr};
            if (arb_grant == 2'b01 && !bus_busy) begin
                cache0.addr <= core0_addr;
                cache0.data <= memory[core0_addr[7:0]];
                cache0.state <= (cache1.addr == core0_addr && cache1.state != INVALID) ? SHARED : EXCLUSIVE;
                core0_data_out <= memory[core0_addr[7:0]];
                core0_ready <= 1;
            end
        end else if (core0_wr && cache0.addr == core0_addr && (cache0.state == EXCLUSIVE || cache0.state == MODIFIED)) begin
            // Write hit
            cache0.data <= core0_data_in;
            cache0.state <= MODIFIED;
            core0_ready <= 1;
        end else if (core0_wr) begin
            // Write miss or write to shared
            bus_req0 <= '{op: BUS_RDX, addr: core0_addr};
            if (arb_grant == 2'b01 && !bus_busy) begin
                cache0.addr <= core0_addr;
                cache0.data <= core0_data_in;
                cache0.state <= MODIFIED;
                memory[core0_addr[7:0]] <= core0_data_in;
                core0_ready <= 1;
            end
        end

        // Handle bus snooping for core0
        if (bus_granted.op != NO_OP && bus_granted.addr == cache0.addr && arb_grant != 2'b01) begin
            case (bus_granted.op)
                BUS_RD: begin
                    if (cache0.state == MODIFIED) begin
                        memory[cache0.addr[7:0]] <= cache0.data;
                        cache0.state <= SHARED;
                    end else if (cache0.state == EXCLUSIVE) begin
                        cache0.state <= SHARED;
                    end
                end
                BUS_RDX, INVALIDATE: begin
                    if (cache0.state != INVALID) begin
                        if (cache0.state == MODIFIED) begin
                            memory[cache0.addr[7:0]] <= cache0.data;
                        end
                        cache0.state <= INVALID;
                    end
                end
            endcase
        end
    end
end

// Cache controller for core 1
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        cache1.state <= INVALID;
        cache1.data <= 0;
        cache1.addr <= 0;
        core1_ready <= 0;
        bus_req1 <= '{op: NO_OP, addr: 0};
    end else begin
        core1_ready <= 0;
        bus_req1 <= '{op: NO_OP, addr: 0};

        // Handle core1 requests
        if (core1_rd && cache1.addr == core1_addr && cache1.state != INVALID) begin
            // Cache hit (S, E, M)
            core1_data_out <= cache1.data;
            core1_ready <= 1;
        end else if (core1_rd) begin
            // Read miss
            bus_req1 <= '{op: BUS_RD, addr: core1_addr};
            if (arb_grant == 2'b10 && !bus_busy) begin
                cache1.addr <= core1_addr;
                cache1.data <= memory[core1_addr[7:0]];
                cache1.state <= (cache0.addr == core1_addr && cache0.state != INVALID) ? SHARED : EXCLUSIVE;
                core1_data_out <= memory[core1_addr[7:0]];
                core1_ready <= 1;
            end
        end else if (core1_wr && cache1.addr == core1_addr && (cache1.state == EXCLUSIVE || cache1.state == MODIFIED)) begin
            // Write hit
            cache1.data <= core1_data_in;
            cache1.state <= MODIFIED;
            core1_ready <= 1;
        end else if (core1_wr) begin
            // Write miss or write to shared
            bus_req1 <= '{op: BUS_RDX, addr: core1_addr};
            if (arb_grant == 2'b10 && !bus_busy) begin
                cache1.addr <= core1_addr;
                cache1.data <= core1_data_in;
                cache1.state <= MODIFIED;
                memory[core1_addr[7:0]] <= core1_data_in;
                core1_ready <= 1;
            end
        end

        // Handle bus snooping for core1
        if (bus_granted.op != NO_OP && bus_granted.addr == cache1.addr && arb_grant != 2'b10) begin
            case (bus_granted.op)
                BUS_RD: begin
                    if (cache1.state == MODIFIED) begin
                        memory[cache1.addr[7:0]] <= cache1.data;
                        cache1.state <= SHARED;
                    end else if (cache1.state == EXCLUSIVE) begin
                        cache1.state <= SHARED;
                    end
                end
                BUS_RDX, INVALIDATE: begin
                    if (cache1.state != INVALID) begin
                        if (cache1.state == MODIFIED) begin
                            memory[cache1.addr[7:0]] <= cache1.data;
                        end
                        cache1.state <= INVALID;
                    end
                end
            endcase
        end
    end
end

// Bus arbiter
always_ff @(posedge clk or posedge reset) begin
    if (reset) begin
        arb_grant <= 2'b00;
        bus_granted <= '{op: NO_OP, addr: 0};
        bus_busy <= 0;
    end else begin
        if (!bus_busy) begin
            if (bus_req0.op != NO_OP) begin
                arb_grant <= 2'b01;
                bus_granted <= bus_req0;
                bus_busy <= 1;
            end else if (bus_req1.op != NO_OP) begin
                arb_grant <= 2'b10;
                bus_granted <= bus_req1;
                bus_busy <= 1;
            end else begin
                arb_grant <= 2'b00;
                bus_granted <= '{op: NO_OP, addr: 0};
            end
        end else begin
            bus_busy <= 0;
            arb_grant <= 2'b00;
            bus_granted <= '{op: NO_OP, addr: 0};
        end
    end
end

// Memory initialization (for simulation)
initial begin
    for (int i = 0; i < 256; i++) begin
        memory[i] = 0;
    end
end

endmodule
*/
`include "mesi_types.svh"
import mesi_types::*;

module cache_mem(
    input logic clk, rst, cpu_read, cpu_write, exclusive,
    input bus_request bus_cmd_in, 
    input logic [7:0] address,
    input logic [7:0] bus_addr_in,

    output logic [7:0] data_out,
    output bus_request bus_cmd_out,
    output logic [7:0] bus_addr_out

);

cache_state state_r;

assign bus_cmd_out = (cpu_read && state_r == Invalid) ? BusRd :
                        (cpu_write && state_r == Invalid) ? BusRdX:
                        (cpu_write && state_r == Shared && exclusive == 1'b1) ? BusUpgr : No_OP;
assign bus_addr_out = address;

always_ff @(posedge clk or negedge rst) begin
    if(rst) begin
        state_r <= Invalid;
    end else begin
        //state_r = present_state;
        case(state_r)
            Invalid: begin
                if(cpu_read && bus_cmd_in == BusRd) state_r <= Shared;
                else if (cpu_write && bus_cmd_in == BusRdX) state_r <= Modified;
                else if (cpu_read && bus_cmd_in == No_OP && exclusive) state_r <= Exclusive;
            end
            Shared: begin
                if(cpu_write) state_r <= Modified;
                else if (bus_cmd_in == BusRdX || bus_cmd_in == BusUpgr) state_r <= Invalid;
            end
            Exclusive: begin
                if(cpu_write) state_r <= Modified;
                else if (bus_cmd_in == BusRdX) state_r <= Invalid;
                else if (bus_cmd_in == BusRd) state_r <= Shared;
            end
            Modified: begin
                if(bus_cmd_in == BusRd) state_r <= Shared; //current processor writes back
                else if (bus_cmd_in == BusRdX) state_r <= Invalid;//current processor writes back
            end
        endcase
    end
end

endmodule
