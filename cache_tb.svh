`timescale 1ns/100ps

module cache_tb();
logic clk = 1'b0, rst;
logic cpu_read[2], cpu_write[2];
logic [7:0] cpu_addr[2];
logic exclusive_0, exclusive_1;

initial begin :generate_clock
    forever #5 clk = ~clk;
end

// always begin : generate_clock
//   #5 clk = ~clk;
// end
cache_top coherence (.clk(clk), .rst(rst), .cpu_read(cpu_read),
                    .cpu_write(cpu_write), .cpu_addr(cpu_addr), .exclusive_0(exclusive_0), .exclusive_1(exclusive_1)
);

initial begin : generate_stimulus
    $timeformat(-9, 0, "ns");
    @(posedge clk);
    rst <= 1'b1;
    cpu_read[0] <= 0; cpu_write[0] <= 0; cpu_addr[0] <= 8'hAA;
    cpu_read[1] <= 0; cpu_write[1] <= 0; cpu_addr[1] <= 8'hAA;
    repeat (3) @(posedge clk);
    @(negedge clk);
    rst <= 1'b0;
    @(posedge clk);
    for( int i =0; i<100; i++) begin
        cpu_read[0] <= $urandom_range(2); cpu_write[0] <= $urandom_range(2); //cpu_addr[0] <= 8'hAA;
        cpu_read[1] <= $urandom_range(2); cpu_write[1] <= $urandom_range(2); //cpu_addr[1] <= 8'hAA;
        exclusive_0 <= $urandom_range(2);
        exclusive_1 <= $urandom_range(2);
        @(posedge clk);
    end

    // exclusive_0 <= 1;
    // exclusive_1 <= 0;
    // @(posedge clk);
    
    // cpu_read[0] <= 1; @(posedge clk); cpu_read[0] <= 0; // Core 0 reads
    // exclusive_0 <= 0;
    // exclusive_1 <= 1;
    // @(posedge clk);
    // cpu_read[1] <= 1; @(posedge clk); cpu_read[1] <= 0; // Core 1 reads (shared)
    // exclusive_0 <= 1;
    // exclusive_1 <= 1;
    // @(posedge clk);
    // cpu_write[0] <= 1; @(posedge clk); cpu_write[0] <= 0; // Core 0 writes  
    // exclusive_0 <= 0;
    // exclusive_1 <= 0;
    // @(posedge clk);
    // cpu_read[1] <= 1; @(posedge clk); cpu_read[1] <= 0; // Core 1 reads again (must invalidate)
    // exclusive_0 <= 1;
    // exclusive_1 <= 1;
    repeat (4) @(posedge clk);
    
    disable generate_clock;
end

endmodule
