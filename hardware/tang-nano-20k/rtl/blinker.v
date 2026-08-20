module blinker (
    input  wire clk,
    output wire led0,
    output wire led1,
    output wire led2,
    output wire led3,
    output wire led4,
    output wire led5
);
    reg [24:0] counter;
    always @(posedge clk) counter <= counter + 1;
    
    // Try multiple pins — one will blink
    assign led0 = counter[24];
    assign led1 = counter[23];
    assign led2 = counter[22];
    assign led3 = counter[21];
    assign led4 = counter[20];
    assign led5 = counter[19];
endmodule
