module led_diag (
    input  wire clk_27,
    output wire led0,
    output wire led1,
    output wire led2,
    output wire led3,
    output wire led4,
    output wire led5
);
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    
    // All LEDs blink at different rates
    assign led0 = ~blink[24];  // slowest
    assign led1 = ~blink[23];
    assign led2 = ~blink[22];
    assign led3 = ~blink[21];
    assign led4 = ~blink[20];  // THIS IS THE ONE — does it work at all?
    assign led5 = ~blink[19];  // fastest
endmodule
