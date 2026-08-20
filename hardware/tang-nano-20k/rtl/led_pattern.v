module led_pattern (
    input  wire clk_27,
    output wire led0, led1, led2, led3, led4, led5
);
    // Active-low: 0=ON, 1=OFF
    assign led0 = 1'b1;  // ON
    assign led1 = 1'b0;  // OFF
    assign led2 = 1'b1;  // ON
    assign led3 = 1'b0;  // OFF
    assign led4 = 1'b1;  // ON
    assign led5 = 1'b0;  // OFF
endmodule
