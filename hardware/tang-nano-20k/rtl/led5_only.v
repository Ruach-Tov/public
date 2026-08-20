module led5_only (
    input  wire clk_27,
    output wire led0,
    output wire led1,
    output wire led2,
    output wire led3,
    output wire led4,
    output wire led5
);
    assign led0 = 1'b1;
    assign led1 = 1'b1;
    assign led2 = 1'b1;
    assign led3 = 1'b1;
    assign led4 = 1'b1;
    assign led5 = 1'b0;
endmodule
