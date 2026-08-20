module single_cas (
    input  wire [15:0] data_i,
    output wire [15:0] data_o
);
    wire [7:0] a = data_i[7:0];
    wire [7:0] b = data_i[15:8];
    wire [7:0] lo = (a <= b) ? a : b;
    wire [7:0] hi = (a <= b) ? b : a;
    assign data_o = {hi, lo};
endmodule
