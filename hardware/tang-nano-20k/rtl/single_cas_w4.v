module single_cas (
    input  wire [7:0] data_i,
    output wire [7:0] data_o
);
    wire [3:0] a = data_i[3:0];
    wire [3:0] b = data_i[7:4];
    wire [3:0] lo = (a <= b) ? a : b;
    wire [3:0] hi = (a <= b) ? b : a;
    assign data_o = {hi, lo};
endmodule
