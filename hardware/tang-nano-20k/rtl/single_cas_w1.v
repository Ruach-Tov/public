module single_cas (
    input  wire [1:0] data_i,
    output wire [1:0] data_o
);
    wire [0:0] a = data_i[0:0];
    wire [0:0] b = data_i[1:1];
    wire [0:0] lo = (a <= b) ? a : b;
    wire [0:0] hi = (a <= b) ? b : a;
    assign data_o = {hi, lo};
endmodule
