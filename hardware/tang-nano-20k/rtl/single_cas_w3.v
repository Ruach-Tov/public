module single_cas (
    input  wire [5:0] data_i,
    output wire [5:0] data_o
);
    wire [2:0] a = data_i[2:0];
    wire [2:0] b = data_i[5:3];
    wire [2:0] lo = (a <= b) ? a : b;
    wire [2:0] hi = (a <= b) ? b : a;
    assign data_o = {hi, lo};
endmodule
