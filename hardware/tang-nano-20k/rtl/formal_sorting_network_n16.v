// =============================================================================
// Formal verification wrapper for sorting_network_n16
//
// Proves for ALL possible inputs:
//   1. When valid_o, output is SORTED (out[i] ≤ out[i+1] for all i)
//
// Usage: sby formal_sorting_network_n16.sby
// =============================================================================

module formal_sorting_network_n16 #(
    parameter W = 8
) (
    input  wire             clk,
    input  wire             rst_n,
    input  wire             valid_i,
    input  wire [16*W-1:0]  data_i,
    output wire             valid_o,
    output wire [16*W-1:0]  data_o
);

    sorting_network_n16 #(.W(W)) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_i(valid_i), .data_i(data_i),
        .valid_o(valid_o), .data_o(data_o)
    );

`ifdef FORMAL

    reg past_valid = 0;
    always @(posedge clk) past_valid <= 1;

    // Reset discipline: released after first cycle
    initial assume(!rst_n);
    always @(posedge clk)
        if (past_valid) assume(rst_n);

    // Extract output elements
    wire [W-1:0] out [0:15];
    genvar g;
    generate
        for (g = 0; g < 16; g = g + 1) begin : unpack
            assign out[g] = data_o[g*W +: W];
        end
    endgenerate

    // PROPERTY: output is SORTED when valid
    generate
        for (g = 0; g < 15; g = g + 1) begin : sorted_check
            always @(posedge clk)
                if (past_valid && valid_o)
                    assert(out[g] <= out[g+1]);
        end
    endgenerate

`endif

endmodule
