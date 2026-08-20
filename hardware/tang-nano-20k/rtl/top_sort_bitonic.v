module top_sort_bitonic (
    input  wire clk,
    input  wire rst_n,
    input  wire serial_in,
    output wire serial_out
);
    parameter W = 4;
    localparam TOTAL_BITS = 16 * W;
    
    reg [TOTAL_BITS-1:0] shift_in;
    reg [TOTAL_BITS-1:0] shift_out;
    reg valid_i;
    wire valid_o;
    wire [TOTAL_BITS-1:0] sorted;
    reg [$clog2(TOTAL_BITS+1)-1:0] bit_count;
    
    bitonic_sort_n16 #(.W(W)) sorter (
        .clk(clk), .rst_n(rst_n),
        .valid_i(valid_i), .data_i(shift_in),
        .valid_o(valid_o), .data_o(sorted)
    );
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            shift_in <= 0;
            shift_out <= 0;
            valid_i <= 0;
            bit_count <= 0;
        end else begin
            shift_in <= {shift_in[TOTAL_BITS-2:0], serial_in};
            bit_count <= bit_count + 1;
            valid_i <= (bit_count == TOTAL_BITS - 1);
            if (valid_o)
                shift_out <= sorted;
            else
                shift_out <= {shift_out[TOTAL_BITS-2:0], 1'b0};
        end
    end
    
    assign serial_out = shift_out[TOTAL_BITS-1];
endmodule
