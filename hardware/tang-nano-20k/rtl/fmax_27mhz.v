module fmax_27mhz (
    input  wire clk_27,
    output wire led0,
    output wire led1,
    output wire led2,
    output wire led3,
    output wire led4,
    output wire led5
);
    parameter W = 4;
    localparam N = 16;
    localparam TB = N * W;
    
    reg [TB-1:0] lfsr = 64'hDEADBEEFCAFEBABE;
    wire lfsr_fb = lfsr[63] ^ lfsr[62] ^ lfsr[60] ^ lfsr[59];
    reg valid_i = 0;
    wire valid_o;
    wire [TB-1:0] sorted;
    reg [7:0] startup = 0;
    reg fail = 0;
    reg [31:0] pass_count = 0;
    
    sorting_network_n16 #(.W(W)) dut (
        .clk(clk_27), .rst_n(1'b1),
        .valid_i(valid_i), .data_i(lfsr),
        .valid_o(valid_o), .data_o(sorted)
    );
    
    wire [N-2:0] viol;
    genvar gi;
    generate
        for (gi = 0; gi < N-1; gi = gi + 1) begin : chk
            assign viol[gi] = sorted[gi*W +: W] > sorted[(gi+1)*W +: W];
        end
    endgenerate
    
    always @(posedge clk_27) begin
        if (startup < 20) startup <= startup + 1;
        else begin
            valid_i <= 1;
            lfsr <= {lfsr[TB-2:0], lfsr_fb};
        end
        if (valid_o) begin
            if (viol != 0) fail <= 1;
            pass_count <= pass_count + 1;
        end
    end
    
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    
    assign led0 = ~blink[24];
    assign led1 = 1'b0;                              // ON (reference)
    assign led2 = fail ? 1'b1 : ~blink[22];
    assign led3 = ~pass_count[20];
    assign led4 = ~(fail);
    assign led5 = 1'b1;
endmodule
