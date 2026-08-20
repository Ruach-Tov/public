// Fixed-frequency dual sort test
// PLL generates a specific frequency, both networks sort, checker verifies
module fmax_test (
    input  wire clk_27,
    output wire led0,    // heartbeat
    output wire led1,    // net01 passing
    output wire led2,    // dobb passing
    output wire led3,    // both agree
    output wire led4,    // pass count bit (fast blink = running)
    output wire led5     // any fail
);
    parameter W = 4;
    parameter FBDIV = 3;  // PLL multiplier: freq = 27 * (FBDIV+1) / 2
    
    localparam N = 16;
    localparam TOTAL_BITS = N * W;
    
    wire fast_clk, pll_locked;
    
    rPLL #(
        .FCLKIN("27.0"),
        .IDIV_SEL(0),
        .FBDIV_SEL(FBDIV),
        .ODIV_SEL(2)
    ) pll (
        .CLKOUTP(), .CLKOUTD(), .CLKOUTD3(),
        .RESET(1'b0), .RESET_P(1'b0), .CLKFB(1'b0),
        .FBDSEL(6'b0), .IDSEL(6'b0), .ODSEL(6'b0),
        .PSDA(4'b0), .DUTYDA(4'b0), .FDLY(4'b0),
        .CLKIN(clk_27),
        .CLKOUT(fast_clk),
        .LOCK(pll_locked)
    );
    
    reg [TOTAL_BITS-1:0] lfsr = 64'hDEADBEEFCAFEBABE;
    wire lfsr_fb = lfsr[63] ^ lfsr[62] ^ lfsr[60] ^ lfsr[59];
    
    reg valid_i = 0;
    wire valid_o_01, valid_o_dobb;
    wire [TOTAL_BITS-1:0] sorted_01, sorted_dobb;
    reg [7:0] startup = 0;
    
    sorting_network_n16 #(.W(W)) net01 (
        .clk(fast_clk), .rst_n(pll_locked),
        .valid_i(valid_i), .data_i(lfsr),
        .valid_o(valid_o_01), .data_o(sorted_01)
    );
    
    dobbelaere_n16 #(.W(W)) dobb (
        .clk(fast_clk), .rst_n(pll_locked),
        .valid_i(valid_i), .data_i(lfsr),
        .valid_o(valid_o_dobb), .data_o(sorted_dobb)
    );
    
    wire [N-2:0] viol_01, viol_dobb;
    genvar gi;
    generate
        for (gi = 0; gi < N-1; gi = gi + 1) begin : chk
            assign viol_01[gi] = sorted_01[gi*W +: W] > sorted_01[(gi+1)*W +: W];
            assign viol_dobb[gi] = sorted_dobb[gi*W +: W] > sorted_dobb[(gi+1)*W +: W];
        end
    endgenerate
    
    reg fail_01 = 0, fail_dobb = 0, mismatch_flag = 0;
    reg [31:0] pass_count = 0;
    
    always @(posedge fast_clk or negedge pll_locked) begin
        if (!pll_locked) begin
            lfsr <= 64'hDEADBEEFCAFEBABE;
            valid_i <= 0;
            fail_01 <= 0; fail_dobb <= 0; mismatch_flag <= 0;
            pass_count <= 0; startup <= 0;
        end else begin
            if (startup < 20) begin
                startup <= startup + 1;
            end else begin
                valid_i <= 1;
                lfsr <= {lfsr[TOTAL_BITS-2:0], lfsr_fb};
            end
            
            if (valid_o_01) begin
                if (viol_01 != 0) fail_01 <= 1;
                if (viol_dobb != 0) fail_dobb <= 1;
                if (sorted_01 != sorted_dobb) mismatch_flag <= 1;
                pass_count <= pass_count + 1;
            end
        end
    end
    
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    
    assign led0 = blink[24];
    assign led1 = fail_01 ? 1'b0 : blink[22];
    assign led2 = fail_dobb ? 1'b0 : blink[22];
    assign led3 = mismatch_flag ? 1'b0 : blink[21];
    assign led4 = pass_count[20];
    assign led5 = (fail_01 | fail_dobb) ? blink[23] : 1'b0;
endmodule
