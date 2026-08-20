// Fmax sweep: dual sorting networks at PLL-multiplied clock
// Button cycles through frequencies. LEDs show pass/fail.
module fmax_sweep (
    input  wire clk_27,     // 27 MHz crystal, pin 4
    input  wire btn_step,   // Button S1 pin 87 — step to next frequency
    input  wire btn_reset,  // Button S2 pin 88 — reset
    output wire led0,       // heartbeat at PLL clock
    output wire led1,       // Network 01 passing
    output wire led2,       // Dobbelaere passing  
    output wire led3,       // MISMATCH detected
    output wire led4,       // frequency bit 0
    output wire led5        // frequency bit 1
);
    parameter W = 4;
    localparam N = 16;
    localparam TOTAL_BITS = N * W;
    
    // PLL — start at 2x (54 MHz), step up via FBDIV
    // For simplicity, generate a fixed high frequency and use a clock divider
    wire pll_clk, pll_locked;
    
    rPLL #(
        .FCLKIN("27.0"),
        .IDIV_SEL(0),
        .FBDIV_SEL(21),  // 594 MHz
        .ODIV_SEL(2)     // VCO / 2 = 594 MHz
    ) pll (
        .CLKOUTP(), .CLKOUTD(), .CLKOUTD3(),
        .RESET(1'b0), .RESET_P(1'b0), .CLKFB(1'b0),
        .FBDSEL(6'b0), .IDSEL(6'b0), .ODSEL(6'b0),
        .PSDA(4'b0), .DUTYDA(4'b0), .FDLY(4'b0),
        .CLKIN(clk_27),
        .CLKOUT(pll_clk),
        .LOCK(pll_locked)
    );
    
    // Clock divider: divide pll_clk by 1,2,4,8 selectable
    reg [2:0] div_select = 0;  // 0=594, 1=297, 2=148, 3=74 MHz
    reg [7:0] div_counter = 0;
    reg test_clk = 0;
    
    always @(posedge pll_clk) begin
        if (div_counter >= (1 << div_select) - 1) begin
            div_counter <= 0;
            test_clk <= ~test_clk;
        end else begin
            div_counter <= div_counter + 1;
        end
    end
    
    // Button debounce for stepping
    reg [19:0] debounce = 0;
    reg btn_prev = 1;
    always @(posedge clk_27) begin
        debounce <= debounce + 1;
        if (debounce == 0) begin
            if (btn_prev && !btn_step) begin
                div_select <= div_select + 1;
            end
            btn_prev <= btn_step;
        end
    end
    
    // LFSR for test data (runs at test_clk)
    reg [TOTAL_BITS-1:0] lfsr = 64'hDEADBEEFCAFEBABE;
    wire lfsr_fb = lfsr[63] ^ lfsr[62] ^ lfsr[60] ^ lfsr[59];
    
    reg valid_i = 0;
    wire valid_o_01, valid_o_dobb;
    wire [TOTAL_BITS-1:0] sorted_01, sorted_dobb;
    reg [7:0] startup = 0;
    
    // Network 01
    sorting_network_n16 #(.W(W)) net01 (
        .clk(test_clk), .rst_n(pll_locked),
        .valid_i(valid_i), .data_i(lfsr),
        .valid_o(valid_o_01), .data_o(sorted_01)
    );
    
    // Dobbelaere
    dobbelaere_n16 #(.W(W)) dobb (
        .clk(test_clk), .rst_n(pll_locked),
        .valid_i(valid_i), .data_i(lfsr),
        .valid_o(valid_o_dobb), .data_o(sorted_dobb)
    );
    
    // Check sorted
    wire [N-2:0] viol_01, viol_dobb;
    genvar gi;
    generate
        for (gi = 0; gi < N-1; gi = gi + 1) begin : chk
            assign viol_01[gi] = sorted_01[gi*W +: W] > sorted_01[(gi+1)*W +: W];
            assign viol_dobb[gi] = sorted_dobb[gi*W +: W] > sorted_dobb[(gi+1)*W +: W];
        end
    endgenerate
    
    wire ok_01 = (viol_01 == 0);
    wire ok_dobb = (viol_dobb == 0);
    wire mismatch = (sorted_01 != sorted_dobb);
    
    reg fail_01 = 0;
    reg fail_dobb = 0;
    reg mismatch_flag = 0;
    reg [31:0] pass_count = 0;
    
    always @(posedge test_clk or negedge pll_locked) begin
        if (!pll_locked) begin
            lfsr <= 64'hDEADBEEFCAFEBABE;
            valid_i <= 0;
            fail_01 <= 0;
            fail_dobb <= 0;
            mismatch_flag <= 0;
            pass_count <= 0;
            startup <= 0;
        end else begin
            if (startup < 20) begin
                startup <= startup + 1;
                valid_i <= 0;
            end else begin
                valid_i <= 1;
                lfsr <= {lfsr[TOTAL_BITS-2:0], lfsr_fb};
            end
            
            if (valid_o_01) begin
                if (!ok_01) fail_01 <= 1;
                if (!ok_dobb) fail_dobb <= 1;
                if (mismatch) mismatch_flag <= 1;
                pass_count <= pass_count + 1;
            end
        end
    end
    
    // LED display
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    
    assign led0 = blink[24];                              // heartbeat
    assign led1 = fail_01 ? 1'b1 : blink[22];            // net01: blink=pass, off=fail
    assign led2 = fail_dobb ? 1'b1 : blink[22];          // dobb: blink=pass, off=fail
    assign led3 = ~mismatch_flag;                          // ON if no mismatch
    assign led4 = div_select[0];                           // freq bit 0
    assign led5 = div_select[1];                           // freq bit 1
endmodule
