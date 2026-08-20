module fmax_single (
    input  wire clk_27,
    output wire led0,
    output wire led1,
    output wire led2,
    output wire led3,
    output wire led4,
    output wire led5
);
    parameter W = 4;
    parameter FBDIV = 9;
    parameter ODIV = 4;
    parameter IDIV = 0;
    parameter USE_DOBB = 0;
    
    localparam N = 16;
    localparam TB = N * W;
    
    wire fast_clk, pll_locked;
    rPLL #(
        .FCLKIN("27.0"), .IDIV_SEL(IDIV),
        .FBDIV_SEL(FBDIV), .ODIV_SEL(ODIV)
    ) pll (
        .CLKOUTP(), .CLKOUTD(), .CLKOUTD3(),
        .RESET(1'b0), .RESET_P(1'b0), .CLKFB(1'b0),
        .FBDSEL(6'b0), .IDSEL(6'b0), .ODSEL(6'b0),
        .PSDA(4'b0), .DUTYDA(4'b0), .FDLY(4'b0),
        .CLKIN(clk_27), .CLKOUT(fast_clk), .LOCK(pll_locked)
    );
    
    // Synchronize pll_locked into fast_clk domain
    reg lock_sync1 = 0, lock_sync2 = 0;
    always @(posedge fast_clk) begin
        lock_sync1 <= pll_locked;
        lock_sync2 <= lock_sync1;
    end
    
    // POR counter in fast_clk domain — starts after lock stabilizes
    reg [9:0] por_count = 0;
    wire por_done = (por_count == 10'h3FF);
    always @(posedge fast_clk) begin
        if (!lock_sync2) por_count <= 0;
        else if (!por_done) por_count <= por_count + 1;
    end
    
    reg [TB-1:0] lfsr;
    wire lfsr_fb = lfsr[63] ^ lfsr[62] ^ lfsr[60] ^ lfsr[59];
    reg valid_i;
    wire valid_o;
    wire [TB-1:0] sorted;
    reg fail;
    reg [31:0] pass_count;
    
    generate
        if (USE_DOBB == 0) begin : use_net01
            sorting_network_n16 #(.W(W)) dut (
                .clk(fast_clk), .rst_n(por_done),
                .valid_i(valid_i), .data_i(lfsr),
                .valid_o(valid_o), .data_o(sorted)
            );
        end else begin : use_dobb
            dobbelaere_n16 #(.W(W)) dut (
                .clk(fast_clk), .rst_n(por_done),
                .valid_i(valid_i), .data_i(lfsr),
                .valid_o(valid_o), .data_o(sorted)
            );
        end
    endgenerate
    
    wire [N-2:0] viol;
    genvar gi;
    generate
        for (gi = 0; gi < N-1; gi = gi + 1) begin : chk
            assign viol[gi] = sorted[gi*W +: W] > sorted[(gi+1)*W +: W];
        end
    endgenerate
    
    // All synchronous to fast_clk, no async reset on data path
    always @(posedge fast_clk) begin
        if (!por_done) begin
            lfsr <= 64'hDEADBEEFCAFEBABE;
            valid_i <= 0; fail <= 0; pass_count <= 0;
        end else begin
            valid_i <= 1;
            lfsr <= {lfsr[TB-2:0], lfsr_fb};
            if (valid_o) begin
                if (viol != 0) fail <= 1;
                else pass_count <= pass_count + 1;
            end
        end
    end
    
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    
    // Active-low LEDs
    assign led0 = ~blink[24];              // heartbeat
    assign led1 = ~lock_sync2;             // ON = PLL locked (synced)
    assign led2 = ~(pass_count > 0);       // ON = passes
    assign led3 = fail;                    // ON = no fail, OFF = fail
    assign led4 = ~(pass_count > 32'd1000000);
    assign led5 = ~lfsr[0];
endmodule
