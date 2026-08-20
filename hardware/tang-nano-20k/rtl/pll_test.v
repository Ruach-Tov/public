module pll_test (
    input  wire clk_27,
    output wire led0,
    output wire led1,
    output wire led2,
    output wire led3,
    output wire led4,
    output wire led5
);
    wire fast_clk, pll_locked;
    
    // Target: 270 MHz
    // CLKOUT = 27 * (9+1) / (0+1) = 270 MHz
    // VCO = 270 * 4 = 1080 MHz (600-1200 range ✓)
    rPLL #(
        .FCLKIN("27.0"),
        .IDIV_SEL(0),
        .FBDIV_SEL(9),
        .ODIV_SEL(4)
    ) pll (
        .CLKOUTP(), .CLKOUTD(), .CLKOUTD3(),
        .RESET(1'b0), .RESET_P(1'b0), .CLKFB(1'b0),
        .FBDSEL(6'b0), .IDSEL(6'b0), .ODSEL(6'b0),
        .PSDA(4'b0), .DUTYDA(4'b0), .FDLY(4'b0),
        .CLKIN(clk_27),
        .CLKOUT(fast_clk),
        .LOCK(pll_locked)
    );
    
    reg [24:0] slow_blink = 0;
    always @(posedge clk_27) slow_blink <= slow_blink + 1;
    
    reg [24:0] fast_blink = 0;
    always @(posedge fast_clk) fast_blink <= fast_blink + 1;
    
    assign led0 = ~slow_blink[24];   // ~0.8 Hz from 27 MHz
    assign led1 = ~pll_locked;       // ON if PLL locked
    assign led2 = ~fast_blink[24];   // 270M/2^25 = 8 Hz (fast flicker)
    assign led3 = ~fast_blink[20];   // 270M/2^21 = 129 Hz (solid dim)
    assign led4 = 1'b1;
    assign led5 = 1'b1;
endmodule
