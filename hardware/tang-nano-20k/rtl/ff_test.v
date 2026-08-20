module ff_test (
    input  wire clk_27,
    output wire led0,
    output wire led1,
    output wire led2,
    output wire led3,
    output wire led4,
    output wire led5
);
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    
    // Test A: FF with Verilog initial = 0, no reset
    reg ff_init0 = 1'b0;
    // Don't ever write to it — just read power-up value
    
    // Test B: FF with Verilog initial = 1, no reset
    reg ff_init1 = 1'b1;
    
    // Test C: FF with no initial value (undefined)
    reg ff_noinit;
    
    // Test D: FF explicitly reset by POR counter
    reg [7:0] por = 0;
    wire por_done = (por == 8'hFF);
    reg ff_reset;
    always @(posedge clk_27) begin
        if (!por_done) begin
            por <= por + 1;
            ff_reset <= 0;
        end
    end
    
    assign led0 = ~blink[24];     // heartbeat
    assign led1 = ff_init0;       // ON(0) if FF inits to 0, OFF(1) if inits to 1
    assign led2 = ff_init1;       // OFF(1) if FF inits to 1, ON(0) if inits to 0
    assign led3 = ff_noinit;      // unknown — what does it power up as?
    assign led4 = ff_reset;       // ON(0) after POR clears it
    assign led5 = 1'b1;           // off
endmodule
