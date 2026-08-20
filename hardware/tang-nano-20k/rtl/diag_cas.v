module diag_cas (
    input  wire clk_27,
    output wire led0,
    output wire led1,
    output wire led2,
    output wire led3,
    output wire led4,
    output wire led5
);
    parameter W = 4;
    
    // Power-on reset — count up, hold reset until counter saturates
    reg [7:0] por_count = 0;
    wire por_done = (por_count == 8'hFF);
    always @(posedge clk_27) begin
        if (!por_done) por_count <= por_count + 1;
    end
    
    reg [7:0] lfsr;
    wire lfsr_fb = lfsr[7] ^ lfsr[5] ^ lfsr[4] ^ lfsr[3];
    wire [W-1:0] a = lfsr[W-1:0];
    wire [W-1:0] b = lfsr[2*W-1:W];
    
    reg [W-1:0] lo, hi;
    reg valid = 0;
    reg fail;
    reg [31:0] pass_count;
    
    always @(posedge clk_27) begin
        if (!por_done) begin
            // Explicit reset
            lfsr <= 8'hAB;
            lo <= 0;
            hi <= 0;
            valid <= 0;
            fail <= 0;
            pass_count <= 0;
        end else begin
            lfsr <= {lfsr[6:0], lfsr_fb};
            
            if (a <= b) begin
                lo <= a;
                hi <= b;
            end else begin
                lo <= b;
                hi <= a;
            end
            valid <= 1;
            
            if (valid) begin
                if (lo > hi)
                    fail <= 1;
                else
                    pass_count <= pass_count + 1;
            end
        end
    end
    
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    
    assign led0 = ~blink[24];
    assign led1 = ~valid;
    assign led2 = ~(pass_count > 0);
    assign led3 = fail;              // OFF = no fail, ON = fail
    assign led4 = ~(pass_count > 32'd1000000);
    assign led5 = ~lfsr[0];
endmodule
