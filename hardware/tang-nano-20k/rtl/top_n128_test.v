module top_n128_test (
    input  wire clk,
    output wire led0,
    output wire led1,
    output wire led2,
    output wire led3,
    output wire led4,
    output wire led5
);
    parameter W = 1;
    localparam N = 128;
    
    reg [127:0] lfsr = 128'hDEADBEEFCAFEBABE0123456789ABCDEF;
    wire lfsr_feedback = lfsr[127] ^ lfsr[125] ^ lfsr[100] ^ lfsr[98];
    
    reg valid_i = 0;
    wire valid_o;
    wire [N*W-1:0] sorted;
    reg [31:0] pass_count = 0;
    reg fail_flag = 0;
    reg [7:0] startup = 0;
    reg [24:0] blink = 0;
    
    sorting_network_n128 #(.W(W)) dut (
        .clk(clk), .rst_n(1'b1),
        .valid_i(valid_i), .data_i(lfsr),
        .valid_o(valid_o), .data_o(sorted)
    );
    
    wire [N-2:0] violations;
    genvar gi;
    generate
        for (gi = 0; gi < N-1; gi = gi + 1) begin : chk
            assign violations[gi] = sorted[gi] & ~sorted[gi+1];
        end
    endgenerate
    
    wire is_sorted = (violations == 0);
    
    always @(posedge clk) begin
        blink <= blink + 1;
        
        if (startup < 8'd40) begin
            startup <= startup + 1;
            valid_i <= 0;
        end else begin
            valid_i <= 1;
            lfsr <= {lfsr[126:0], lfsr_feedback};
        end
        
        if (valid_o) begin
            if (is_sorted)
                pass_count <= pass_count + 1;
            else
                fail_flag <= 1;
        end
    end
    
    // 6 LEDs show status:
    // led0: heartbeat (always blinks = design is running)
    // led1: valid_o is producing outputs
    // led2: pass_count > 0 (at least one sort completed)
    // led3: pass_count[20] (blinks fast if many passes)
    // led4: FAIL flag (steady ON if any failure detected)
    // led5: ALL GOOD (steady ON if passing, no fail)
    
    assign led0 = blink[24];                           // heartbeat ~1Hz
    assign led1 = blink[23] & valid_o;                 // outputs flowing
    assign led2 = (pass_count > 0) ? blink[22] : 1'b1; // passes happening
    assign led3 = pass_count[20];                       // fast blink = many sorts
    assign led4 = fail_flag;                            // FAIL indicator
    assign led5 = ~fail_flag & (pass_count > 0);       // ALL GOOD
endmodule
