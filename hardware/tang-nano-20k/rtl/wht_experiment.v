// Walsh-Hadamard Transform of LFSR output
// 16-point WHT on 4-bit values
// Compare: raw LFSR spectrum vs post-sort spectrum
module wht_experiment (
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
    
    // LFSR
    reg [TB-1:0] lfsr = 64'hDEADBEEFCAFEBABE;
    wire lfsr_fb = lfsr[63] ^ lfsr[62] ^ lfsr[60] ^ lfsr[59];
    
    // Sorting network
    reg valid_i = 0;
    wire valid_o;
    wire [TB-1:0] sorted;
    reg [7:0] startup = 0;
    
    sorting_network_n16 #(.W(W)) sorter (
        .clk(clk_27), .rst_n(1'b1),
        .valid_i(valid_i), .data_i(lfsr),
        .valid_o(valid_o), .data_o(sorted)
    );
    
    // POR
    reg [7:0] por = 0;
    wire por_done = (por == 8'hFF);
    always @(posedge clk_27) begin
        if (!por_done) por <= por + 1;
    end
    
    always @(posedge clk_27) begin
        if (por_done) begin
            valid_i <= 1;
            lfsr <= {lfsr[TB-2:0], lfsr_fb};
        end
    end
    
    // =========================================================
    // 16-point Walsh-Hadamard Transform (in-place butterfly)
    // Input: 16 signed values (sign-extend W-bit unsigned to W+4 bits)
    // 4 stages of butterflies: stride 1, 2, 4, 8
    // =========================================================
    
    localparam SW = W + 5;  // signed width: enough for 4 stages of addition
    
    // Stage 0: sign-extend input values
    reg signed [SW-1:0] wht_raw [0:N-1];   // WHT of raw LFSR
    reg signed [SW-1:0] wht_sort [0:N-1];  // WHT of sorted output
    
    // Butterfly: a,b → a+b, a-b
    // Stage 1: stride 1 (pairs 0-1, 2-3, 4-5, ...)
    reg signed [SW-1:0] s1_raw [0:N-1];
    reg signed [SW-1:0] s1_sort [0:N-1];
    // Stage 2: stride 2
    reg signed [SW-1:0] s2_raw [0:N-1];
    reg signed [SW-1:0] s2_sort [0:N-1];
    // Stage 3: stride 4
    reg signed [SW-1:0] s3_raw [0:N-1];
    reg signed [SW-1:0] s3_sort [0:N-1];
    // Stage 4: stride 8 — final
    reg signed [SW-1:0] s4_raw [0:N-1];
    reg signed [SW-1:0] s4_sort [0:N-1];
    
    integer i;
    
    always @(posedge clk_27) begin
        if (valid_o) begin
            // Load inputs (sign-extend unsigned to signed)
            for (i = 0; i < N; i = i + 1) begin
                wht_raw[i]  <= $signed({1'b0, lfsr[i*W +: W]});
                wht_sort[i] <= $signed({1'b0, sorted[i*W +: W]});
            end
            
            // Stage 1: stride 1 butterflies
            for (i = 0; i < N; i = i + 2) begin
                s1_raw[i]   <= wht_raw[i] + wht_raw[i+1];
                s1_raw[i+1] <= wht_raw[i] - wht_raw[i+1];
                s1_sort[i]   <= wht_sort[i] + wht_sort[i+1];
                s1_sort[i+1] <= wht_sort[i] - wht_sort[i+1];
            end
            
            // Stage 2: stride 2 butterflies
            for (i = 0; i < N; i = i + 4) begin
                s2_raw[i]   <= s1_raw[i]   + s1_raw[i+2];
                s2_raw[i+1] <= s1_raw[i+1] + s1_raw[i+3];
                s2_raw[i+2] <= s1_raw[i]   - s1_raw[i+2];
                s2_raw[i+3] <= s1_raw[i+1] - s1_raw[i+3];
                s2_sort[i]   <= s1_sort[i]   + s1_sort[i+2];
                s2_sort[i+1] <= s1_sort[i+1] + s1_sort[i+3];
                s2_sort[i+2] <= s1_sort[i]   - s1_sort[i+2];
                s2_sort[i+3] <= s1_sort[i+1] - s1_sort[i+3];
            end
            
            // Stage 3: stride 4 butterflies
            for (i = 0; i < N; i = i + 8) begin
                s3_raw[i]   <= s2_raw[i]   + s2_raw[i+4];
                s3_raw[i+1] <= s2_raw[i+1] + s2_raw[i+5];
                s3_raw[i+2] <= s2_raw[i+2] + s2_raw[i+6];
                s3_raw[i+3] <= s2_raw[i+3] + s2_raw[i+7];
                s3_raw[i+4] <= s2_raw[i]   - s2_raw[i+4];
                s3_raw[i+5] <= s2_raw[i+1] - s2_raw[i+5];
                s3_raw[i+6] <= s2_raw[i+2] - s2_raw[i+6];
                s3_raw[i+7] <= s2_raw[i+3] - s2_raw[i+7];
                s3_sort[i]   <= s2_sort[i]   + s2_sort[i+4];
                s3_sort[i+1] <= s2_sort[i+1] + s2_sort[i+5];
                s3_sort[i+2] <= s2_sort[i+2] + s2_sort[i+6];
                s3_sort[i+3] <= s2_sort[i+3] + s2_sort[i+7];
                s3_sort[i+4] <= s2_sort[i]   - s2_sort[i+4];
                s3_sort[i+5] <= s2_sort[i+1] - s2_sort[i+5];
                s3_sort[i+6] <= s2_sort[i+2] - s2_sort[i+6];
                s3_sort[i+7] <= s2_sort[i+3] - s2_sort[i+7];
            end
            
            // Stage 4: stride 8 butterflies — FINAL
            for (i = 0; i < 8; i = i + 1) begin
                s4_raw[i]   <= s3_raw[i] + s3_raw[i+8];
                s4_raw[i+8] <= s3_raw[i] - s3_raw[i+8];
                s4_sort[i]   <= s3_sort[i] + s3_sort[i+8];
                s4_sort[i+8] <= s3_sort[i] - s3_sort[i+8];
            end
        end
    end
    
    // =========================================================
    // Accumulate |coefficient|^2 over many samples for each 
    // sequency, to see the power spectrum
    // =========================================================
    reg [31:0] power_raw [0:N-1];
    reg [31:0] power_sort [0:N-1];
    reg [31:0] sample_count = 0;
    reg accumulated = 0;
    
    // Accumulate for 2^20 samples then freeze
    always @(posedge clk_27) begin
        if (valid_o && por_done && !accumulated) begin
            sample_count <= sample_count + 1;
            if (sample_count >= 32'h100000) begin
                accumulated <= 1;
            end else begin
                for (i = 0; i < N; i = i + 1) begin
                    if (sample_count == 0) begin
                        power_raw[i]  <= 0;
                        power_sort[i] <= 0;
                    end
                    // Accumulate absolute value (avoid multiply)
                    power_raw[i]  <= power_raw[i]  + (s4_raw[i]  > 0 ? s4_raw[i]  : -s4_raw[i]);
                    power_sort[i] <= power_sort[i] + (s4_sort[i] > 0 ? s4_sort[i] : -s4_sort[i]);
                end
            end
        end
    end
    
    // =========================================================
    // Display: show which sequency has the most power
    // after sorting vs before sorting
    // =========================================================
    reg [3:0] max_raw_seq = 0;
    reg [3:0] max_sort_seq = 0;
    reg [31:0] max_raw_val = 0;
    reg [31:0] max_sort_val = 0;
    
    // Find max (combinational scan)
    integer j;
    always @(*) begin
        max_raw_val = 0; max_raw_seq = 0;
        max_sort_val = 0; max_sort_seq = 0;
        // Skip DC (sequency 0) — it's always dominant
        for (j = 1; j < N; j = j + 1) begin
            if (power_raw[j] > max_raw_val) begin
                max_raw_val = power_raw[j];
                max_raw_seq = j[3:0];
            end
            if (power_sort[j] > max_sort_val) begin
                max_sort_val = power_sort[j];
                max_sort_seq = j[3:0];
            end
        end
    end
    
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    
    // Active-low LEDs:
    // led0: heartbeat
    // led1: accumulated (done collecting)
    // led2-3: peak raw sequency (2 bits)
    // led4-5: peak sorted sequency (2 bits)
    assign led0 = ~blink[24];
    assign led1 = ~accumulated;
    assign led2 = ~max_raw_seq[0];
    assign led3 = ~max_raw_seq[1];
    assign led4 = ~max_sort_seq[0];
    assign led5 = ~max_sort_seq[1];
endmodule
