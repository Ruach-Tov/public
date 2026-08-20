// WHT of 1-bit sorting network — minimal
// At W=1: values are 0/1. Sort = count-sort (zeros first, ones last).
// WHT coefficient k = sum_i (-1)^popcount(i&k) * x[i]
// For binary x[i], this is just: (count of x[i]=1 where Walsh=+1) - (count where Walsh=-1)
module wht_lite (
    input  wire clk_27,
    output wire led0, led1, led2, led3, led4, led5
);
    localparam N = 16;
    
    reg [7:0] por = 0;
    wire por_done = (por == 8'hFF);
    always @(posedge clk_27) if (!por_done) por <= por + 1;
    
    // LFSR — 16 bits for 16 binary inputs
    reg [15:0] lfsr = 16'hCAFE;
    wire lfsr_fb = lfsr[15] ^ lfsr[14] ^ lfsr[12] ^ lfsr[3];
    
    reg valid_i = 0;
    wire valid_o;
    wire [N-1:0] sorted;
    
    sorting_network_n16 #(.W(1)) sorter (
        .clk(clk_27), .rst_n(por_done),
        .valid_i(valid_i), .data_i(lfsr),
        .valid_o(valid_o), .data_o(sorted)
    );
    
    always @(posedge clk_27) begin
        if (por_done) begin
            valid_i <= 1;
            lfsr <= {lfsr[14:0], lfsr_fb};
        end
    end
    
    // WHT sequency 1: Walsh W_1(i) = (-1)^i[0]
    // For raw: count 1s at even positions - count 1s at odd positions
    // For sorted: same but on sorted output
    wire signed [4:0] raw_seq1 = 
        $signed({1'b0, lfsr[0]}) - $signed({1'b0, lfsr[1]}) +
        $signed({1'b0, lfsr[2]}) - $signed({1'b0, lfsr[3]}) +
        $signed({1'b0, lfsr[4]}) - $signed({1'b0, lfsr[5]}) +
        $signed({1'b0, lfsr[6]}) - $signed({1'b0, lfsr[7]}) +
        $signed({1'b0, lfsr[8]}) - $signed({1'b0, lfsr[9]}) +
        $signed({1'b0, lfsr[10]}) - $signed({1'b0, lfsr[11]}) +
        $signed({1'b0, lfsr[12]}) - $signed({1'b0, lfsr[13]}) +
        $signed({1'b0, lfsr[14]}) - $signed({1'b0, lfsr[15]});
    
    wire signed [4:0] sort_seq1 = 
        $signed({1'b0, sorted[0]}) - $signed({1'b0, sorted[1]}) +
        $signed({1'b0, sorted[2]}) - $signed({1'b0, sorted[3]}) +
        $signed({1'b0, sorted[4]}) - $signed({1'b0, sorted[5]}) +
        $signed({1'b0, sorted[6]}) - $signed({1'b0, sorted[7]}) +
        $signed({1'b0, sorted[8]}) - $signed({1'b0, sorted[9]}) +
        $signed({1'b0, sorted[10]}) - $signed({1'b0, sorted[11]}) +
        $signed({1'b0, sorted[12]}) - $signed({1'b0, sorted[13]}) +
        $signed({1'b0, sorted[14]}) - $signed({1'b0, sorted[15]});
    
    // Sequency 8: (-1)^i[3] — first 8 minus last 8
    wire signed [4:0] sort_seq8 = 
        $signed({1'b0, sorted[0]}) + $signed({1'b0, sorted[1]}) +
        $signed({1'b0, sorted[2]}) + $signed({1'b0, sorted[3]}) +
        $signed({1'b0, sorted[4]}) + $signed({1'b0, sorted[5]}) +
        $signed({1'b0, sorted[6]}) + $signed({1'b0, sorted[7]}) -
        $signed({1'b0, sorted[8]}) - $signed({1'b0, sorted[9]}) -
        $signed({1'b0, sorted[10]}) - $signed({1'b0, sorted[11]}) -
        $signed({1'b0, sorted[12]}) - $signed({1'b0, sorted[13]}) -
        $signed({1'b0, sorted[14]}) - $signed({1'b0, sorted[15]});
    
    // Accumulate |coefficients| over 2^18 samples
    reg [31:0] acc_raw1 = 0, acc_sort1 = 0, acc_sort8 = 0;
    reg [31:0] cnt = 0;
    reg done = 0;
    
    wire [4:0] abs_raw1  = raw_seq1[4]  ? -raw_seq1  : raw_seq1;
    wire [4:0] abs_sort1 = sort_seq1[4] ? -sort_seq1 : sort_seq1;
    wire [4:0] abs_sort8 = sort_seq8[4] ? -sort_seq8 : sort_seq8;
    
    always @(posedge clk_27) begin
        if (valid_o && !done) begin
            cnt <= cnt + 1;
            acc_raw1  <= acc_raw1  + abs_raw1;
            acc_sort1 <= acc_sort1 + abs_sort1;
            acc_sort8 <= acc_sort8 + abs_sort8;
            if (cnt >= 32'h40000) done <= 1;
        end
    end
    
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    
    // Active-low
    assign led0 = ~blink[24];                              // heartbeat
    assign led1 = ~done;                                    // accumulation done
    assign led2 = ~(acc_sort1 > acc_raw1);                  // sort increased seq1?
    assign led3 = ~(acc_sort8 > acc_sort1);                 // seq8 > seq1 after sort?
    assign led4 = ~(acc_sort8 > acc_raw1);                  // seq8(sorted) > seq1(raw)?
    assign led5 = ~(sort_seq8 < 0);                         // live: seq8 sign (always ≤0 after sort!)
endmodule
