module diag_sort (
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
    
    // Power-on reset
    reg [7:0] por_count = 0;
    wire por_done = (por_count == 8'hFF);
    always @(posedge clk_27) begin
        if (!por_done) por_count <= por_count + 1;
    end
    
    reg [TB-1:0] lfsr;
    wire lfsr_fb = lfsr[63] ^ lfsr[62] ^ lfsr[60] ^ lfsr[59];
    reg valid_i;
    wire valid_o;
    wire [TB-1:0] sorted;
    reg fail;
    reg [31:0] pass_count;
    
    sorting_network_n16 #(.W(W)) dut (
        .clk(clk_27), .rst_n(por_done),
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
        if (!por_done) begin
            lfsr <= 64'hDEADBEEFCAFEBABE;
            valid_i <= 0;
            fail <= 0;
            pass_count <= 0;
        end else begin
            valid_i <= 1;
            lfsr <= {lfsr[TB-2:0], lfsr_fb};
            
            if (valid_o) begin
                if (viol != 0)
                    fail <= 1;
                else
                    pass_count <= pass_count + 1;
            end
        end
    end
    
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    
    // Active-low: 0=ON, 1=OFF
    assign led0 = ~blink[24];                          // heartbeat
    assign led1 = ~por_done;                            // ON = POR complete
    assign led2 = ~(pass_count > 0);                    // ON = passes happening
    assign led3 = fail;                                 // ON = no fail (0=ON), OFF = fail
    assign led4 = ~(pass_count > 32'd1000000);          // ON = million+ passes
    assign led5 = ~lfsr[0];                             // data flowing
endmodule
