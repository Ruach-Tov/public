module fmax_uart (
    input  wire clk_27,
    output wire uart_tx,
    output wire led0,
    output wire led3
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
    
    reg lock_sync1 = 0, lock_sync2 = 0;
    always @(posedge fast_clk) begin
        lock_sync1 <= pll_locked;
        lock_sync2 <= lock_sync1;
    end
    
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
    
    // Simple UART TX at 115200 from 27 MHz domain
    // 27000000 / 115200 = 234.375 ≈ 234
    localparam BAUD_DIV = 234;
    
    reg [7:0] tx_data;
    reg [3:0] tx_bit = 0;
    reg [7:0] baud_count = 0;
    reg tx_busy = 0;
    reg tx_out = 1;
    reg [24:0] report_timer = 0;
    reg report_trigger = 0;
    reg [2:0] report_state = 0;
    
    // Report every ~0.5 seconds: "P" for pass, "F" for fail, then newline
    always @(posedge clk_27) begin
        report_timer <= report_timer + 1;
        
        if (report_timer == 0) begin
            report_trigger <= 1;
            report_state <= 0;
        end
        
        if (report_trigger && !tx_busy) begin
            case (report_state)
                0: begin tx_data <= fail ? "F" : "P"; tx_busy <= 1; report_state <= 1; end
                1: begin tx_data <= 8'h0A; tx_busy <= 1; report_state <= 2; end  // newline
                2: begin report_trigger <= 0; end
            endcase
        end
        
        if (tx_busy) begin
            if (baud_count < BAUD_DIV - 1) begin
                baud_count <= baud_count + 1;
            end else begin
                baud_count <= 0;
                case (tx_bit)
                    0: begin tx_out <= 0; tx_bit <= 1; end  // start bit
                    1: begin tx_out <= tx_data[0]; tx_bit <= 2; end
                    2: begin tx_out <= tx_data[1]; tx_bit <= 3; end
                    3: begin tx_out <= tx_data[2]; tx_bit <= 4; end
                    4: begin tx_out <= tx_data[3]; tx_bit <= 5; end
                    5: begin tx_out <= tx_data[4]; tx_bit <= 6; end
                    6: begin tx_out <= tx_data[5]; tx_bit <= 7; end
                    7: begin tx_out <= tx_data[6]; tx_bit <= 8; end
                    8: begin tx_out <= tx_data[7]; tx_bit <= 9; end
                    9: begin tx_out <= 1; tx_bit <= 0; tx_busy <= 0; end  // stop bit
                endcase
            end
        end
    end
    
    assign uart_tx = tx_out;
    
    reg [24:0] blink = 0;
    always @(posedge clk_27) blink <= blink + 1;
    assign led0 = ~blink[24];
    assign led3 = fail;
endmodule
