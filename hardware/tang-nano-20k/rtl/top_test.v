// Test wrapper: sorting network with internal test pattern
// Only exposes clk, rst_n, and a LED showing pass/fail
module top_test (
    input  wire clk,      // 27 MHz on pin 4
    input  wire rst_n,    // Button S2, pin 88
    output wire led_pass  // LED on pin 15 (active low)
);
    parameter W = 4;
    
    reg [16*W-1:0] test_data;
    wire [16*W-1:0] sorted_data;
    reg valid_i;
    wire valid_o;
    reg [15:0] test_count;
    reg all_pass;
    
    sorting_network_n16 #(.W(W)) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_i(valid_i), .data_i(test_data),
        .valid_o(valid_o), .data_o(sorted_data)
    );
    
    // Generate test patterns: all 2^16 binary inputs
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            test_count <= 0;
            valid_i <= 0;
            all_pass <= 1;
            test_data <= 0;
        end else begin
            if (test_count < 16'hFFFF) begin
                valid_i <= 1;
                test_count <= test_count + 1;
                // Pack: bit j of test_count -> element j (0 or 1, zero-extended to W bits)
                test_data[0*W +: W] <= {{(W-1){1'b0}}, test_count[0]};
                test_data[1*W +: W] <= {{(W-1){1'b0}}, test_count[1]};
                test_data[2*W +: W] <= {{(W-1){1'b0}}, test_count[2]};
                test_data[3*W +: W] <= {{(W-1){1'b0}}, test_count[3]};
                test_data[4*W +: W] <= {{(W-1){1'b0}}, test_count[4]};
                test_data[5*W +: W] <= {{(W-1){1'b0}}, test_count[5]};
                test_data[6*W +: W] <= {{(W-1){1'b0}}, test_count[6]};
                test_data[7*W +: W] <= {{(W-1){1'b0}}, test_count[7]};
                test_data[8*W +: W] <= {{(W-1){1'b0}}, test_count[8]};
                test_data[9*W +: W] <= {{(W-1){1'b0}}, test_count[9]};
                test_data[10*W +: W] <= {{(W-1){1'b0}}, test_count[10]};
                test_data[11*W +: W] <= {{(W-1){1'b0}}, test_count[11]};
                test_data[12*W +: W] <= {{(W-1){1'b0}}, test_count[12]};
                test_data[13*W +: W] <= {{(W-1){1'b0}}, test_count[13]};
                test_data[14*W +: W] <= {{(W-1){1'b0}}, test_count[14]};
                test_data[15*W +: W] <= {{(W-1){1'b0}}, test_count[15]};
            end else begin
                valid_i <= 0;
            end
            
            // Check output is sorted
            if (valid_o) begin
                if (sorted_data[0*W +: W] > sorted_data[1*W +: W] ||
                    sorted_data[1*W +: W] > sorted_data[2*W +: W] ||
                    sorted_data[2*W +: W] > sorted_data[3*W +: W] ||
                    sorted_data[3*W +: W] > sorted_data[4*W +: W] ||
                    sorted_data[4*W +: W] > sorted_data[5*W +: W] ||
                    sorted_data[5*W +: W] > sorted_data[6*W +: W] ||
                    sorted_data[6*W +: W] > sorted_data[7*W +: W] ||
                    sorted_data[7*W +: W] > sorted_data[8*W +: W] ||
                    sorted_data[8*W +: W] > sorted_data[9*W +: W] ||
                    sorted_data[9*W +: W] > sorted_data[10*W +: W] ||
                    sorted_data[10*W +: W] > sorted_data[11*W +: W] ||
                    sorted_data[11*W +: W] > sorted_data[12*W +: W] ||
                    sorted_data[12*W +: W] > sorted_data[13*W +: W] ||
                    sorted_data[13*W +: W] > sorted_data[14*W +: W] ||
                    sorted_data[14*W +: W] > sorted_data[15*W +: W])
                    all_pass <= 0;
            end
        end
    end
    
    assign led_pass = ~all_pass;  // Active low: LED on = pass
endmodule
