// =============================================================================
// Testbench for sorting_network_n16_d9 (depth-optimal, 61 comparators, 9 layers)
// Exhaustive 0-1 verification (2^16 = 65536 inputs)
// =============================================================================

`timescale 1ns / 1ps

module tb_sorting_network_n16_d9;

    parameter W = 8;
    parameter N = 16;

    reg              clk;
    reg              rst_n;
    reg              valid_i;
    reg  [N*W-1:0]   data_i;
    wire             valid_o;
    wire [N*W-1:0]   data_o;

    sorting_network_n16_d9 #(.W(W)) dut (
        .clk(clk), .rst_n(rst_n),
        .valid_i(valid_i), .data_i(data_i),
        .valid_o(valid_o), .data_o(data_o)
    );

    always #5 clk = ~clk;

    integer i, j, pass_count, fail_count;
    reg [W-1:0] out_elem [0:N-1];
    reg sorted;

    initial begin
        clk = 0;
        rst_n = 0;
        valid_i = 0;
        data_i = 0;
        pass_count = 0;
        fail_count = 0;

        #20;
        rst_n = 1;
        #10;

        $display("=== Exhaustive 0-1 verification (2^16 = 65536 inputs) ===");
        $display("Network: N=16, 61 comparators, depth 9 (Network D01)");
        $display("");

        for (i = 0; i < 65536; i = i + 1) begin
            @(posedge clk);
            valid_i = 1;
            for (j = 0; j < N; j = j + 1)
                data_i[j*W +: W] = (i >> j) & 1;
        end

        for (i = 0; i < 11; i = i + 1) begin
            @(posedge clk);
            valid_i = 0;
        end

        #100;

        $display("");
        $display("=== Results ===");
        $display("Passed: %0d", pass_count);
        $display("Failed: %0d", fail_count);

        if (fail_count == 0)
            $display("VERIFIED: Network sorts all 2^16 binary inputs correctly.");
        else
            $display("FAILED: %0d inputs not sorted correctly.", fail_count);

        $finish;
    end

    always @(posedge clk) begin
        if (valid_o) begin
            for (j = 0; j < N; j = j + 1)
                out_elem[j] = data_o[j*W +: W];

            sorted = 1;
            for (j = 0; j < N-1; j = j + 1) begin
                if (out_elem[j] > out_elem[j+1])
                    sorted = 0;
            end

            if (sorted)
                pass_count = pass_count + 1;
            else begin
                fail_count = fail_count + 1;
                if (fail_count <= 10) begin
                    $display("FAIL at output %0d:", pass_count + fail_count);
                    for (j = 0; j < N; j = j + 1)
                        $write(" %0d", out_elem[j]);
                    $display("");
                end
            end
        end
    end

endmodule
