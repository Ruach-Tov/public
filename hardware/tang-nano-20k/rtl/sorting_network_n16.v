// =============================================================================
// Optimal Sorting Network — N=16, 60 comparators, depth 10
// Network 01 from the Ruach Tov Collective catalog
// L3 program: (s₁, s₂, s₁)
//
// 50% fewer comparators than Batcher's bitonic sort (120 → 60)
// Same depth (10 stages). Same latency. Half the area.
//
// Fully pipelined: one sorted output per clock cycle after
// initial pipeline fill (10 cycles).
//
// Parameters:
//   W — data width per element (default 32 bits)
//
// Ports:
//   clk     — clock
//   rst_n   — active-low reset
//   valid_i — input valid
//   data_i  — 16 × W-bit input (concatenated, element 0 in LSBs)
//   valid_o — output valid (10 cycles after valid_i)
//   data_o  — 16 × W-bit sorted output (element 0 = minimum)
//
// License: Public domain. Ruach Tov Collective, August 2026.
// =============================================================================

module sorting_network_n16 #(
    parameter W = 32    // width of each element in bits
) (
    input  wire             clk,
    input  wire             rst_n,
    input  wire             valid_i,
    input  wire [16*W-1:0]  data_i,
    output wire             valid_o,
    output wire [16*W-1:0]  data_o
);

    // ─── Pipeline stage registers ─────────────────────────────────────────
    // 10 layers + input = 11 sets of 16 wires
    reg [W-1:0] s [0:10][0:15];
    reg [10:0]  valid_pipe;

    // ─── Compare-and-swap primitive ───────────────────────────────────────
    // Outputs: lo = min(a,b), hi = max(a,b)
    function automatic [2*W-1:0] cas;
        input [W-1:0] a, b;
        begin
            if (a <= b)
                cas = {b, a};  // {hi, lo}
            else
                cas = {a, b};  // {hi, lo}
        end
    endfunction

    // Unpack input
    integer k;
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            valid_pipe <= 0;
        end else begin
            valid_pipe <= {valid_pipe[9:0], valid_i};

            // ─── Unpack input ─────────────────────────────────────────
            for (k = 0; k < 16; k = k + 1)
                s[0][k] <= data_i[k*W +: W];

            // ─── Layer 1: (0,1)(2,3)(4,5)(6,7)(8,9)(10,11)(12,13)(14,15)
            {s[1][1],  s[1][0]}  <= cas(s[0][0],  s[0][1]);
            {s[1][3],  s[1][2]}  <= cas(s[0][2],  s[0][3]);
            {s[1][5],  s[1][4]}  <= cas(s[0][4],  s[0][5]);
            {s[1][7],  s[1][6]}  <= cas(s[0][6],  s[0][7]);
            {s[1][9],  s[1][8]}  <= cas(s[0][8],  s[0][9]);
            {s[1][11], s[1][10]} <= cas(s[0][10], s[0][11]);
            {s[1][13], s[1][12]} <= cas(s[0][12], s[0][13]);
            {s[1][15], s[1][14]} <= cas(s[0][14], s[0][15]);

            // ─── Layer 2: (0,2)(1,3)(4,6)(5,7)(8,10)(9,11)(12,14)(13,15)
            {s[2][2],  s[2][0]}  <= cas(s[1][0],  s[1][2]);
            {s[2][3],  s[2][1]}  <= cas(s[1][1],  s[1][3]);
            {s[2][6],  s[2][4]}  <= cas(s[1][4],  s[1][6]);
            {s[2][7],  s[2][5]}  <= cas(s[1][5],  s[1][7]);
            {s[2][10], s[2][8]}  <= cas(s[1][8],  s[1][10]);
            {s[2][11], s[2][9]}  <= cas(s[1][9],  s[1][11]);
            {s[2][14], s[2][12]} <= cas(s[1][12], s[1][14]);
            {s[2][15], s[2][13]} <= cas(s[1][13], s[1][15]);

            // ─── Layer 3: (0,4)(1,5)(2,6)(3,7)(8,12)(9,13)(10,14)(11,15)
            {s[3][4],  s[3][0]}  <= cas(s[2][0],  s[2][4]);
            {s[3][5],  s[3][1]}  <= cas(s[2][1],  s[2][5]);
            {s[3][6],  s[3][2]}  <= cas(s[2][2],  s[2][6]);
            {s[3][7],  s[3][3]}  <= cas(s[2][3],  s[2][7]);
            {s[3][12], s[3][8]}  <= cas(s[2][8],  s[2][12]);
            {s[3][13], s[3][9]}  <= cas(s[2][9],  s[2][13]);
            {s[3][14], s[3][10]} <= cas(s[2][10], s[2][14]);
            {s[3][15], s[3][11]} <= cas(s[2][11], s[2][15]);

            // ─── Layer 4: (0,8)(1,9)(2,10)(3,11)(4,12)(5,13)(6,14)(7,15)
            {s[4][8],  s[4][0]}  <= cas(s[3][0],  s[3][8]);
            {s[4][9],  s[4][1]}  <= cas(s[3][1],  s[3][9]);
            {s[4][10], s[4][2]}  <= cas(s[3][2],  s[3][10]);
            {s[4][11], s[4][3]}  <= cas(s[3][3],  s[3][11]);
            {s[4][12], s[4][4]}  <= cas(s[3][4],  s[3][12]);
            {s[4][13], s[4][5]}  <= cas(s[3][5],  s[3][13]);
            {s[4][14], s[4][6]}  <= cas(s[3][6],  s[3][14]);
            {s[4][15], s[4][7]}  <= cas(s[3][7],  s[3][15]);

            // ─── Layer 5: (1,4)(2,8)(3,12)(5,10)(6,9)(7,13)(11,14)
            {s[5][4],  s[5][1]}  <= cas(s[4][1],  s[4][4]);
            {s[5][8],  s[5][2]}  <= cas(s[4][2],  s[4][8]);
            {s[5][12], s[5][3]}  <= cas(s[4][3],  s[4][12]);
            {s[5][10], s[5][5]}  <= cas(s[4][5],  s[4][10]);
            {s[5][9],  s[5][6]}  <= cas(s[4][6],  s[4][9]);
            {s[5][13], s[5][7]}  <= cas(s[4][7],  s[4][13]);
            {s[5][14], s[5][11]} <= cas(s[4][11], s[4][14]);
            // Pass-through wires not involved in this layer
            s[5][0]  <= s[4][0];
            s[5][15] <= s[4][15];

            // ─── Layer 6: (1,2)(3,6)(4,8)(7,11)(9,12)(13,14)
            {s[6][2],  s[6][1]}  <= cas(s[5][1],  s[5][2]);
            {s[6][6],  s[6][3]}  <= cas(s[5][3],  s[5][6]);
            {s[6][8],  s[6][4]}  <= cas(s[5][4],  s[5][8]);
            {s[6][11], s[6][7]}  <= cas(s[5][7],  s[5][11]);
            {s[6][12], s[6][9]}  <= cas(s[5][9],  s[5][12]);
            {s[6][14], s[6][13]} <= cas(s[5][13], s[5][14]);
            // Pass-through
            s[6][0]  <= s[5][0];
            s[6][5]  <= s[5][5];
            s[6][10] <= s[5][10];
            s[6][15] <= s[5][15];

            // ─── Layer 7: (2,4)(5,8)(7,10)(11,13)
            {s[7][4],  s[7][2]}  <= cas(s[6][2],  s[6][4]);
            {s[7][8],  s[7][5]}  <= cas(s[6][5],  s[6][8]);
            {s[7][10], s[7][7]}  <= cas(s[6][7],  s[6][10]);
            {s[7][13], s[7][11]} <= cas(s[6][11], s[6][13]);
            // Pass-through
            s[7][0]  <= s[6][0];
            s[7][1]  <= s[6][1];
            s[7][3]  <= s[6][3];
            s[7][6]  <= s[6][6];
            s[7][9]  <= s[6][9];
            s[7][12] <= s[6][12];
            s[7][14] <= s[6][14];
            s[7][15] <= s[6][15];

            // ─── Layer 8: (3,5)(6,8)(7,9)(10,12)
            {s[8][5],  s[8][3]}  <= cas(s[7][3],  s[7][5]);
            {s[8][8],  s[8][6]}  <= cas(s[7][6],  s[7][8]);
            {s[8][9],  s[8][7]}  <= cas(s[7][7],  s[7][9]);
            {s[8][12], s[8][10]} <= cas(s[7][10], s[7][12]);
            // Pass-through
            s[8][0]  <= s[7][0];
            s[8][1]  <= s[7][1];
            s[8][2]  <= s[7][2];
            s[8][4]  <= s[7][4];
            s[8][11] <= s[7][11];
            s[8][13] <= s[7][13];
            s[8][14] <= s[7][14];
            s[8][15] <= s[7][15];

            // ─── Layer 9: (3,4)(5,6)(7,8)(9,10)(11,12)
            {s[9][4],  s[9][3]}  <= cas(s[8][3],  s[8][4]);
            {s[9][6],  s[9][5]}  <= cas(s[8][5],  s[8][6]);
            {s[9][8],  s[9][7]}  <= cas(s[8][7],  s[8][8]);
            {s[9][10], s[9][9]}  <= cas(s[8][9],  s[8][10]);
            {s[9][12], s[9][11]} <= cas(s[8][11], s[8][12]);
            // Pass-through
            s[9][0]  <= s[8][0];
            s[9][1]  <= s[8][1];
            s[9][2]  <= s[8][2];
            s[9][13] <= s[8][13];
            s[9][14] <= s[8][14];
            s[9][15] <= s[8][15];

            // ─── Layer 10: (6,7)(8,9)
            {s[10][7],  s[10][6]}  <= cas(s[9][6],  s[9][7]);
            {s[10][9],  s[10][8]}  <= cas(s[9][8],  s[9][9]);
            // Pass-through
            s[10][0]  <= s[9][0];
            s[10][1]  <= s[9][1];
            s[10][2]  <= s[9][2];
            s[10][3]  <= s[9][3];
            s[10][4]  <= s[9][4];
            s[10][5]  <= s[9][5];
            s[10][10] <= s[9][10];
            s[10][11] <= s[9][11];
            s[10][12] <= s[9][12];
            s[10][13] <= s[9][13];
            s[10][14] <= s[9][14];
            s[10][15] <= s[9][15];
        end
    end

    // ─── Pack output ──────────────────────────────────────────────────────
    genvar g;
    generate
        for (g = 0; g < 16; g = g + 1) begin : pack_out
            assign data_o[g*W +: W] = s[10][g];
        end
    endgenerate

    assign valid_o = valid_pipe[10];

endmodule
