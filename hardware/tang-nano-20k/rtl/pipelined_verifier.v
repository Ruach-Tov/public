// pipelined_verifier.v — Layer-parallel reconfigurable sorting network verifier
// Each layer of non-conflicting comparators executes in ONE clock cycle.
// A 14-layer network verifies one test vector in 14 cycles.
// At 594 MHz: 14 cycles × 1.68ns = 23.5 ns per vector.
// 1000 vectors = 23.5 microseconds per mutation check.
//
// Architecture:
//   - Up to MAX_LAYERS layers, each with up to N/2 comparators
//   - Layer config stored in BRAM: for each layer, a bitmask of active
//     comparators plus their (lo, hi) indices
//   - Pipeline: one layer applied per clock cycle
//   - After all layers: check sorted in one cycle
//
// Ruach Tov Collective, 2026. CC BY 4.0.

module pipelined_verifier #(
    parameter N = 35,                // number of wires
    parameter W = 1,                 // bits per wire (1 for 0-1 principle)
    parameter MAX_LAYERS = 24,       // max depth
    parameter MAX_PER_LAYER = 17,    // max comparators per layer (N/2 rounded)
    parameter IDX_W = 6,             // bits for wire index
    parameter LAYER_W = 5            // bits for layer index
)(
    input  wire             clk,
    input  wire             rst_n,
    
    // --- Configuration interface ---
    // Write one comparator at a time: layer index, slot, lo/hi, enable
    input  wire             cfg_we,
    input  wire [LAYER_W-1:0]  cfg_layer,
    input  wire [4:0]          cfg_slot,     // 0..MAX_PER_LAYER-1
    input  wire [IDX_W-1:0]    cfg_lo,
    input  wire [IDX_W-1:0]    cfg_hi,
    
    // Set the number of active layers and comparators per layer
    input  wire             cfg_meta_we,
    input  wire [LAYER_W-1:0]  cfg_num_layers,
    
    // --- Verification interface ---
    input  wire             verify_start,
    input  wire [N*W-1:0]   test_vector,    // packed input
    output reg              verify_done,
    output reg              verify_pass,
    output reg              busy
);

    // Comparator storage: for each layer, up to MAX_PER_LAYER (lo, hi) pairs
    reg [IDX_W-1:0] layer_lo [0:MAX_LAYERS-1][0:MAX_PER_LAYER-1];
    reg [IDX_W-1:0] layer_hi [0:MAX_LAYERS-1][0:MAX_PER_LAYER-1];
    reg [4:0]       layer_count [0:MAX_LAYERS-1]; // active comparators in this layer
    reg [LAYER_W-1:0] num_layers;
    
    // Configuration write
    always @(posedge clk) begin
        if (cfg_we) begin
            layer_lo[cfg_layer][cfg_slot] <= cfg_lo;
            layer_hi[cfg_layer][cfg_slot] <= cfg_hi;
        end
        if (cfg_meta_we) begin
            num_layers <= cfg_num_layers;
        end
    end
    
    // Track comparator count per layer via cfg writes
    // (Use cfg_slot + 1 as count when it's the highest slot written)
    always @(posedge clk) begin
        if (cfg_we) begin
            if (cfg_slot >= layer_count[cfg_layer])
                layer_count[cfg_layer] <= cfg_slot + 1;
        end
    end

    // ================================================================
    // Verification pipeline
    // ================================================================
    
    // Wire state registers
    reg [N*W-1:0] wires;
    reg [LAYER_W-1:0] cur_layer;
    
    // Apply one full layer combinationally
    // All comparators in a layer are non-conflicting, so they can
    // execute simultaneously. We build the next wire state by
    // iterating over comparators in the current layer.
    
    // For W=1: each CAS is just AND/OR on single bits
    reg [N*W-1:0] next_wires;
    integer c;
    
    always @(*) begin
        next_wires = wires;  // default: pass through
        for (c = 0; c < MAX_PER_LAYER; c = c + 1) begin
            if (c < layer_count[cur_layer]) begin
                // Apply CAS: min to lo, max to hi
                next_wires[layer_lo[cur_layer][c]] = 
                    wires[layer_lo[cur_layer][c]] & wires[layer_hi[cur_layer][c]];
                next_wires[layer_hi[cur_layer][c]] = 
                    wires[layer_lo[cur_layer][c]] | wires[layer_hi[cur_layer][c]];
            end
        end
    end
    
    // Check sorted: no 1→0 transitions
    reg is_sorted;
    integer k;
    always @(*) begin
        is_sorted = 1'b1;
        for (k = 0; k < N-1; k = k + 1) begin
            if (wires[k] & ~wires[k+1])
                is_sorted = 1'b0;
        end
    end
    
    // State machine
    localparam S_IDLE  = 2'd0;
    localparam S_APPLY = 2'd1;
    localparam S_CHECK = 2'd2;
    localparam S_DONE  = 2'd3;
    
    reg [1:0] state;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= S_IDLE;
            busy <= 0;
            verify_done <= 0;
            verify_pass <= 0;
        end else begin
            verify_done <= 0;
            
            case (state)
                S_IDLE: begin
                    if (verify_start) begin
                        wires <= test_vector;
                        cur_layer <= 0;
                        state <= S_APPLY;
                        busy <= 1;
                    end
                end
                
                S_APPLY: begin
                    wires <= next_wires;
                    if (cur_layer >= num_layers - 1) begin
                        state <= S_CHECK;
                    end else begin
                        cur_layer <= cur_layer + 1;
                    end
                end
                
                S_CHECK: begin
                    verify_pass <= is_sorted;
                    verify_done <= 1;
                    busy <= 0;
                    state <= S_IDLE;
                end
                
                default: state <= S_IDLE;
            endcase
        end
    end
endmodule


// Batch wrapper: feeds multiple test vectors through the pipelined verifier
module pipelined_batch_verifier #(
    parameter N = 35,
    parameter W = 1,
    parameter MAX_LAYERS = 24,
    parameter MAX_PER_LAYER = 17,
    parameter MAX_VECTORS = 1024,
    parameter IDX_W = 6,
    parameter LAYER_W = 5,
    parameter VEC_ADDR_W = 10
)(
    input  wire             clk,
    input  wire             rst_n,
    
    // Comparator config (directly connected to pipelined_verifier)
    input  wire             cfg_we,
    input  wire [LAYER_W-1:0]  cfg_layer,
    input  wire [4:0]          cfg_slot,
    input  wire [IDX_W-1:0]    cfg_lo,
    input  wire [IDX_W-1:0]    cfg_hi,
    input  wire             cfg_meta_we,
    input  wire [LAYER_W-1:0]  cfg_num_layers,
    
    // Test vector config
    input  wire             cfg_vec_we,
    input  wire [VEC_ADDR_W-1:0] cfg_vec_addr,
    input  wire [N*W-1:0]      cfg_vec_data,
    input  wire [VEC_ADDR_W-1:0] cfg_num_vectors,
    
    // Batch control
    input  wire             start_batch,
    output reg              batch_done,
    output reg              batch_pass,       // 1 = all vectors sorted
    output reg [VEC_ADDR_W-1:0] vectors_tested,
    output reg [VEC_ADDR_W-1:0] first_fail
);

    // Test vector storage
    reg [N*W-1:0] vectors [0:MAX_VECTORS-1];
    reg [VEC_ADDR_W-1:0] num_vectors;
    
    always @(posedge clk) begin
        if (cfg_vec_we) begin
            vectors[cfg_vec_addr] <= cfg_vec_data;
        end
        if (cfg_vec_we && cfg_vec_addr == 0)
            num_vectors <= cfg_num_vectors;
    end
    
    // Pipelined verifier instance
    wire v_done, v_pass, v_busy;
    reg  v_start;
    reg  [N*W-1:0] v_input;
    
    pipelined_verifier #(
        .N(N), .W(W), .MAX_LAYERS(MAX_LAYERS),
        .MAX_PER_LAYER(MAX_PER_LAYER), .IDX_W(IDX_W), .LAYER_W(LAYER_W)
    ) pv (
        .clk(clk), .rst_n(rst_n),
        .cfg_we(cfg_we), .cfg_layer(cfg_layer), .cfg_slot(cfg_slot),
        .cfg_lo(cfg_lo), .cfg_hi(cfg_hi),
        .cfg_meta_we(cfg_meta_we), .cfg_num_layers(cfg_num_layers),
        .verify_start(v_start), .test_vector(v_input),
        .verify_done(v_done), .verify_pass(v_pass), .busy(v_busy)
    );
    
    // Batch state machine
    reg [VEC_ADDR_W-1:0] vec_idx;
    
    localparam B_IDLE   = 2'd0;
    localparam B_LAUNCH = 2'd1;
    localparam B_WAIT   = 2'd2;
    localparam B_DONE   = 2'd3;
    
    reg [1:0] bstate;
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            bstate <= B_IDLE;
            batch_done <= 0;
            batch_pass <= 0;
            v_start <= 0;
        end else begin
            batch_done <= 0;
            v_start <= 0;
            
            case (bstate)
                B_IDLE: begin
                    if (start_batch) begin
                        vec_idx <= 0;
                        batch_pass <= 1;
                        vectors_tested <= 0;
                        bstate <= B_LAUNCH;
                    end
                end
                
                B_LAUNCH: begin
                    v_input <= vectors[vec_idx];
                    v_start <= 1;
                    bstate <= B_WAIT;
                end
                
                B_WAIT: begin
                    if (v_done) begin
                        vectors_tested <= vec_idx + 1;
                        if (!v_pass) begin
                            batch_pass <= 0;
                            first_fail <= vec_idx;
                            bstate <= B_DONE;
                        end else if (vec_idx >= num_vectors - 1) begin
                            bstate <= B_DONE;
                        end else begin
                            vec_idx <= vec_idx + 1;
                            bstate <= B_LAUNCH;
                        end
                    end
                end
                
                B_DONE: begin
                    batch_done <= 1;
                    bstate <= B_IDLE;
                end
            endcase
        end
    end
endmodule
