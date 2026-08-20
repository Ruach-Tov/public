// reconfigurable_cas.v — Reconfigurable Compare-And-Swap unit
// Instead of hardwired connections, reads (lo, hi) wire indices from BRAM
// and routes the appropriate wires through the comparator.
//
// Each CAS unit:
//   1. Reads pair (lo_idx, hi_idx) from config BRAM
//   2. Selects wires[lo_idx] and wires[hi_idx] from the bus
//   3. Computes min/max
//   4. Writes results back to wires[lo_idx] and wires[hi_idx]
//
// For n=35, W=1: each wire is 1 bit. The "bus" is 35 bits.
// A full layer of non-conflicting comparators can execute in one cycle.
//
// Ruach Tov Collective, 2026. CC BY 4.0.

// Single reconfigurable comparator: given a bus, swap two indexed wires
module reconfig_cas #(
    parameter N = 35,               // number of wires
    parameter IDX_W = 6             // bits for wire index (ceil(log2(N)))
)(
    input  wire [N-1:0]     data_in,
    input  wire [IDX_W-1:0] lo_idx,     // wire index for min output
    input  wire [IDX_W-1:0] hi_idx,     // wire index for max output
    input  wire             enable,      // 0 = pass through, 1 = compare-and-swap
    output wire [N-1:0]     data_out
);
    wire a = data_in[lo_idx];   // value on lo wire
    wire b = data_in[hi_idx];   // value on hi wire
    wire mn = a & b;            // min (for W=1)
    wire mx = a | b;            // max (for W=1)
    
    // Build output: replace lo_idx with min, hi_idx with max, rest unchanged
    // Use generate to build the MUX for each output bit
    genvar i;
    generate
        for (i = 0; i < N; i = i + 1) begin : mux
            assign data_out[i] = (!enable)    ? data_in[i] :
                                 (i == lo_idx) ? mn :
                                 (i == hi_idx) ? mx :
                                                 data_in[i];
        end
    endgenerate
endmodule

// Pipelined reconfigurable sorting network verifier
// Reads comparator pairs from BRAM, applies them sequentially,
// checks if output is sorted.
module reconfig_sorter_verify #(
    parameter N = 35,
    parameter MAX_COMPS = 256,       // max comparators
    parameter IDX_W = 6,
    parameter COMP_ADDR_W = 8        // ceil(log2(MAX_COMPS))
)(
    input  wire             clk,
    input  wire             rst_n,
    
    // Configuration interface (RISC-V writes pairs here)
    input  wire             cfg_we,          // write enable
    input  wire [COMP_ADDR_W-1:0] cfg_addr,  // comparator index
    input  wire [IDX_W-1:0] cfg_lo,          // lo wire index
    input  wire [IDX_W-1:0] cfg_hi,          // hi wire index
    input  wire [COMP_ADDR_W-1:0] cfg_num_comps, // total comparators
    
    // Verification interface
    input  wire             verify_start,    // pulse to start verification
    input  wire [N-1:0]     test_vector,     // input to test
    output reg              verify_done,     // pulses when result ready
    output reg              verify_pass,     // 1 = sorted, 0 = not sorted
    output reg              busy
);
    // Comparator pair storage (BRAM)
    reg [IDX_W-1:0] comp_lo [0:MAX_COMPS-1];
    reg [IDX_W-1:0] comp_hi [0:MAX_COMPS-1];
    reg [COMP_ADDR_W-1:0] num_comps;
    
    // Configuration write
    always @(posedge clk) begin
        if (cfg_we) begin
            comp_lo[cfg_addr] <= cfg_lo;
            comp_hi[cfg_addr] <= cfg_hi;
        end
    end
    
    always @(posedge clk) begin
        if (cfg_we && cfg_addr == 0)
            num_comps <= cfg_num_comps;
    end
    
    // State machine for sequential verification
    reg [N-1:0] wires;
    reg [COMP_ADDR_W-1:0] comp_idx;
    
    localparam S_IDLE    = 2'd0;
    localparam S_APPLY   = 2'd1;
    localparam S_CHECK   = 2'd2;
    localparam S_DONE    = 2'd3;
    
    reg [1:0] state;
    
    // Current comparator
    wire [IDX_W-1:0] cur_lo = comp_lo[comp_idx];
    wire [IDX_W-1:0] cur_hi = comp_hi[comp_idx];
    
    // Apply one CAS
    wire a_val = wires[cur_lo];
    wire b_val = wires[cur_hi];
    wire mn_val = a_val & b_val;
    wire mx_val = a_val | b_val;
    
    // Check sorted
    reg sorted;
    reg [IDX_W-1:0] check_idx;
    
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
                        comp_idx <= 0;
                        state <= S_APPLY;
                        busy <= 1;
                    end
                end
                
                S_APPLY: begin
                    // Apply current comparator
                    wires[cur_lo] <= mn_val;
                    wires[cur_hi] <= mx_val;
                    
                    if (comp_idx >= num_comps - 1) begin
                        state <= S_CHECK;
                        check_idx <= 0;
                        sorted <= 1;
                    end else begin
                        comp_idx <= comp_idx + 1;
                    end
                end
                
                S_CHECK: begin
                    // Check if output is sorted (no 1->0 transitions)
                    if (wires[check_idx] & ~wires[check_idx + 1])
                        sorted <= 0;
                    
                    if (check_idx >= N - 2) begin
                        state <= S_DONE;
                    end else begin
                        check_idx <= check_idx + 1;
                    end
                end
                
                S_DONE: begin
                    verify_pass <= sorted;
                    verify_done <= 1;
                    busy <= 0;
                    state <= S_IDLE;
                end
            endcase
        end
    end
endmodule

// Top-level: batch verifier — tests multiple vectors against one network
module batch_verifier #(
    parameter N = 35,
    parameter MAX_COMPS = 256,
    parameter MAX_VECTORS = 1024,    // test vectors stored in BRAM
    parameter IDX_W = 6,
    parameter COMP_ADDR_W = 8,
    parameter VEC_ADDR_W = 10
)(
    input  wire             clk,
    input  wire             rst_n,
    
    // Configuration: comparator pairs
    input  wire             cfg_comp_we,
    input  wire [COMP_ADDR_W-1:0] cfg_comp_addr,
    input  wire [IDX_W-1:0] cfg_comp_lo,
    input  wire [IDX_W-1:0] cfg_comp_hi,
    input  wire [COMP_ADDR_W-1:0] cfg_num_comps,
    
    // Configuration: test vectors
    input  wire             cfg_vec_we,
    input  wire [VEC_ADDR_W-1:0] cfg_vec_addr,
    input  wire [N-1:0]     cfg_vec_data,
    input  wire [VEC_ADDR_W-1:0] cfg_num_vectors,
    
    // Control
    input  wire             start_batch,     // start testing all vectors
    output reg              batch_done,      // all vectors tested
    output reg              batch_pass,      // 1 = all passed, 0 = at least one failed
    output reg [VEC_ADDR_W-1:0] fail_vector  // index of first failing vector
);
    // Test vector storage
    reg [N-1:0] vectors [0:MAX_VECTORS-1];
    reg [VEC_ADDR_W-1:0] num_vectors;
    
    always @(posedge clk) begin
        if (cfg_vec_we) begin
            vectors[cfg_vec_addr] <= cfg_vec_data;
            if (cfg_vec_addr == 0) num_vectors <= cfg_num_vectors;
        end
    end
    
    // Instantiate single verifier
    wire v_done, v_pass, v_busy;
    reg v_start;
    reg [N-1:0] v_input;
    
    reconfig_sorter_verify #(
        .N(N), .MAX_COMPS(MAX_COMPS), .IDX_W(IDX_W), .COMP_ADDR_W(COMP_ADDR_W)
    ) verifier (
        .clk(clk), .rst_n(rst_n),
        .cfg_we(cfg_comp_we), .cfg_addr(cfg_comp_addr),
        .cfg_lo(cfg_comp_lo), .cfg_hi(cfg_comp_hi),
        .cfg_num_comps(cfg_num_comps),
        .verify_start(v_start), .test_vector(v_input),
        .verify_done(v_done), .verify_pass(v_pass), .busy(v_busy)
    );
    
    // Batch state machine
    reg [VEC_ADDR_W-1:0] vec_idx;
    
    localparam B_IDLE = 2'd0;
    localparam B_LAUNCH = 2'd1;
    localparam B_WAIT = 2'd2;
    localparam B_DONE = 2'd3;
    
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
                        if (!v_pass) begin
                            // Failed — stop early
                            batch_pass <= 0;
                            fail_vector <= vec_idx;
                            bstate <= B_DONE;
                        end else if (vec_idx >= num_vectors - 1) begin
                            // All passed
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
