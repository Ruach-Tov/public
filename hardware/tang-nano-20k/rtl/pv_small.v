// Reduced pipelined verifier for synthesis test
module pv_small #(
    parameter N = 16,
    parameter MAX_LAYERS = 12,
    parameter MAX_PER_LAYER = 8,
    parameter TOTAL_SLOTS = 96  // MAX_LAYERS * MAX_PER_LAYER
)(
    input  wire        clk,
    input  wire        rst_n,
    
    input  wire        cfg_we,
    input  wire [6:0]  cfg_addr,    // flat index: layer*MAX_PER_LAYER + slot
    input  wire [3:0]  cfg_lo,
    input  wire [3:0]  cfg_hi,
    input  wire [3:0]  cfg_num_layers,
    input  wire [3:0]  cfg_layer_count,  // comparators in this layer
    input  wire [3:0]  cfg_layer_idx,    // which layer to set count for
    
    input  wire        verify_start,
    input  wire [N-1:0] test_vector,
    output reg         verify_done,
    output reg         verify_pass,
    output reg         busy
);
    // Flat comparator storage
    reg [3:0] comp_lo [0:TOTAL_SLOTS-1];
    reg [3:0] comp_hi [0:TOTAL_SLOTS-1];
    reg [3:0] lcount [0:MAX_LAYERS-1];
    reg [3:0] num_layers;
    
    always @(posedge clk) begin
        if (cfg_we) begin
            comp_lo[cfg_addr] <= cfg_lo;
            comp_hi[cfg_addr] <= cfg_hi;
            num_layers <= cfg_num_layers;
            lcount[cfg_layer_idx] <= cfg_layer_count;
        end
    end
    
    // State
    reg [N-1:0] wires;
    reg [3:0] cur_layer;
    reg [3:0] cur_comp;
    reg [6:0] flat_addr;
    
    localparam S_IDLE  = 2'd0;
    localparam S_APPLY = 2'd1;
    localparam S_CHECK = 2'd2;
    
    reg [1:0] state;
    
    // Read current comparator from flat storage
    wire [3:0] clo = comp_lo[flat_addr];
    wire [3:0] chi = comp_hi[flat_addr];
    wire a = wires[clo];
    wire b = wires[chi];
    
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= S_IDLE; busy <= 0; verify_done <= 0;
        end else begin
            verify_done <= 0;
            case (state)
                S_IDLE: begin
                    if (verify_start) begin
                        wires <= test_vector;
                        cur_layer <= 0;
                        cur_comp <= 0;
                        flat_addr <= 0;
                        state <= S_APPLY;
                        busy <= 1;
                    end
                end
                S_APPLY: begin
                    // Apply one comparator per cycle
                    wires[clo] <= a & b;
                    wires[chi] <= a | b;
                    
                    if (cur_comp >= lcount[cur_layer] - 1) begin
                        // Next layer
                        if (cur_layer >= num_layers - 1) begin
                            state <= S_CHECK;
                        end else begin
                            cur_layer <= cur_layer + 1;
                            cur_comp <= 0;
                            flat_addr <= flat_addr + 1;
                        end
                    end else begin
                        cur_comp <= cur_comp + 1;
                        flat_addr <= flat_addr + 1;
                    end
                end
                S_CHECK: begin
                    // Check sorted
                    verify_pass <= 1;
                    begin : check_blk
                        integer k;
                        for (k = 0; k < N-1; k = k+1)
                            if (wires[k] & ~wires[k+1]) verify_pass <= 0;
                    end
                    verify_done <= 1;
                    busy <= 0;
                    state <= S_IDLE;
                end
            endcase
        end
    end
endmodule
