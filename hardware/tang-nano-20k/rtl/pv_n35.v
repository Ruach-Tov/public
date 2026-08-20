// pv_n35.v — Reconfigurable sorting network verifier for n=35
// Flat 1D BRAM addressing, one comparator per cycle.
module pv_n35 #(
    parameter N = 35,
    parameter MAX_LAYERS = 24,
    parameter MAX_PER_LAYER = 17,
    parameter TOTAL_SLOTS = 408,  // 24 * 17
    parameter ADDR_W = 9,         // ceil(log2(408))
    parameter IDX_W = 6           // ceil(log2(35))
)(
    input  wire        clk,
    input  wire        rst_n,
    
    input  wire        cfg_we,
    input  wire [ADDR_W-1:0] cfg_addr,
    input  wire [IDX_W-1:0]  cfg_lo,
    input  wire [IDX_W-1:0]  cfg_hi,
    input  wire [4:0]        cfg_num_layers,
    input  wire [4:0]        cfg_layer_count,
    input  wire [4:0]        cfg_layer_idx,
    
    input  wire        verify_start,
    input  wire [N-1:0] test_vector,
    output reg         verify_done,
    output reg         verify_pass,
    output reg         busy
);
    // Flat comparator storage
    reg [IDX_W-1:0] comp_lo [0:TOTAL_SLOTS-1];
    reg [IDX_W-1:0] comp_hi [0:TOTAL_SLOTS-1];
    reg [4:0] lcount [0:MAX_LAYERS-1];
    reg [4:0] num_layers;
    
    always @(posedge clk) begin
        if (cfg_we) begin
            comp_lo[cfg_addr] <= cfg_lo;
            comp_hi[cfg_addr] <= cfg_hi;
            num_layers <= cfg_num_layers;
            lcount[cfg_layer_idx] <= cfg_layer_count;
        end
    end
    
    reg [N-1:0] wires;
    reg [4:0] cur_layer;
    reg [4:0] cur_comp;
    reg [ADDR_W-1:0] flat_addr;
    
    localparam S_IDLE  = 2'd0;
    localparam S_APPLY = 2'd1;
    localparam S_CHECK = 2'd2;
    
    reg [1:0] state;
    
    wire [IDX_W-1:0] clo = comp_lo[flat_addr];
    wire [IDX_W-1:0] chi = comp_hi[flat_addr];
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
                    wires[clo] <= a & b;
                    wires[chi] <= a | b;
                    
                    if (cur_comp >= lcount[cur_layer] - 1) begin
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
