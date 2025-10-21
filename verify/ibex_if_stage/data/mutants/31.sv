```json
[
    {
        "original_code_slice": "always_ff @(posedge clk_i or negedge rst_ni) begin",
        "mutation_code_slice": "always_ff @(negedge clk_i or negedge rst_ni) begin"
    },
    {
        "original_code_slice": "always_ff @(posedge clk_i or negedge rst_ni) begin",
        "mutation_code_slice": "always_ff @(posedge clk_i or posedge rst_ni) begin"
    },
    {
        "original_code_slice": "always_ff @(posedge clk_i or negedge rst_ni) begin",
        "mutation_code_slice": "always_ff @(negedge clk_i or posedge rst_ni) begin"
    },
    {
        "original_code_slice": "always_ff @(posedge clk_i or negedge rst_ni) begin",
        "mutation_code_slice": "always_ff @(posedge clk_i) begin"
    },
    {
        "original_code_slice": "always_ff @(posedge clk_i or negedge rst_ni) begin",
        "mutation_code_slice": "always_ff @(negedge clk_i) begin"
    },
    {
        "original_code_slice": "always_ff @(posedge clk_i) begin",
        "mutation_code_slice": "always_ff @(negedge clk_i) begin"
    },
    {
        "original_code_slice": "always_ff @(posedge clk_i) begin",
        "mutation_code_slice": "always_ff @(posedge clk_i or negedge rst_ni) begin"
    },
    {
        "original_code_slice": "always_comb begin : exc_pc_mux",
        "mutation_code_slice": "always @(*) begin : exc_pc_mux"
    },
    {
        "original_code_slice": "always_comb begin : fetch_addr_mux",
        "mutation_code_slice": "always @(*) begin : fetch_addr_mux"
    },
    {
        "original_code_slice": "always_comb begin : exc_pc_mux",
        "mutation_code_slice": "always @(exc_pc_mux_i or csr_mtvec_i or exc_cause or DmHaltAddr or DmExceptionAddr) begin : exc_pc_mux"
    }
]
```