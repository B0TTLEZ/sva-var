```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_BOOT) |-> (fetch_addr_n[7:0] == 8'h80));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |-> (fetch_addr_n == branch_target_ex_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_EXC) |-> (fetch_addr_n == exc_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_ERET) |-> (fetch_addr_n == csr_mepc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_DRET) |-> (fetch_addr_n == csr_depc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_BP) |-> (fetch_addr_n == predict_branch_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i inside {PC_BOOT, PC_JUMP, PC_EXC, PC_ERET, PC_DRET, PC_BP}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (pc_mux_i != PC_BP) || BranchPredictor);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_BOOT && pc_set_i) |-> csr_mtvec_init_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_BOOT) |-> (fetch_addr_n[31:8] == boot_addr_i[31:8]));"
    }
]
```