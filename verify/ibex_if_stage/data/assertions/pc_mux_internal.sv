```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_BOOT) |-> (pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_JUMP) |-> (pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_EXC) |-> (pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_ERET) |-> (pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_DRET) |-> (pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_BP) |-> (BranchPredictor && predict_branch_taken && !pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal inside {PC_BOOT, PC_JUMP, PC_EXC, PC_ERET, PC_DRET, PC_BP}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal != PC_BP) |-> !(BranchPredictor && predict_branch_taken && !pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_BP) |-> !pc_set_i);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_BP) |-> predict_branch_taken);"
    }
]
```