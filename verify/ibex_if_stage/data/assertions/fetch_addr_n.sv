```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_BOOT) |-> (fetch_addr_n == {boot_addr_i[31:8], 8'h80}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_JUMP) |-> (fetch_addr_n == branch_target_ex_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_EXC) |-> (fetch_addr_n == exc_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_ERET) |-> (fetch_addr_n == csr_mepc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_DRET) |-> (fetch_addr_n == csr_depc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_BP && BranchPredictor) |-> (fetch_addr_n == predict_branch_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (fetch_addr_n[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_BOOT) |-> (fetch_addr_n[7:0] == 8'h80));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_EXC) |-> (fetch_addr_n[7:0] == exc_pc[7:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_internal == PC_JUMP) |-> (fetch_addr_n[1:0] == branch_target_ex_i[1:0]));"
    }
]
```