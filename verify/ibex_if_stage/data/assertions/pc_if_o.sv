```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (pc_if_o == fetch_addr_n));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_BOOT) |-> (pc_if_o == {boot_addr_i[31:8], 8'h80}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |-> (pc_if_o == branch_target_ex_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_EXC) |-> (pc_if_o == exc_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_ERET) |-> (pc_if_o == csr_mepc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_DRET) |-> (pc_if_o == csr_depc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (BranchPredictor && predict_branch_taken && !pc_set_i) |-> (pc_if_o == predict_branch_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> (pc_if_o == instr_skid_addr_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid) |-> (pc_if_o == fetch_addr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_if_o[1:0] == 2'b00));"
    }
]
```