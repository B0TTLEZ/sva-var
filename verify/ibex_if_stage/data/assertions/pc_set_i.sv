```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (branch_req));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (prefetch_branch));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (fetch_addr_n == {boot_addr_i[31:8], 8'h80}) || (pc_mux_i == PC_JUMP) || (pc_mux_i == PC_EXC) || (pc_mux_i == PC_ERET) || (pc_mux_i == PC_DRET));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i && pc_mux_i == PC_BOOT) |-> (fetch_addr_n == {boot_addr_i[31:8], 8'h80}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i && pc_mux_i == PC_JUMP) |-> (fetch_addr_n == branch_target_ex_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i && pc_mux_i == PC_EXC) |-> (fetch_addr_n == exc_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i && pc_mux_i == PC_ERET) |-> (fetch_addr_n == csr_mepc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i && pc_mux_i == PC_DRET) |-> (fetch_addr_n == csr_depc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (instr_valid_id_d == (if_instr_valid & id_in_ready_i & ~pc_set_i) | (instr_valid_id_q & ~instr_valid_clear_i)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (instr_new_id_d == (if_instr_valid & id_in_ready_i)));"
    }
]
```