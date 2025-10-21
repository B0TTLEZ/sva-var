```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |-> !$isunknown(branch_target_ex_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |-> (branch_target_ex_i[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i && (pc_mux_i == PC_JUMP)) |-> ##1 (instr_addr_o == branch_target_ex_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req && (pc_mux_internal == PC_JUMP)) |-> (fetch_addr_n == branch_target_ex_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |-> (branch_target_ex_i != 32'h0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |-> (branch_target_ex_i != pc_if_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |-> (branch_target_ex_i != pc_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |-> (branch_target_ex_i != {boot_addr_i[31:8], 8'h80}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |-> (branch_target_ex_i != csr_mepc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |-> (branch_target_ex_i != csr_depc_i));"
    }
]
```