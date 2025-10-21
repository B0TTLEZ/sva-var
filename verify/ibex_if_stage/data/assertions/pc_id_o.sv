```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |=> (pc_id_o == $past(fetch_addr_n)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d) |-> (pc_id_o == pc_if_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o) |-> (pc_id_o[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!instr_is_compressed_id_o) |-> (pc_id_o[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_JUMP) |=> (pc_id_o == branch_target_ex_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_EXC) |=> (pc_id_o == exc_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_ERET) |=> (pc_id_o == csr_mepc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_DRET) |=> (pc_id_o == csr_depc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_BOOT) |=> (pc_id_o == {boot_addr_i[31:8], 8'h80}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_clear_i) |=> (pc_id_o == $past(pc_id_o)));"
    }
]
```