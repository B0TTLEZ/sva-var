```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid & id_in_ready_i & ~pc_set_i) |-> instr_valid_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_q & ~instr_valid_clear_i) |-> instr_valid_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid & id_in_ready_i & pc_set_i) |-> ~instr_valid_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (~if_instr_valid & ~instr_valid_id_q) |-> ~instr_valid_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_clear_i) |-> ~instr_valid_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_q & instr_valid_clear_i) |-> ~instr_valid_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid & ~id_in_ready_i) |-> ~instr_valid_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> ~instr_valid_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid & id_in_ready_i & ~pc_set_i) |=> instr_valid_id_q);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_d) |=> instr_valid_id_q);"
    }
]
```