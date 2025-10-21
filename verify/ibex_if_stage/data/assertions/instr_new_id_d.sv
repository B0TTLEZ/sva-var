```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid & id_in_ready_i & ~pc_set_i) |-> instr_new_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (~if_instr_valid | ~id_in_ready_i | pc_set_i) |-> ~instr_new_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d) |-> (if_instr_valid & id_in_ready_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> ~instr_new_id_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d) |-> $past(if_instr_valid,1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d) |-> $past(id_in_ready_i,1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d) |-> $past(~pc_set_i,1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d & ~instr_valid_clear_i) |=> instr_valid_id_q);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d & instr_valid_clear_i) |=> ~instr_valid_id_q);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d) |=> instr_new_id_q);"
    }
]
```