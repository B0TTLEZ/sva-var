```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & ~id_in_ready_i & ~stall_dummy_instr) |-> instr_skid_valid_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken & ~pc_set_i & ~id_in_ready_i & ~instr_skid_valid_q) |-> instr_skid_valid_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) instr_skid_valid_d |-> (instr_skid_valid_q & ~id_in_ready_i & ~stall_dummy_instr) || (predict_branch_taken & ~pc_set_i & ~id_in_ready_i & ~instr_skid_valid_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & id_in_ready_i) |-> !instr_skid_valid_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & stall_dummy_instr) |-> !instr_skid_valid_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i & predict_branch_taken) |-> !instr_skid_valid_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (id_in_ready_i & predict_branch_taken) |-> !instr_skid_valid_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & predict_branch_taken) |-> !instr_skid_valid_d);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) instr_skid_valid_d |-> ##1 instr_skid_valid_q);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) $rose(instr_skid_valid_d) |-> $past(predict_branch_taken & ~pc_set_i & ~id_in_ready_i & ~instr_skid_valid_q));"
    }
]
```