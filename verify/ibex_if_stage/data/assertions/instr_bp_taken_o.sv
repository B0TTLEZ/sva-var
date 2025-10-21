```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_o) |-> (BranchPredictor));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_o) |-> (instr_skid_valid_q | predict_branch_taken));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_o) |-> (if_id_pipe_reg_we));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_o) |-> (fetch_valid | instr_skid_valid_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_o) |-> !(fetch_err));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_o) |-> !(pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_o) |-> !(illegal_c_insn));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_o) |-> (instr_bp_taken_d));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_o) |-> (predict_branch_taken_raw));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_o) |-> !(stall_dummy_instr));"
    }
]
```