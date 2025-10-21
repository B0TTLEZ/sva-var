```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> (instr_bp_taken_d == instr_skid_bp_taken_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!instr_skid_valid_q) |-> (instr_bp_taken_d == predict_branch_taken));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken && !instr_skid_valid_q) |-> (instr_bp_taken_d));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!predict_branch_taken && !instr_skid_valid_q) |-> (!instr_bp_taken_d));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q && instr_skid_bp_taken_q) |-> (instr_bp_taken_d));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q && !instr_skid_bp_taken_q) |-> (!instr_bp_taken_d));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (!instr_bp_taken_d));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_err) |-> (!instr_bp_taken_d));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_bp_taken_d && if_id_pipe_reg_we) |-> (instr_bp_taken_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!instr_bp_taken_d && if_id_pipe_reg_we) |-> (!instr_bp_taken_q));"
    }
]
```