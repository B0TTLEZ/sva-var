```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> (instr_skid_bp_taken_q == predict_branch_taken));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_en) |=> (instr_skid_bp_taken_q == $past(predict_branch_taken)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q && !instr_skid_en) |=> (instr_skid_bp_taken_q == $past(instr_skid_bp_taken_q)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> (instr_skid_bp_taken_q == instr_bp_taken_d));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_en) |-> (instr_skid_bp_taken_q == predict_branch_taken));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q && !instr_skid_en) |-> (instr_skid_bp_taken_q == $past(instr_skid_bp_taken_q)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q && id_in_ready_i) |-> (instr_skid_bp_taken_q == instr_bp_taken_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q && !id_in_ready_i) |-> (instr_skid_bp_taken_q == $past(instr_skid_bp_taken_q)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_en) |-> (instr_skid_bp_taken_q == predict_branch_taken));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q && !instr_skid_en && !id_in_ready_i) |-> (instr_skid_bp_taken_q == $past(instr_skid_bp_taken_q)));"
    }
]
```