```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_d) |-> (id_in_ready_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (id_in_ready_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_ready && !stall_dummy_instr) |-> (id_in_ready_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d) |-> (id_in_ready_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid) |-> (id_in_ready_i || instr_skid_valid_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (BranchPredictor && predict_branch_taken) |-> (id_in_ready_i || instr_skid_valid_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_q && !instr_valid_clear_i) |-> (id_in_ready_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> (!id_in_ready_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (stall_dummy_instr) |-> (!id_in_ready_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (!id_in_ready_i));"
    }
]
```