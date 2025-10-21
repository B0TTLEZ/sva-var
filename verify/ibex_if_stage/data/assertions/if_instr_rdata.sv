```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> (if_instr_rdata == instr_skid_data_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!instr_skid_valid_q) |-> (if_instr_rdata == fetch_rdata));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid) |-> !$isunknown(if_instr_rdata));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & fetch_valid) |-> (if_instr_rdata == instr_skid_data_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (BranchPredictor & predict_branch_taken & ~instr_skid_valid_q) |-> (if_instr_rdata == fetch_rdata));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid & ~instr_skid_valid_q) |-> (if_instr_rdata == fetch_rdata));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_err) |-> (if_instr_rdata == 32'h0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (insert_dummy_instr) |-> (if_instr_rdata == dummy_instr_data));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid & ~fetch_err) |-> (if_instr_rdata == fetch_rdata));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (instr_rdata_id_o == if_instr_rdata));"
    }
]
```