```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid) |-> if_instr_valid);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> if_instr_valid);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid && instr_skid_valid_q) |-> if_instr_valid);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> !if_instr_valid);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid && !instr_skid_valid_q) |-> if_instr_valid);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid) |-> (fetch_valid || instr_skid_valid_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid && !instr_skid_valid_q) |-> fetch_valid);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid && instr_skid_valid_q) |-> !fetch_valid);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> !if_instr_valid);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid) |-> !pc_set_i);"
    }
]
```