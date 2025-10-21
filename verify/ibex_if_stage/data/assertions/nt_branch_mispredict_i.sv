```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (predict_branch_taken));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (branch_req == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (instr_skid_valid_q == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (fetch_valid_raw == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (fetch_err == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (fetch_ready == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (if_instr_valid == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (if_instr_bus_err == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (if_instr_pmp_err == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (if_instr_err == 0));"
    }
]
```