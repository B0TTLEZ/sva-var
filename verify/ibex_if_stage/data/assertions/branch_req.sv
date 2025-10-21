```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (branch_req));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken) |-> (branch_req));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req) |-> (pc_set_i || predict_branch_taken));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i && predict_branch_taken) |-> (branch_req));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req && !pc_set_i) |-> (predict_branch_taken));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req && !predict_branch_taken) |-> (pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (!branch_req));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req) |-> (instr_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req) |-> (prefetch_branch));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req) |-> (fetch_valid_raw));"
    }
]
```