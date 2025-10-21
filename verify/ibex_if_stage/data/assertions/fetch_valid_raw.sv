```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o && instr_gnt_i) |-> ##1 fetch_valid_raw);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid_raw) |-> (instr_rvalid_i || prefetch_busy));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid_raw && !fetch_ready) |=> $stable(fetch_valid_raw));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_branch) |-> !fetch_valid_raw);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid_raw && fetch_err) |-> !fetch_valid);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid_raw) |-> !nt_branch_mispredict_i);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid_raw && BranchPredictor) |-> !instr_skid_valid_q);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid_raw) |-> (instr_req_o || ICache));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid_raw && !ICache) |-> prefetch_busy);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid_raw && ICache) |-> (ic_tag_req_o || ic_data_req_o));"
    }
]
```