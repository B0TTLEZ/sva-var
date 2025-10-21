```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o) |-> !$isunknown(fetch_addr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o) |-> (fetch_addr[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid) |-> (fetch_addr == pc_if_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_branch) |-> (fetch_addr == prefetch_addr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (fetch_addr == fetch_addr_n));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (BranchPredictor && predict_branch_taken && !pc_set_i) |-> (fetch_addr == predict_branch_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid && !fetch_err) |-> (fetch_addr == pc_if_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> (fetch_addr == instr_skid_addr_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (fetch_addr == pc_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (PCIncrCheck && prev_instr_seq_q) |-> (fetch_addr == prev_instr_addr_incr_buf));"
    }
]
```