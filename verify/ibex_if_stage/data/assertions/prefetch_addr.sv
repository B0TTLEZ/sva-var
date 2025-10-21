```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req) |-> (prefetch_addr == {fetch_addr_n[31:1], 1'b0}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i) |-> (prefetch_addr == nt_branch_addr_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_branch) |-> (prefetch_addr[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req && nt_branch_mispredict_i) |-> (prefetch_addr == nt_branch_addr_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_branch && !branch_req) |-> (prefetch_addr == nt_branch_addr_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_branch && branch_req) |-> (prefetch_addr == {fetch_addr_n[31:1], 1'b0}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_branch) |-> !$isunknown(prefetch_addr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (prefetch_addr == {fetch_addr_n[31:1], 1'b0}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken) |-> (prefetch_addr == predict_branch_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_branch && !nt_branch_mispredict_i) |-> (prefetch_addr == {fetch_addr_n[31:1], 1'b0}));"
    }
]
```