```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> !$isunknown(unused_fetch_addr_n0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (unused_fetch_addr_n0 == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid) |-> (unused_fetch_addr_n0 == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o) |-> (unused_fetch_addr_n0 == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_gnt_i) |-> (unused_fetch_addr_n0 == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i) |-> (unused_fetch_addr_n0 == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req) |-> (unused_fetch_addr_n0 == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_branch) |-> (unused_fetch_addr_n0 == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid) |-> (unused_fetch_addr_n0 == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (unused_fetch_addr_n0 == 1'b0));"
    }
]
```