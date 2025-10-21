```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o) |-> (req_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o && !instr_gnt_i) |=> instr_req_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o && instr_gnt_i) |-> (instr_addr_o[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> ##1 !instr_req_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_inval_i) |-> ##1 !instr_req_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o && !icache_enable_i) |-> (instr_addr_o == prefetch_addr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o && icache_enable_i) |-> (instr_addr_o == fetch_addr_n));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o && BranchPredictor && predict_branch_taken) |-> (instr_addr_o == predict_branch_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o && nt_branch_mispredict_i) |-> (instr_addr_o == nt_branch_addr_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o) |-> !$isunknown(instr_addr_o));"
    }
]
```