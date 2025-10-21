```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> !$isunknown(instr_skid_addr_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_en) |-> (instr_skid_addr_q == fetch_addr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & ~instr_skid_en) |-> $stable(instr_skid_addr_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & id_in_ready_i) |-> (instr_skid_addr_q == pc_if_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> (instr_skid_addr_q[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (nt_branch_mispredict_i & instr_skid_valid_q) |-> (instr_skid_addr_q == nt_branch_addr_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & ~stall_dummy_instr) |-> (instr_skid_addr_q == if_instr_addr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & predict_branch_taken) |-> (instr_skid_addr_q == predict_branch_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & branch_req) |-> (instr_skid_addr_q == fetch_addr_n));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q & pc_set_i) |-> (instr_skid_addr_q == exc_pc));"
    }
]
```