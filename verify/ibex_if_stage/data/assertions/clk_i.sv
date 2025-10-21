```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) ($stable(rst_ni)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o |-> ##[1:$] instr_gnt_i or !instr_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i |-> $past(instr_gnt_i,1)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i |-> ##1 !pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (branch_req |-> $stable(fetch_addr_n)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we |-> instr_new_id_d));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid |-> !nt_branch_mispredict_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_branch |-> (branch_req || nt_branch_mispredict_i)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_d |-> (if_instr_valid && id_in_ready_i && !pc_set_i) || (instr_valid_id_q && !instr_valid_clear_i)));"
    }
]
```