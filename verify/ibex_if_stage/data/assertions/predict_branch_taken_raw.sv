```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken_raw) |-> (fetch_valid));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken_raw) |-> !(fetch_err));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken_raw) |-> !(instr_skid_valid_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken_raw) |-> !(pc_set_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken_raw) |-> (fetch_rdata[1:0] != 2'b11) || (fetch_rdata[17] == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken_raw) |-> (fetch_rdata[6:0] inside {7'b1100011, 7'b1101111, 7'b1100111}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken_raw) |-> !(illegal_c_insn));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken_raw) |-> (predict_branch_pc == {fetch_addr[31:2] + {29'b0, fetch_rdata[31], fetch_rdata[7], fetch_rdata[30:25], fetch_rdata[11:8]}, 1'b0}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken_raw) |-> !(stall_dummy_instr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken_raw) |-> !(nt_branch_mispredict_i));"
    }
]
```