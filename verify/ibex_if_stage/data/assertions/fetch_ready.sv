```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_ready) |-> (id_in_ready_i & ~stall_dummy_instr & ~instr_skid_valid_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_skid_valid_q) |-> !fetch_ready);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (stall_dummy_instr) |-> !fetch_ready);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (id_in_ready_i) |-> fetch_ready);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid & fetch_ready) |-> (id_in_ready_i & ~stall_dummy_instr & ~instr_skid_valid_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_ready & ~id_in_ready_i) |-> $past(instr_skid_valid_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_ready & ~id_in_ready_i) |-> $past(stall_dummy_instr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_ready & ~id_in_ready_i) |-> $past(instr_skid_valid_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_ready & ~id_in_ready_i) |-> $past(stall_dummy_instr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_ready & ~id_in_ready_i) |-> $past(instr_skid_valid_q));"
    }
]
```