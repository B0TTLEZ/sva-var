```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (PCIncrCheck) |-> !$isunknown(prev_instr_addr_incr_buf));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prev_instr_seq_q && !branch_req && !if_instr_err && !stall_dummy_instr) |-> (prev_instr_addr_incr_buf == (pc_id_o + (instr_is_compressed_id_o ? 32'd2 : 32'd4))));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (PCIncrCheck && prev_instr_seq_q) |-> (prev_instr_addr_incr_buf[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (PCIncrCheck && prev_instr_seq_q && instr_is_compressed_id_o) |-> (prev_instr_addr_incr_buf == pc_id_o + 32'd2));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (PCIncrCheck && prev_instr_seq_q && !instr_is_compressed_id_o) |-> (prev_instr_addr_incr_buf == pc_id_o + 32'd4));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (PCIncrCheck && prev_instr_seq_q) |-> (prev_instr_addr_incr_buf == prev_instr_addr_incr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (PCIncrCheck && pc_mismatch_alert_o) |-> (pc_if_o != prev_instr_addr_incr_buf));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (PCIncrCheck && !prev_instr_seq_q) |-> (prev_instr_addr_incr_buf == $past(prev_instr_addr_incr_buf)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (PCIncrCheck && branch_req) |-> (prev_instr_addr_incr_buf == $past(prev_instr_addr_incr_buf)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (PCIncrCheck && if_instr_err) |-> (prev_instr_addr_incr_buf == $past(prev_instr_addr_incr_buf)));"
    }
]
```