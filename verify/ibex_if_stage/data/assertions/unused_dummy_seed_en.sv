```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> !$isunknown(unused_dummy_seed_en));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_en_i) |-> (unused_dummy_seed_en == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_seed_en_i) |-> (unused_dummy_seed_en == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid) |-> (unused_dummy_seed_en == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (id_in_ready_i) |-> (unused_dummy_seed_en == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (insert_dummy_instr) |-> (unused_dummy_seed_en == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (stall_dummy_instr) |-> (unused_dummy_seed_en == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (unused_dummy_seed_en == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_d) |-> (unused_dummy_seed_en == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d) |-> (unused_dummy_seed_en == 1'b0));"
    }
]
```