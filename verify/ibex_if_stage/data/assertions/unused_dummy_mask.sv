```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_dummy_mask == 3'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_en_i) |-> (unused_dummy_mask == dummy_instr_mask_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!dummy_instr_en_i) |-> (unused_dummy_mask == 3'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_seed_en_i) |-> (unused_dummy_mask == dummy_instr_mask_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (insert_dummy_instr) |-> (unused_dummy_mask == dummy_instr_mask_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!insert_dummy_instr) |-> (unused_dummy_mask == 3'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_o) |-> (unused_dummy_mask == 3'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_o) |-> (unused_dummy_mask == 3'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (unused_dummy_mask == 3'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (stall_dummy_instr) |-> (unused_dummy_mask == dummy_instr_mask_i));"
    }
]
```