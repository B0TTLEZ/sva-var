```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_dummy_en == $past(dummy_instr_en_i)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_en_i) |-> (unused_dummy_en == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!dummy_instr_en_i) |-> (unused_dummy_en == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (unused_dummy_en == 1'b1) |-> (dummy_instr_en_i == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (unused_dummy_en == 1'b0) |-> (dummy_instr_en_i == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (unused_dummy_en !== 1'b0 && unused_dummy_en !== 1'b1) |-> $isunknown(unused_dummy_en));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (rst_ni) |-> ##1 (unused_dummy_en == $past(dummy_instr_en_i)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_en_i && !$past(dummy_instr_en_i)) |-> (unused_dummy_en == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!dummy_instr_en_i && $past(dummy_instr_en_i)) |-> (unused_dummy_en == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> !$isunknown(unused_dummy_en));"
    }
]
```