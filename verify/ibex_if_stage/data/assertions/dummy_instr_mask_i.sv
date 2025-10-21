```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_mask_i == 3'b000) |-> !dummy_instr_id_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_mask_i[0]) |-> dummy_instr_id_o |-> $past(instr_rdata_id_o[6:0]) inside {7'b0010011, 7'b0110011});"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_mask_i[1]) |-> dummy_instr_id_o |-> $past(instr_rdata_id_o[6:0]) inside {7'b0100011, 7'b0000011});"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_mask_i[2]) |-> dummy_instr_id_o |-> $past(instr_rdata_id_o[6:0]) inside {7'b1100011, 7'b1100111, 7'b1101111});"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_mask_i == 3'b111) |-> dummy_instr_en_i |-> ##[1:$] dummy_instr_id_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_mask_i != 3'b000) |-> dummy_instr_en_i |-> ##[1:$] dummy_instr_id_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) $onehot0(dummy_instr_mask_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_mask_i > 3'b111) |-> 0);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_seed_en_i && dummy_instr_mask_i != 0) |-> ##1 dummy_instr_id_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_mask_i == 3'b001 && dummy_instr_en_i) |-> ##[1:10] dummy_instr_id_o);"
    }
]
```