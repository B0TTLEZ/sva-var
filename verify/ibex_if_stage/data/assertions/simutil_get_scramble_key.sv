```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (simutil_get_scramble_key) |-> (ic_scr_key_valid_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!ic_scr_key_valid_i) |-> (!$isunknown(simutil_get_scramble_key)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_inval_i) |-> (!$isunknown(simutil_get_scramble_key)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i) |-> (!$isunknown(simutil_get_scramble_key)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> (simutil_get_scramble_key));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> (!$isunknown(simutil_get_scramble_key)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o) |-> (!$isunknown(simutil_get_scramble_key)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o) |-> (!$isunknown(simutil_get_scramble_key)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_gnt_i) |-> (!$isunknown(simutil_get_scramble_key)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i) |-> (!$isunknown(simutil_get_scramble_key)));"
    }
]
```