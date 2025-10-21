```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i) |-> (ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> (ic_scr_key_valid_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> ##1 $past(ic_scr_key_valid_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i && !ic_scr_key_req_o) |=> !ic_scr_key_req_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> !$isunknown(ic_tag_wdata_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> !$isunknown(ic_data_wdata_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> (ic_tag_write_o || ic_data_write_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o && ic_tag_write_o) |-> !$isunknown(ic_tag_addr_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o && ic_data_write_o) |-> !$isunknown(ic_data_addr_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> (ic_tag_req_o == {IC_NUM_WAYS{1'b1}} || ic_data_req_o == {IC_NUM_WAYS{1'b1}}));"
    }
]
```