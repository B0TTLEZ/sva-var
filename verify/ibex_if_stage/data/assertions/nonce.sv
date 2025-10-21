```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i) |-> (ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> (ic_scr_key_valid_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!ic_scr_key_valid_i) |-> (!ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_inval_i) |-> (ic_scr_key_req_o == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i && ic_scr_key_valid_i) |-> ##[1:10] ic_scr_key_req_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o && !ic_scr_key_valid_i) |=> $fell(ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> (icache_enable_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> (!$isunknown(ic_tag_addr_o)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> (!$isunknown(ic_data_addr_o)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_req_o) |-> (ic_tag_req_o != 0 || ic_data_req_o != 0));"
    }
]
```