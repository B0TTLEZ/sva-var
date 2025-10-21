```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i) |-> (ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!ic_scr_key_valid_i) |-> (!ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i && ICache) |-> (ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!ICache) |-> (!ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i && !ICache) |-> (!ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i) |-> ##1 (ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i && icache_enable_i) |-> (ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i && !icache_enable_i) |-> (!ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i && icache_inval_i) |-> (ic_scr_key_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i && !icache_inval_i) |-> (ic_scr_key_req_o));"
    }
]
```