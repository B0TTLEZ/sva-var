```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_req_o) |-> !$isunknown(ic_data_addr_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_req_o) |-> (ic_data_addr_o[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o) |-> (ic_data_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_inval_i) |-> ##[1:10] !$isunknown(ic_data_addr_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i && ic_data_req_o) |-> (ic_data_addr_o < (1 << IC_INDEX_W)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_req_o && !ic_data_write_o) |-> ##[1:5] $stable(ic_data_addr_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o) |-> ##1 !ic_data_write_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_req_o && $past(ic_data_req_o)) |-> (ic_data_addr_o == $past(ic_data_addr_o) + 1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_inval_i) |-> ##1 (ic_data_addr_o == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_req_o && !icache_enable_i) |-> $past(icache_enable_i));"
    }
]
```