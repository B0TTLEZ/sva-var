```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o) |-> ##1 $stable(ic_tag_rdata_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> !$isunknown(ic_tag_wdata_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o && ic_tag_write_o) |-> ##1 (ic_tag_rdata_i == ic_tag_wdata_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o) |-> !$isunknown(ic_tag_addr_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o) |-> $onehot(ic_tag_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o) |-> ##1 !$isunknown(ic_tag_rdata_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o) |-> (ic_tag_addr_o < (1 << IC_INDEX_W)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o && !ic_tag_write_o) |-> ##1 (ic_tag_rdata_i != '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o) |-> (ic_tag_addr_o == $past(ic_tag_addr_o, 1)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o) |-> ##1 (ic_tag_rdata_i inside {[0:(1 << TagSizeECC)-1]}));"
    }
]
```