```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> !$isunknown(ic_tag_wdata_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> (ic_tag_wdata_o == $past(ic_tag_wdata_o, 1)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o) |-> (ic_tag_wdata_o == $past(ic_tag_wdata_o, 1)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> (ic_tag_wdata_o != '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> (ic_tag_wdata_o == $past(ic_tag_wdata_o, 1)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> (ic_tag_wdata_o == $past(ic_tag_wdata_o, 1)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> (ic_tag_wdata_o == $past(ic_tag_wdata_o, 1)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> (ic_tag_wdata_o == $past(ic_tag_wdata_o, 1)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> (ic_tag_wdata_o == $past(ic_tag_wdata_o, 1)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> (ic_tag_wdata_o == $past(ic_tag_wdata_o, 1)));"
    }
]
```