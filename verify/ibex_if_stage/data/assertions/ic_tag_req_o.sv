```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ICache) |-> (ic_tag_req_o == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!ICache) |-> (ic_tag_req_o == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_inval_i) |-> (ic_tag_req_o == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i) |-> (ic_tag_req_o == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o) |-> (ic_tag_req_o == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o) |-> (ic_tag_req_o == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_req_o) |-> (ic_tag_req_o == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_ecc_error_o) |-> (ic_tag_req_o == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_busy) |-> (ic_tag_req_o == 1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid) |-> (ic_tag_req_o == 1'b1));"
    }
]
```