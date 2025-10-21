```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i) |-> (ic_tag_req_o != 'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!icache_enable_i) |-> (ic_tag_req_o == 'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i) |-> (ic_data_req_o != 'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!icache_enable_i) |-> (ic_data_req_o == 'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i) |-> (instr_req_o == req_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i && icache_inval_i) |-> (ic_tag_write_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i && !icache_inval_i) |-> (!ic_tag_write_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i) |-> (prefetch_busy == if_busy_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i && instr_rvalid_i) |-> (icache_ecc_error_o == |ecc_err));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i && ic_scr_key_valid_i) |-> (ic_scr_key_req_o));"
    }
]
```