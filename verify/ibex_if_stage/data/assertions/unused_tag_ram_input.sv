```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> ($isunknown(unused_tag_ram_input) == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_req_o == 0) |-> (unused_tag_ram_input == '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_tag_write_o == 0) |-> (unused_tag_ram_input == '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i == 0) |-> (unused_tag_ram_input == '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_inval_i == 0) |-> (unused_tag_ram_input == '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ICache == 0) |-> (unused_tag_ram_input == '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_tag_ram_input == ic_tag_rdata_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> ($onehot0(unused_tag_ram_input) == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> ($isunknown(unused_tag_ram_input[0]) == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_tag_ram_input[IC_NUM_WAYS-1] == ic_tag_rdata_i[IC_NUM_WAYS-1]));"
    }
]
```