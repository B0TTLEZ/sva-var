```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o) |-> !$isunknown(ic_data_wdata_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o && icache_enable_i) |-> (ic_data_wdata_o == {LineSizeECC{1'b0}}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o && !icache_enable_i) |-> (ic_data_wdata_o == {LineSizeECC{1'b0}}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o && icache_inval_i) |-> (ic_data_wdata_o == {LineSizeECC{1'b0}}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o && !icache_inval_i) |-> (ic_data_wdata_o == {LineSizeECC{1'b0}}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o && ic_scr_key_valid_i) |-> (ic_data_wdata_o == {LineSizeECC{1'b0}}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o && !ic_scr_key_valid_i) |-> (ic_data_wdata_o == {LineSizeECC{1'b0}}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o && icache_ecc_error_o) |-> (ic_data_wdata_o == {LineSizeECC{1'b0}}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o && !icache_ecc_error_o) |-> (ic_data_wdata_o == {LineSizeECC{1'b0}}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o && prefetch_busy) |-> (ic_data_wdata_o == {LineSizeECC{1'b0}}));"
    }
]
```