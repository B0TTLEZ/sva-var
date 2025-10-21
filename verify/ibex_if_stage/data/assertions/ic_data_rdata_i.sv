```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_req_o) |-> ##[1:2] $stable(ic_data_rdata_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_write_o) |-> !$isunknown(ic_data_rdata_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i && ic_data_req_o) |-> ic_data_rdata_i inside {[0:'1]});"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_rdata_i[0] == 1'b1) |-> ##1 ic_data_rdata_i[0] == 1'b1);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_rdata_i[LineSizeECC-1:0] == '0) |-> !icache_ecc_error_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_rdata_i[LineSizeECC-1:0] != '0) |-> icache_ecc_error_o == $past(icache_ecc_error_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_rdata_i[LineSizeECC-1:0] == '1) |-> ##1 ic_data_rdata_i[LineSizeECC-1:0] == '1);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_rdata_i[LineSizeECC-1:0] != '0 && ic_data_rdata_i[LineSizeECC-1:0] != '1) |-> ##1 ic_data_rdata_i[LineSizeECC-1:0] != '0);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_rdata_i[LineSizeECC-1:0] == '0) |-> ##1 ic_data_rdata_i[LineSizeECC-1:0] == '0);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_data_rdata_i[LineSizeECC-1:0] != '0) |-> ##1 ic_data_rdata_i[LineSizeECC-1:0] != '0);"
    }
]
```