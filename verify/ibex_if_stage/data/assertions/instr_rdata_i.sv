```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i) |-> !$isunknown(instr_rdata_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i && MemECC) |-> (instr_rdata_i[38:32] == prim_secded_inv_39_32_enc(instr_rdata_i[31:0])));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i && !MemECC) |-> (instr_rdata_i[38:32] == 7'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i) |-> (instr_rdata_i === $past(instr_rdata_i) || !$past(instr_rvalid_i)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i && instr_req_o) |-> (instr_rdata_i === $past(instr_rdata_i,2) || !$past(instr_rvalid_i,2)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i && ICache) |-> (instr_rdata_i[31:0] === ic_data_rdata_i[0][31:0] || instr_rdata_i[31:0] === ic_data_rdata_i[1][31:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i && !ICache) |-> (instr_rdata_i[31:0] === $past(fetch_rdata)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i && instr_bus_err_i) |-> (instr_rdata_i === '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i && !instr_bus_err_i) |-> (instr_rdata_i !== '0 || instr_rdata_i[31:0] === '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i && BranchPredictor) |-> (instr_rdata_i[31:0] === $past(instr_skid_data_q) || !$past(instr_skid_valid_q)));"
    }
]
```