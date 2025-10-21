```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid) |-> !$isunknown(fetch_rdata));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i) |-> (fetch_rdata == instr_rdata_i[31:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_err) |-> (fetch_rdata == '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ICache && fetch_valid) |-> (fetch_rdata == ic_data_rdata_i[0][31:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid && !fetch_err) |-> (fetch_rdata[1:0] != 2'b11 || instr_is_compressed));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (BranchPredictor && predict_branch_taken) |-> (fetch_rdata == if_instr_rdata));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (MemECC && fetch_valid) |-> (fetch_rdata == instr_rdata_i[31:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid && !ICache) |-> (fetch_rdata == instr_rdata_i[31:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid && instr_skid_valid_q) |-> (fetch_rdata == instr_skid_data_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid && !instr_skid_valid_q) |-> (fetch_rdata == if_instr_rdata));"
    }
]
```