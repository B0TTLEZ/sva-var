```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_o) |-> !$isunknown(instr_rdata_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_fetch_err_o) |-> (instr_rdata_id_o == 0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_id_o) |-> (instr_rdata_id_o == gen_dummy_instr.dummy_instr_data));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o && !illegal_c_insn_id_o) |-> (instr_rdata_id_o[1:0] != 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!instr_is_compressed_id_o) |-> (instr_rdata_id_o[1:0] == 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (illegal_c_insn_id_o) |-> (instr_rdata_id_o[1:0] != 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_o && !instr_fetch_err_o && !dummy_instr_id_o) |-> (instr_rdata_id_o == instr_decompressed));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_o && !instr_fetch_err_o) |-> (instr_rdata_id_o == instr_rdata_alu_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_o && instr_is_compressed_id_o) |-> (instr_rdata_id_o[15:0] == instr_rdata_c_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |=> !instr_valid_id_o || (instr_rdata_id_o == $past(instr_rdata_id_o)));"
    }
]
```