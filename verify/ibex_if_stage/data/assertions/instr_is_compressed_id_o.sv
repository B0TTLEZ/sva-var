```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o) |-> (instr_rdata_id_o[1:0] != 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!instr_is_compressed_id_o) |-> (instr_rdata_id_o[1:0] == 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o) |-> (instr_rdata_c_id_o == instr_rdata_id_o[15:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o) |-> (illegal_c_insn_id_o == illegal_c_instr_out));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o) |-> (instr_fetch_err_plus2_o == if_instr_err_plus2));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o) |-> (pc_id_o[1] == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o && instr_valid_id_o) |-> (instr_new_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o) |-> (instr_out[1:0] != 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o) |-> (if_instr_rdata[1:0] != 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o) |-> (fetch_rdata[1:0] != 2'b11));"
    }
]
```