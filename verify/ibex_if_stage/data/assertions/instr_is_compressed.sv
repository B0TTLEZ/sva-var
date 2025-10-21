```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed) |-> (instr_rdata_id_o[1:0] != 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!instr_is_compressed) |-> (instr_rdata_id_o[1:0] == 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed & fetch_valid) |-> (instr_rdata_c_id_o == instr_rdata_id_o[15:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed) |-> (instr_rdata_id_o[17:16] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed & illegal_c_insn_id_o) |-> (instr_rdata_id_o[15:13] inside {3'b010, 3'b011}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed) |-> (instr_rdata_alu_id_o == instr_rdata_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed & pc_set_i) |-> (pc_if_o[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed & fetch_err) |-> (instr_fetch_err_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed & ~fetch_err) |-> (instr_fetch_err_o == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed & BranchPredictor) |-> (instr_bp_taken_o == 1'b0));"
    }
]
```