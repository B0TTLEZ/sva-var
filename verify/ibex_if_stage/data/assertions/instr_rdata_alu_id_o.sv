```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_o) |-> !$isunknown(instr_rdata_alu_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_o) |-> (instr_rdata_alu_id_o == instr_rdata_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (instr_rdata_alu_id_o == instr_out));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_fetch_err_o) |-> (instr_rdata_alu_id_o == '0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (illegal_c_insn_id_o) |-> (instr_rdata_alu_id_o[1:0] != 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_id_o) |-> (instr_rdata_alu_id_o[1:0] != 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (dummy_instr_id_o) |-> (instr_rdata_alu_id_o inside {32'h00000013, 32'h00100073, 32'h00200073, 32'h00300073, 32'h00400073, 32'h00500073, 32'h00600073, 32'h00700073}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |=> (instr_rdata_alu_id_o == $past(instr_rdata_alu_id_o)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_clear_i) |=> (instr_rdata_alu_id_o == $past(instr_rdata_alu_id_o)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ResetAll && !rst_ni) |-> (instr_rdata_alu_id_o == '0));"
    }
]
```