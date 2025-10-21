```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_out) |-> (if_instr_rdata[1:0] != 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!instr_is_compressed_out) |-> (if_instr_rdata[1:0] == 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_out) |-> (instr_out[1:0] == 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (fetch_valid & ~fetch_err) |-> ##1 (instr_is_compressed_out == $past(instr_is_compressed)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_out) |-> (illegal_c_instr_out == $past(illegal_c_insn)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_out & if_id_pipe_reg_we) |-> (pc_id_o[1] == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_out & if_id_pipe_reg_we) |-> (instr_rdata_c_id_o == if_instr_rdata[15:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_out & if_id_pipe_reg_we) |-> (instr_rdata_id_o[1:0] == 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_out & if_id_pipe_reg_we) |-> (instr_rdata_alu_id_o[1:0] == 2'b11));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_is_compressed_out & if_id_pipe_reg_we) |-> (instr_fetch_err_plus2_o == 1'b0));"
    }
]
```