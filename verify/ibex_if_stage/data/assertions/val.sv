```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_d) |-> (instr_valid_id_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_new_id_d) |-> (instr_new_id_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (instr_rdata_id_o == instr_out));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (instr_rdata_alu_id_o == instr_out));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (instr_fetch_err_o == instr_err_out));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (instr_fetch_err_plus2_o == if_instr_err_plus2));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (instr_rdata_c_id_o == if_instr_rdata[15:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (instr_is_compressed_id_o == instr_is_compressed_out));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (illegal_c_insn_id_o == illegal_c_instr_out));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_id_pipe_reg_we) |-> (pc_id_o == pc_if_o));"
    }
]
```