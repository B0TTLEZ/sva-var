```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_q) |-> (instr_valid_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> ##1 (!instr_valid_id_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_clear_i) |-> ##1 (!instr_valid_id_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_instr_valid && id_in_ready_i && !pc_set_i) |-> ##1 (instr_valid_id_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!instr_valid_id_q) |-> (!instr_valid_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_q && !instr_valid_clear_i) |-> ##1 (instr_valid_id_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (rst_ni) |-> ##1 (!instr_valid_id_q));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_q) |-> (instr_new_id_q == instr_new_id_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_q && if_id_pipe_reg_we) |-> (instr_rdata_id_o == instr_out));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_valid_id_q && if_id_pipe_reg_we) |-> (pc_id_o == pc_if_o));"
    }
]
```