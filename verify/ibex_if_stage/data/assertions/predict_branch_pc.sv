```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken) |-> !$isunknown(predict_branch_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken) |-> (predict_branch_pc[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken & fetch_valid) |-> (predict_branch_pc == fetch_addr + (instr_is_compressed_out ? 32'd2 : 32'd4)));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken) |-> (predict_branch_pc != 32'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken & pc_set_i) |-> (predict_branch_pc == branch_target_ex_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken & nt_branch_mispredict_i) |-> (predict_branch_pc == nt_branch_addr_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken & exc_pc_mux_i == EXC_PC_EXC) |-> (predict_branch_pc == {csr_mtvec_i[31:8], 8'h00}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken & exc_pc_mux_i == EXC_PC_IRQ) |-> (predict_branch_pc == {csr_mtvec_i[31:8], 1'b0, exc_cause.lower_cause, 2'b00}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken & exc_pc_mux_i == EXC_PC_DBD) |-> (predict_branch_pc == DmHaltAddr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (predict_branch_taken & exc_pc_mux_i == EXC_PC_DBG_EXC) |-> (predict_branch_pc == DmExceptionAddr));"
    }
]
```