```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o) |-> (instr_addr_o[1:0] == 2'b00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o) |-> !$isunknown(instr_addr_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> (instr_addr_o == fetch_addr_n));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o & icache_enable_i) |-> (instr_addr_o == prefetch_addr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o & ~icache_enable_i) |-> (instr_addr_o == fetch_addr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o & pc_mux_internal == PC_JUMP) |-> (instr_addr_o == branch_target_ex_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o & pc_mux_internal == PC_EXC) |-> (instr_addr_o == exc_pc));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o & pc_mux_internal == PC_ERET) |-> (instr_addr_o == csr_mepc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o & pc_mux_internal == PC_DRET) |-> (instr_addr_o == csr_depc_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o & pc_mux_internal == PC_BP) |-> (instr_addr_o == predict_branch_pc));"
    }
]
```