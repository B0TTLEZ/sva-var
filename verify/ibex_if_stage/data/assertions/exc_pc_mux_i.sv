```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_EXC) |-> (exc_pc == {csr_mtvec_i[31:8], 8'h00}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_IRQ) |-> (exc_pc == {csr_mtvec_i[31:8], 1'b0, irq_vec, 2'b00}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_DBD) |-> (exc_pc == DmHaltAddr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_DBG_EXC) |-> (exc_pc == DmExceptionAddr));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i inside {EXC_PC_EXC, EXC_PC_IRQ, EXC_PC_DBD, EXC_PC_DBG_EXC}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i && (pc_mux_i == PC_EXC)) |-> (exc_pc_mux_i inside {EXC_PC_EXC, EXC_PC_IRQ}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_int) |-> (exc_pc_mux_i == EXC_PC_IRQ));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_ext) |-> (exc_pc_mux_i == EXC_PC_IRQ));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_IRQ) |-> (irq_vec == exc_cause.lower_cause));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_IRQ && exc_cause.irq_int) |-> (irq_vec == ExcCauseIrqNm.lower_cause));"
    }
]
```