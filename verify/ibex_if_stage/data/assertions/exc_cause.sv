```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_ext) |-> (exc_pc_mux_i == EXC_PC_IRQ));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_int) |-> (exc_pc_mux_i == EXC_PC_IRQ));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.lower_cause == ExcCauseIrqNm.lower_cause) |-> (exc_cause.irq_int));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_IRQ) |-> (exc_cause.irq_ext || exc_cause.irq_int));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_ext && exc_cause.irq_int) |-> 0);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_ext) |-> (exc_pc[7:0] == {1'b0, exc_cause.lower_cause, 2'b00}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_int) |-> (exc_pc[7:0] == {1'b0, ExcCauseIrqNm.lower_cause, 2'b00}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.lower_cause inside {[0:31]}) |-> 1'b1);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_EXC) |-> (!exc_cause.irq_ext && !exc_cause.irq_int));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_IRQ) |-> (|{exc_cause.irq_ext, exc_cause.irq_int}));"
    }
]
```