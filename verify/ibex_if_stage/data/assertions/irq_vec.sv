```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_int) |-> (irq_vec == ExcCauseIrqNm.lower_cause));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!exc_cause.irq_int) |-> (irq_vec == exc_cause.lower_cause));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_IRQ) |-> (irq_vec[4:0] == exc_cause.lower_cause[4:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_ext) |-> (irq_vec == exc_cause.lower_cause));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_int) |-> (irq_vec[4:0] == ExcCauseIrqNm.lower_cause[4:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_IRQ) |-> (irq_vec[4:0] == exc_cause.lower_cause[4:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_int) |-> (irq_vec[4:0] == ExcCauseIrqNm.lower_cause[4:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_ext) |-> (irq_vec[4:0] == exc_cause.lower_cause[4:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_pc_mux_i == EXC_PC_IRQ) |-> (irq_vec[4:0] == exc_cause.lower_cause[4:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (exc_cause.irq_int) |-> (irq_vec[4:0] == ExcCauseIrqNm.lower_cause[4:0]));"
    }
]
```