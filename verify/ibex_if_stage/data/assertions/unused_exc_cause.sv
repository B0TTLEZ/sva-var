```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) unused_exc_cause == 1'b0);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) unused_exc_cause == (|{exc_cause.irq_ext, exc_cause.irq_int}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) unused_exc_cause == $past(unused_exc_cause));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) unused_exc_cause == $stable(unused_exc_cause));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) unused_exc_cause !== 1'bx);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) unused_exc_cause !== 1'bz);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) unused_exc_cause == $onehot0({exc_cause.irq_ext, exc_cause.irq_int}));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) unused_exc_cause == $countones({exc_cause.irq_ext, exc_cause.irq_int}) == 0);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) unused_exc_cause == (exc_cause.irq_ext ^ exc_cause.irq_int));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) unused_exc_cause == (exc_cause.irq_ext | exc_cause.irq_int));"
    }
]
```