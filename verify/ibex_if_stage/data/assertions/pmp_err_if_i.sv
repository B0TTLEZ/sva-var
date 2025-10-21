```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pmp_err_if_i) |-> (if_instr_pmp_err));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pmp_err_if_i) |-> (if_instr_err));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pmp_err_if_i) |-> (instr_fetch_err_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pmp_err_if_i) |-> (if_instr_valid));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pmp_err_if_i) |-> (fetch_valid));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pmp_err_if_i) |-> (instr_req_o));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pmp_err_if_i) |-> (instr_gnt_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pmp_err_if_i) |-> (instr_rvalid_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pmp_err_if_i) |-> (instr_bus_err_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pmp_err_if_i) |-> (if_instr_bus_err));"
    }
]
```