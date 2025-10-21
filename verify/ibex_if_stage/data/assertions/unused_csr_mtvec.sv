```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_csr_mtvec == csr_mtvec_i[7:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (csr_mtvec_i[7:0] == 8'h00) |-> (unused_csr_mtvec == 8'h00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (csr_mtvec_i[7:0] == 8'hFF) |-> (unused_csr_mtvec == 8'hFF));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (csr_mtvec_i[7:0] != unused_csr_mtvec) |-> $past(csr_mtvec_i[7:0]) != $past(unused_csr_mtvec));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (csr_mtvec_i[7:0] == unused_csr_mtvec));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (unused_csr_mtvec == $past(csr_mtvec_i[7:0])));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (csr_mtvec_i[7:0] == 8'hAA) |-> (unused_csr_mtvec == 8'hAA));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (csr_mtvec_i[7:0] == 8'h55) |-> (unused_csr_mtvec == 8'h55));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (unused_csr_mtvec == csr_mtvec_i[7:0]) |-> (1'b1));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (unused_csr_mtvec != csr_mtvec_i[7:0]) |-> (1'b0));"
    }
]
```