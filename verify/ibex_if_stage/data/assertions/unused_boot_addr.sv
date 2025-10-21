```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_boot_addr == boot_addr_i[7:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_mux_i == PC_BOOT) |-> (unused_boot_addr == 8'h00));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_boot_addr == boot_addr_i[31:24]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_boot_addr == boot_addr_i[15:8]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_boot_addr == boot_addr_i[23:16]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_boot_addr == boot_addr_i[7:0]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_boot_addr == boot_addr_i[31:24]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_boot_addr == boot_addr_i[15:8]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_boot_addr == boot_addr_i[23:16]));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> (unused_boot_addr == boot_addr_i[7:0]));"
    }
]
```