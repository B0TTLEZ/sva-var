```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i & icache_inval_i) |-> ##[1:$] if_busy_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (req_i & ~instr_gnt_i) |-> if_busy_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_busy) |-> if_busy_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_busy_o) |-> (req_i | prefetch_busy));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (pc_set_i) |-> ##[1:$] if_busy_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i) |-> if_busy_o);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_busy_o & ~prefetch_busy) |-> req_i);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_busy_o & ~req_i) |-> prefetch_busy);"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_busy_o) |-> (instr_req_o | prefetch_busy));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (if_busy_o & ~instr_req_o) |-> prefetch_busy);"
    }
]
```