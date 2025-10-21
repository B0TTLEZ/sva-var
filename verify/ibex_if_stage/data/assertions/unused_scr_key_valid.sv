```json
[
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (1'b1) |-> !$isunknown(unused_scr_key_valid));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ic_scr_key_valid_i) |-> (unused_scr_key_valid == ic_scr_key_valid_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (!ICache) |-> (unused_scr_key_valid == 1'b0));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (ICache) |-> (unused_scr_key_valid == ic_scr_key_valid_i));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_inval_i) |-> !$isunknown(unused_scr_key_valid));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (icache_enable_i) |-> !$isunknown(unused_scr_key_valid));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_req_o) |-> !$isunknown(unused_scr_key_valid));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_gnt_i) |-> !$isunknown(unused_scr_key_valid));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (instr_rvalid_i) |-> !$isunknown(unused_scr_key_valid));"
    },
    {
        "assertion": "assert property(@(posedge clk_i) disable iff(!rst_ni) (prefetch_busy) |-> !$isunknown(unused_scr_key_valid));"
    }
]
```