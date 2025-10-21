```json
[
    {
        "original_code_slice": "assign prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd2 : 32'd4);",
        "mutation_code_slice": "assign prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd1 : 32'd4);"
    },
    {
        "original_code_slice": "assign prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd2 : 32'd4);",
        "mutation_code_slice": "assign prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd2 : 32'd8);"
    },
    {
        "original_code_slice": "assign prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd2 : 32'd4);",
        "mutation_code_slice": "assign prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd3 : 32'd4);"
    },
    {
        "original_code_slice": "assign prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd2 : 32'd4);",
        "mutation_code_slice": "assign prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd4 : 32'd4);"
    },
    {
        "original_code_slice": "assign next_pc = fetch_addr + (instr_is_compressed_out ? 32'd2 : 32'd4);",
        "mutation_code_slice": "assign next_pc = fetch_addr + (instr_is_compressed_out ? 32'd1 : 32'd4);"
    },
    {
        "original_code_slice": "assign next_pc = fetch_addr + (instr_is_compressed_out ? 32'd2 : 32'd4);",
        "mutation_code_slice": "assign next_pc = fetch_addr + (instr_is_compressed_out ? 32'd2 : 32'd8);"
    },
    {
        "original_code_slice": "assign next_pc = fetch_addr + (instr_is_compressed_out ? 32'd2 : 32'd4);",
        "mutation_code_slice": "assign next_pc = fetch_addr + (instr_is_compressed_out ? 32'd3 : 32'd4);"
    },
    {
        "original_code_slice": "assign next_pc = fetch_addr + (instr_is_compressed_out ? 32'd2 : 32'd4);",
        "mutation_code_slice": "assign next_pc = fetch_addr + (instr_is_compressed_out ? 32'd4 : 32'd4);"
    },
    {
        "original_code_slice": "assign fetch_addr_n = { boot_addr_i[31:8], 8'h80 };",
        "mutation_code_slice": "assign fetch_addr_n = { boot_addr_i[31:8], 8'h40 };"
    },
    {
        "original_code_slice": "assign fetch_addr_n = { boot_addr_i[31:8], 8'h80 };",
        "mutation_code_slice": "assign fetch_addr_n = { boot_addr_i[31:8], 8'hC0 };"
    }
]
```