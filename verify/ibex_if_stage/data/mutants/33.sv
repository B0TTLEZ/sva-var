```json
[
    {
        "original_code_slice": "instr_rdata_c_id_o       <= if_instr_rdata[15:0];",
        "mutation_code_slice": "instr_rdata_c_id_o       <= if_instr_rdata[14:0];"
    },
    {
        "original_code_slice": "assign unused_boot_addr = boot_addr_i[7:0];",
        "mutation_code_slice": "assign unused_boot_addr = boot_addr_i[6:0];"
    },
    {
        "original_code_slice": "assign unused_csr_mtvec = csr_mtvec_i[7:0];",
        "mutation_code_slice": "assign unused_csr_mtvec = csr_mtvec_i[8:1];"
    },
    {
        "original_code_slice": "fetch_addr_n = { boot_addr_i[31:8], 8'h80 };",
        "mutation_code_slice": "fetch_addr_n = { boot_addr_i[31:9], 7'h80 };"
    },
    {
        "original_code_slice": "exc_pc = { csr_mtvec_i[31:8], 8'h00 };",
        "mutation_code_slice": "exc_pc = { csr_mtvec_i[31:9], 7'h00 };"
    },
    {
        "original_code_slice": "exc_pc = { csr_mtvec_i[31:8], 1'b0, irq_vec, 2'b00 };",
        "mutation_code_slice": "exc_pc = { csr_mtvec_i[31:9], 1'b0, irq_vec, 2'b00 };"
    },
    {
        "original_code_slice": "prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd2 : 32'd4);",
        "mutation_code_slice": "prev_instr_addr_incr = pc_id_o + (instr_is_compressed_id_o ? 32'd1 : 32'd4);"
    },
    {
        "original_code_slice": "next_pc = fetch_addr + (instr_is_compressed_out ? 32'd2 : 32'd4);",
        "mutation_code_slice": "next_pc = fetch_addr + (instr_is_compressed_out ? 32'd3 : 32'd4);"
    },
    {
        "original_code_slice": "fetch_addr_n = { boot_addr_i[31:8], 8'h80 };",
        "mutation_code_slice": "fetch_addr_n = { boot_addr_i[31:7], 9'h100 };"
    },
    {
        "original_code_slice": "exc_pc = { csr_mtvec_i[31:8], 8'h00 };",
        "mutation_code_slice": "exc_pc = { csr_mtvec_i[31:7], 9'h100 };"
    }
]
```