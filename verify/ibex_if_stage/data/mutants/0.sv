```json
[
    {
        "original_code_slice": "assign instr_valid_id_d = (if_instr_valid & id_in_ready_i & ~pc_set_i) |\n                            (instr_valid_id_q & ~instr_valid_clear_i);",
        "mutation_code_slice": "// assign instr_valid_id_d = (if_instr_valid & id_in_ready_i & ~pc_set_i) |\n//                            (instr_valid_id_q & ~instr_valid_clear_i);"
    },
    {
        "original_code_slice": "assign instr_new_id_d   = if_instr_valid & id_in_ready_i;",
        "mutation_code_slice": "// assign instr_new_id_d   = if_instr_valid & id_in_ready_i;"
    },
    {
        "original_code_slice": "assign if_id_pipe_reg_we = instr_new_id_d;",
        "mutation_code_slice": "// assign if_id_pipe_reg_we = instr_new_id_d;"
    },
    {
        "original_code_slice": "assign instr_valid_id_o = instr_valid_id_q;",
        "mutation_code_slice": "// assign instr_valid_id_o = instr_valid_id_q;"
    },
    {
        "original_code_slice": "assign instr_new_id_o   = instr_new_id_q;",
        "mutation_code_slice": "// assign instr_new_id_o   = instr_new_id_q;"
    },
    {
        "original_code_slice": "assign pc_if_o     = if_instr_addr;",
        "mutation_code_slice": "// assign pc_if_o     = if_instr_addr;"
    },
    {
        "original_code_slice": "assign if_busy_o   = prefetch_busy;",
        "mutation_code_slice": "// assign if_busy_o   = prefetch_busy;"
    },
    {
        "original_code_slice": "assign if_instr_pmp_err = pmp_err_if_i |\n                            (if_instr_addr[1] & ~instr_is_compressed & pmp_err_if_plus2_i);",
        "mutation_code_slice": "// assign if_instr_pmp_err = pmp_err_if_i |\n//                            (if_instr_addr[1] & ~instr_is_compressed & pmp_err_if_plus2_i);"
    },
    {
        "original_code_slice": "assign if_instr_err = if_instr_bus_err | if_instr_pmp_err;",
        "mutation_code_slice": "// assign if_instr_err = if_instr_bus_err | if_instr_pmp_err;"
    },
    {
        "original_code_slice": "assign if_instr_err_plus2 = ((if_instr_addr[1] & ~instr_is_compressed & pmp_err_if_plus2_i) |\n                               fetch_err_plus2) & ~pmp_err_if_i;",
        "mutation_code_slice": "// assign if_instr_err_plus2 = ((if_instr_addr[1] & ~instr_is_compressed & pmp_err_if_plus2_i) |\n//                               fetch_err_plus2) & ~pmp_err_if_i;"
    }
]
```