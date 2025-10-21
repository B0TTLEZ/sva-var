```json
[
    {
        "original_code_slice": "assign instr_valid_id_d = (if_instr_valid & id_in_ready_i & ~pc_set_i) |\n                            (instr_valid_id_q & ~instr_valid_clear_i);",
        "mutation_code_slice": "assign instr_valid_id_d = (if_instr_valid & id_in_ready_i & ~pc_set_i) |\n                            (instr_valid_id_q <= #5 ~instr_valid_clear_i);"
    },
    {
        "original_code_slice": "assign instr_new_id_d   = if_instr_valid & id_in_ready_i;",
        "mutation_code_slice": "assign instr_new_id_d   = if_instr_valid <= #5 id_in_ready_i;"
    },
    {
        "original_code_slice": "assign if_id_pipe_reg_we = instr_new_id_d;",
        "mutation_code_slice": "assign if_id_pipe_reg_we = instr_new_id_d <= #5 1'b1;"
    },
    {
        "original_code_slice": "assign fetch_ready = id_in_ready_i & ~stall_dummy_instr & ~instr_skid_valid_q;",
        "mutation_code_slice": "assign fetch_ready = id_in_ready_i & ~stall_dummy_instr <= #5 ~instr_skid_valid_q;"
    },
    {
        "original_code_slice": "assign if_instr_valid = fetch_valid | (instr_skid_valid_q & ~nt_branch_mispredict_i);",
        "mutation_code_slice": "assign if_instr_valid = fetch_valid | (instr_skid_valid_q <= #5 ~nt_branch_mispredict_i);"
    },
    {
        "original_code_slice": "assign if_instr_rdata   = instr_skid_valid_q ? instr_skid_data_q : fetch_rdata;",
        "mutation_code_slice": "assign if_instr_rdata   = instr_skid_valid_q <= #5 instr_skid_data_q : fetch_rdata;"
    },
    {
        "original_code_slice": "assign if_instr_addr    = instr_skid_valid_q ? instr_skid_addr_q : fetch_addr;",
        "mutation_code_slice": "assign if_instr_addr    = instr_skid_valid_q <= #5 instr_skid_addr_q : fetch_addr;"
    },
    {
        "original_code_slice": "assign if_instr_bus_err = ~instr_skid_valid_q & fetch_err;",
        "mutation_code_slice": "assign if_instr_bus_err = ~instr_skid_valid_q <= #5 fetch_err;"
    },
    {
        "original_code_slice": "assign instr_bp_taken_d = instr_skid_valid_q ? instr_skid_bp_taken_q : predict_branch_taken;",
        "mutation_code_slice": "assign instr_bp_taken_d = instr_skid_valid_q <= #5 instr_skid_bp_taken_q : predict_branch_taken;"
    },
    {
        "original_code_slice": "assign fetch_ready = id_in_ready_i & ~stall_dummy_instr;",
        "mutation_code_slice": "assign fetch_ready = id_in_ready_i <= #5 ~stall_dummy_instr;"
    }
]
```