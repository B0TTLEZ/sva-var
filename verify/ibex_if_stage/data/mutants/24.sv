```json
[
    {
        "original_code_slice": "assign instr_valid_id_d = (if_instr_valid & id_in_ready_i & ~pc_set_i) |\n                            (instr_valid_id_q & ~instr_valid_clear_i);",
        "mutation_code_slice": "assign instr_valid_id_d = (if_instr_valid & id_in_ready_i & ~pc_set_i) |\n                            (instr_valid_id_q & ~instr_valid_clear_i);\nassign instr_valid_id_d = instr_valid_id_q;"
    },
    {
        "original_code_slice": "assign instr_new_id_d   = if_instr_valid & id_in_ready_i;",
        "mutation_code_slice": "assign instr_new_id_d   = if_instr_valid & id_in_ready_i;\nassign instr_new_id_d   = instr_new_id_q;"
    },
    {
        "original_code_slice": "assign if_instr_valid = fetch_valid | (instr_skid_valid_q & ~nt_branch_mispredict_i);",
        "mutation_code_slice": "assign if_instr_valid = fetch_valid | (instr_skid_valid_q & ~nt_branch_mispredict_i);\nassign if_instr_valid = fetch_valid;"
    },
    {
        "original_code_slice": "assign if_instr_rdata   = instr_skid_valid_q ? instr_skid_data_q : fetch_rdata;",
        "mutation_code_slice": "assign if_instr_rdata   = instr_skid_valid_q ? instr_skid_data_q : fetch_rdata;\nassign if_instr_rdata   = fetch_rdata;"
    },
    {
        "original_code_slice": "assign if_instr_addr    = instr_skid_valid_q ? instr_skid_addr_q : fetch_addr;",
        "mutation_code_slice": "assign if_instr_addr    = instr_skid_valid_q ? instr_skid_addr_q : fetch_addr;\nassign if_instr_addr    = fetch_addr;"
    },
    {
        "original_code_slice": "assign if_instr_bus_err = ~instr_skid_valid_q & fetch_err;",
        "mutation_code_slice": "assign if_instr_bus_err = ~instr_skid_valid_q & fetch_err;\nassign if_instr_bus_err = fetch_err;"
    },
    {
        "original_code_slice": "assign instr_bp_taken_d = instr_skid_valid_q ? instr_skid_bp_taken_q : predict_branch_taken;",
        "mutation_code_slice": "assign instr_bp_taken_d = instr_skid_valid_q ? instr_skid_bp_taken_q : predict_branch_taken;\nassign instr_bp_taken_d = predict_branch_taken;"
    },
    {
        "original_code_slice": "assign fetch_ready = id_in_ready_i & ~stall_dummy_instr & ~instr_skid_valid_q;",
        "mutation_code_slice": "assign fetch_ready = id_in_ready_i & ~stall_dummy_instr & ~instr_skid_valid_q;\nassign fetch_ready = id_in_ready_i;"
    },
    {
        "original_code_slice": "assign predict_branch_taken = predict_branch_taken_raw & ~instr_skid_valid_q & ~fetch_err;",
        "mutation_code_slice": "assign predict_branch_taken = predict_branch_taken_raw & ~instr_skid_valid_q & ~fetch_err;\nassign predict_branch_taken = predict_branch_taken_raw;"
    },
    {
        "original_code_slice": "assign branch_req  = pc_set_i | predict_branch_taken;",
        "mutation_code_slice": "assign branch_req  = pc_set_i | predict_branch_taken;\nassign branch_req  = pc_set_i;"
    }
]
```