```json
[
    {
        "original_code_slice": "assign unused_boot_addr = boot_addr_i[7:0];",
        "mutation_code_slice": "assign unused_boot_addr = boot_addr_i[7:0]; #5"
    },
    {
        "original_code_slice": "assign unused_csr_mtvec = csr_mtvec_i[7:0];",
        "mutation_code_slice": "assign unused_csr_mtvec = csr_mtvec_i[7:0]; #10"
    },
    {
        "original_code_slice": "assign unused_exc_cause = |{exc_cause.irq_ext, exc_cause.irq_int};",
        "mutation_code_slice": "assign unused_exc_cause = |{exc_cause.irq_ext, exc_cause.irq_int}; #2"
    },
    {
        "original_code_slice": "assign csr_mtvec_init_o = (pc_mux_i == PC_BOOT) & pc_set_i;",
        "mutation_code_slice": "assign csr_mtvec_init_o = (pc_mux_i == PC_BOOT) & pc_set_i; #3"
    },
    {
        "original_code_slice": "assign instr_intg_err = |ecc_err;",
        "mutation_code_slice": "assign instr_intg_err = |ecc_err; #7"
    },
    {
        "original_code_slice": "assign instr_err        = instr_intg_err | instr_bus_err_i;",
        "mutation_code_slice": "assign instr_err        = instr_intg_err | instr_bus_err_i; #4"
    },
    {
        "original_code_slice": "assign instr_intg_err_o = instr_intg_err & instr_rvalid_i;",
        "mutation_code_slice": "assign instr_intg_err_o = instr_intg_err & instr_rvalid_i; #6"
    },
    {
        "original_code_slice": "assign prefetch_branch = branch_req | nt_branch_mispredict_i;",
        "mutation_code_slice": "assign prefetch_branch = branch_req | nt_branch_mispredict_i; #8"
    },
    {
        "original_code_slice": "assign prefetch_addr   = branch_req ? {fetch_addr_n[31:1], 1'b0} : nt_branch_addr_i;",
        "mutation_code_slice": "assign prefetch_addr   = branch_req ? {fetch_addr_n[31:1], 1'b0} : nt_branch_addr_i; #9"
    },
    {
        "original_code_slice": "assign fetch_valid = fetch_valid_raw & ~nt_branch_mispredict_i;",
        "mutation_code_slice": "assign fetch_valid = fetch_valid_raw & ~nt_branch_mispredict_i; #1"
    }
]
```