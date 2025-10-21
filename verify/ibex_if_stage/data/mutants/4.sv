```json
[
    {
        "original_code_slice": "if (exc_cause.irq_int) begin",
        "mutation_code_slice": "if (!exc_cause.irq_int) begin"
    },
    {
        "original_code_slice": "if (instr_skid_en) begin",
        "mutation_code_slice": "if (!instr_skid_en) begin"
    },
    {
        "original_code_slice": "if (fetch_valid & fetch_ready) begin",
        "mutation_code_slice": "if (fetch_valid | fetch_ready) begin"
    },
    {
        "original_code_slice": "if (predicted_branch_live_q) begin",
        "mutation_code_slice": "if (!predicted_branch_live_q) begin"
    },
    {
        "original_code_slice": "if (branch_req & predicted_branch) begin",
        "mutation_code_slice": "if (branch_req | predicted_branch) begin"
    },
    {
        "original_code_slice": "if (instr_skid_valid_q & ~id_in_ready_i & ~stall_dummy_instr)",
        "mutation_code_slice": "if (instr_skid_valid_q | ~id_in_ready_i | ~stall_dummy_instr)"
    },
    {
        "original_code_slice": "if (prev_instr_seq_q & (pc_if_o != prev_instr_addr_incr_buf))",
        "mutation_code_slice": "if (prev_instr_seq_q & (pc_if_o == prev_instr_addr_incr_buf))"
    },
    {
        "original_code_slice": "if (if_instr_addr[1] & ~instr_is_compressed & pmp_err_if_plus2_i)",
        "mutation_code_slice": "if (if_instr_addr[1] | ~instr_is_compressed | pmp_err_if_plus2_i)"
    },
    {
        "original_code_slice": "if (insert_dummy_instr) begin",
        "mutation_code_slice": "if (!insert_dummy_instr) begin"
    },
    {
        "original_code_slice": "if (fetch_err) begin",
        "mutation_code_slice": "if (!fetch_err) begin"
    }
]
```