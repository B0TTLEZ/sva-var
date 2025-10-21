```json
[
    {
        "original_code_slice" : "assign instr_rdata_id_o         = instr_out;",
        "mutation_code_slice" : "assign instr_rdata_alu_id_o     = instr_out;"
    },
    {
        "original_code_slice" : "assign instr_rdata_alu_id_o     = instr_out;",
        "mutation_code_slice" : "assign instr_rdata_id_o         = instr_out;"
    },
    {
        "original_code_slice" : "assign instr_fetch_err_o        = instr_err_out;",
        "mutation_code_slice" : "assign instr_fetch_err_plus2_o  = instr_err_out;"
    },
    {
        "original_code_slice" : "assign instr_fetch_err_plus2_o  = if_instr_err_plus2;",
        "mutation_code_slice" : "assign instr_fetch_err_o        = if_instr_err_plus2;"
    },
    {
        "original_code_slice" : "assign instr_is_compressed_id_o = instr_is_compressed_out;",
        "mutation_code_slice" : "assign illegal_c_insn_id_o      = instr_is_compressed_out;"
    },
    {
        "original_code_slice" : "assign illegal_c_insn_id_o      = illegal_c_instr_out;",
        "mutation_code_slice" : "assign instr_is_compressed_id_o = illegal_c_instr_out;"
    },
    {
        "original_code_slice" : "assign pc_id_o                  = pc_if_o;",
        "mutation_code_slice" : "assign pc_if_o                   = pc_id_o;"
    },
    {
        "original_code_slice" : "assign if_instr_rdata   = instr_skid_valid_q ? instr_skid_data_q : fetch_rdata;",
        "mutation_code_slice" : "assign if_instr_addr    = instr_skid_valid_q ? instr_skid_data_q : fetch_rdata;"
    },
    {
        "original_code_slice" : "assign if_instr_addr    = instr_skid_valid_q ? instr_skid_addr_q : fetch_addr;",
        "mutation_code_slice" : "assign if_instr_rdata   = instr_skid_valid_q ? instr_skid_addr_q : fetch_addr;"
    },
    {
        "original_code_slice" : "assign if_instr_bus_err = ~instr_skid_valid_q & fetch_err;",
        "mutation_code_slice" : "assign if_instr_valid   = ~instr_skid_valid_q & fetch_err;"
    }
]
```