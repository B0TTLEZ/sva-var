```json
[
    {
        "original_code_slice" : "unique case (pc_mux_internal)\n      PC_BOOT: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };\n      PC_JUMP: fetch_addr_n = branch_target_ex_i;\n      PC_EXC:  fetch_addr_n = exc_pc;                       // set PC to exception handler\n      PC_ERET: fetch_addr_n = csr_mepc_i;                   // restore PC when returning from EXC\n      PC_DRET: fetch_addr_n = csr_depc_i;\n      PC_BP:   fetch_addr_n = BranchPredictor ? predict_branch_pc : { boot_addr_i[31:8], 8'h80 };\n      default: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };\n    endcase",
        "mutation_code_slice" : "unique case (pc_mux_internal)\n      PC_BOOT: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };\n      PC_JUMP: fetch_addr_n = branch_target_ex_i;\n      PC_EXC:  fetch_addr_n = exc_pc;                       // set PC to exception handler\n      PC_ERET: fetch_addr_n = csr_mepc_i;                   // restore PC when returning from EXC\n      PC_DRET: fetch_addr_n = csr_depc_i;\n      PC_BP:   fetch_addr_n = BranchPredictor ? predict_branch_pc : { boot_addr_i[31:8], 8'h80 };\n      default: fetch_addr_n = csr_mepc_i;                   // wrong transition to ERET address\n    endcase"
    },
    {
        "original_code_slice" : "unique case (exc_pc_mux_i)\n      EXC_PC_EXC:     exc_pc = { csr_mtvec_i[31:8], 8'h00                };\n      EXC_PC_IRQ:     exc_pc = { csr_mtvec_i[31:8], 1'b0, irq_vec, 2'b00 };\n      EXC_PC_DBD:     exc_pc = DmHaltAddr;\n      EXC_PC_DBG_EXC: exc_pc = DmExceptionAddr;\n      default:        exc_pc = { csr_mtvec_i[31:8], 8'h00                };\n    endcase",
        "mutation_code_slice" : "unique case (exc_pc_mux_i)\n      EXC_PC_EXC:     exc_pc = { csr_mtvec_i[31:8], 8'h00                };\n      EXC_PC_IRQ:     exc_pc = { csr_mtvec_i[31:8], 1'b0, irq_vec, 2'b00 };\n      EXC_PC_DBD:     exc_pc = DmHaltAddr;\n      EXC_PC_DBG_EXC: exc_pc = DmExceptionAddr;\n      default:        exc_pc = DmHaltAddr;                   // wrong transition to debug halt\n    endcase"
    },
    {
        "original_code_slice" : "assign pc_mux_internal =\n    (BranchPredictor && predict_branch_taken && !pc_set_i) ? PC_BP : pc_mux_i;",
        "mutation_code_slice" : "assign pc_mux_internal =\n    (BranchPredictor && predict_branch_taken && !pc_set_i) ? PC_EXC : pc_mux_i; // wrong transition to exception"
    },
    {
        "original_code_slice" : "assign prefetch_branch = branch_req | nt_branch_mispredict_i;",
        "mutation_code_slice" : "assign prefetch_branch = branch_req; // ignore mispredict signal"
    },
    {
        "original_code_slice" : "assign fetch_valid = fetch_valid_raw & ~nt_branch_mispredict_i;",
        "mutation_code_slice" : "assign fetch_valid = fetch_valid_raw; // ignore mispredict signal"
    },
    {
        "original_code_slice" : "assign if_instr_valid = fetch_valid | (instr_skid_valid_q & ~nt_branch_mispredict_i);",
        "mutation_code_slice" : "assign if_instr_valid = fetch_valid | instr_skid_valid_q; // ignore mispredict signal"
    },
    {
        "original_code_slice" : "assign branch_req  = pc_set_i | predict_branch_taken;",
        "mutation_code_slice" : "assign branch_req  = pc_set_i; // ignore branch prediction"
    },
    {
        "original_code_slice" : "assign instr_valid_id_d = (if_instr_valid & id_in_ready_i & ~pc_set_i) |\n                            (instr_valid_id_q & ~instr_valid_clear_i);",
        "mutation_code_slice" : "assign instr_valid_id_d = (if_instr_valid & id_in_ready_i) |\n                            (instr_valid_id_q & ~instr_valid_clear_i); // ignore pc_set_i"
    },
    {
        "original_code_slice" : "assign fetch_ready = id_in_ready_i & ~stall_dummy_instr & ~instr_skid_valid_q;",
        "mutation_code_slice" : "assign fetch_ready = id_in_ready_i & ~stall_dummy_instr; // ignore skid buffer"
    },
    {
        "original_code_slice" : "assign predict_branch_taken = predict_branch_taken_raw & ~instr_skid_valid_q & ~fetch_err;",
        "mutation_code_slice" : "assign predict_branch_taken = predict_branch_taken_raw & ~fetch_err; // ignore skid buffer"
    }
]
```