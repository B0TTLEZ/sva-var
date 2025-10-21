```json
[
    {
        "original_code_slice": "if (exc_cause.irq_int) begin\n      // All internal interrupts go to the NMI vector\n      irq_vec = ExcCauseIrqNm.lower_cause;\n    end",
        "mutation_code_slice": "// All internal interrupts go to the NMI vector\n      irq_vec = ExcCauseIrqNm.lower_cause;"
    },
    {
        "original_code_slice": "if (ResetAll) begin : g_instr_rdata_ra\n    always_ff @(posedge clk_i or negedge rst_ni) begin\n      if (!rst_ni) begin\n        instr_rdata_id_o         <= '0;\n        instr_rdata_alu_id_o     <= '0;\n        instr_fetch_err_o        <= '0;\n        instr_fetch_err_plus2_o  <= '0;\n        instr_rdata_c_id_o       <= '0;\n        instr_is_compressed_id_o <= '0;\n        illegal_c_insn_id_o      <= '0;\n        pc_id_o                  <= '0;\n      end else if (if_id_pipe_reg_we) begin\n        instr_rdata_id_o         <= instr_out;\n        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.\n        instr_rdata_alu_id_o     <= instr_out;\n        instr_fetch_err_o        <= instr_err_out;\n        instr_fetch_err_plus2_o  <= if_instr_err_plus2;\n        instr_rdata_c_id_o       <= if_instr_rdata[15:0];\n        instr_is_compressed_id_o <= instr_is_compressed_out;\n        illegal_c_insn_id_o      <= illegal_c_instr_out;\n        pc_id_o                  <= pc_if_o;\n      end\n    end\n  end",
        "mutation_code_slice": "if (ResetAll) begin : g_instr_rdata_ra\n    always_ff @(posedge clk_i or negedge rst_ni) begin\n      if (!rst_ni) begin\n        instr_rdata_id_o         <= '0;\n        instr_rdata_alu_id_o     <= '0;\n        instr_fetch_err_o        <= '0;\n        instr_fetch_err_plus2_o  <= '0;\n        instr_rdata_c_id_o       <= '0;\n        instr_is_compressed_id_o <= '0;\n        illegal_c_insn_id_o      <= '0;\n        pc_id_o                  <= '0;\n      end else if (if_id_pipe_reg_we) begin\n        instr_rdata_id_o         <= instr_out;\n        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.\n        instr_rdata_alu_id_o     <= instr_out;\n        instr_fetch_err_o        <= instr_err_out;\n        instr_fetch_err_plus2_o  <= if_instr_err_plus2;\n        instr_rdata_c_id_o       <= if_instr_rdata[15:0];\n        instr_is_compressed_id_o <= instr_is_compressed_out;\n        illegal_c_insn_id_o      <= illegal_c_instr_out;\n        pc_id_o                  <= pc_if_o;\n      end\n    end\n  end"
    },
    {
        "original_code_slice": "if (BranchPredictor) begin : g_branch_predictor",
        "mutation_code_slice": "begin : g_branch_predictor"
    },
    {
        "original_code_slice": "if (DummyInstructions) begin : gen_dummy_instr",
        "mutation_code_slice": "begin : gen_dummy_instr"
    },
    {
        "original_code_slice": "if (ICache) begin : gen_icache",
        "mutation_code_slice": "begin : gen_icache"
    },
    {
        "original_code_slice": "if (PCIncrCheck) begin : g_secure_pc",
        "mutation_code_slice": "begin : g_secure_pc"
    },
    {
        "original_code_slice": "if (MemECC) begin : g_mem_ecc",
        "mutation_code_slice": "begin : g_mem_ecc"
    },
    {
        "original_code_slice": "if (ResetAll) begin : g_bp_taken_ra",
        "mutation_code_slice": "begin : g_bp_taken_ra"
    },
    {
        "original_code_slice": "if (ResetAll) begin : g_instr_skid_ra",
        "mutation_code_slice": "begin : g_instr_skid_ra"
    },
    {
        "original_code_slice": "if (BranchPredictor) begin : g_branch_predictor_asserts",
        "mutation_code_slice": "begin : g_branch_predictor_asserts"
    }
]
```