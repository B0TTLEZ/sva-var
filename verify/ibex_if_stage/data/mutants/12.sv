```json
[
    {
        "original_code_slice" : "always_ff @(posedge clk_i or negedge rst_ni) begin\n      if (!rst_ni) begin\n        instr_valid_id_q <= 1'b0;\n        instr_new_id_q   <= 1'b0;\n      end else begin\n        instr_valid_id_q <= instr_valid_id_d;\n        instr_new_id_q   <= instr_new_id_d;\n      end\n    end",
        "mutation_code_slice" : ""
    },
    {
        "original_code_slice" : "always_ff @(posedge clk_i or negedge rst_ni) begin\n      if (!rst_ni) begin\n        instr_skid_valid_q <= 1'b0;\n      end else begin\n        instr_skid_valid_q <= instr_skid_valid_d;\n      end\n    end",
        "mutation_code_slice" : ""
    },
    {
        "original_code_slice" : "always_ff @(posedge clk_i or negedge rst_ni) begin\n      if (!rst_ni) begin\n        prev_instr_seq_q <= 1'b0;\n      end else begin\n        prev_instr_seq_q <= prev_instr_seq_d;\n      end\n    end",
        "mutation_code_slice" : ""
    },
    {
        "original_code_slice" : "always_ff @(posedge clk_i or negedge rst_ni) begin\n      if (!rst_ni) begin\n        predicted_branch_live_q <= 1'b0;\n        mispredicted_q          <= 1'b0;\n      end else begin\n        predicted_branch_live_q <= predicted_branch_live_d;\n        mispredicted_q          <= mispredicted_d;\n      end\n    end",
        "mutation_code_slice" : ""
    },
    {
        "original_code_slice" : "always_ff @(posedge clk_i) begin\n      if (branch_req & predicted_branch) begin\n        predicted_branch_nt_pc_q <= next_pc;\n      end\n    end",
        "mutation_code_slice" : ""
    },
    {
        "original_code_slice" : "always_ff @(posedge clk_i or negedge rst_ni) begin\n      if (!rst_ni) begin\n        dummy_instr_id_o <= 1'b0;\n      end else if (if_id_pipe_reg_we) begin\n        dummy_instr_id_o <= insert_dummy_instr;\n      end\n    end",
        "mutation_code_slice" : ""
    },
    {
        "original_code_slice" : "always_comb begin : exc_pc_mux\n    irq_vec = exc_cause.lower_cause;\n\n    if (exc_cause.irq_int) begin\n      // All internal interrupts go to the NMI vector\n      irq_vec = ExcCauseIrqNm.lower_cause;\n    end\n\n    unique case (exc_pc_mux_i)\n      EXC_PC_EXC:     exc_pc = { csr_mtvec_i[31:8], 8'h00                };\n      EXC_PC_IRQ:     exc_pc = { csr_mtvec_i[31:8], 1'b0, irq_vec, 2'b00 };\n      EXC_PC_DBD:     exc_pc = DmHaltAddr;\n      EXC_PC_DBG_EXC: exc_pc = DmExceptionAddr;\n      default:        exc_pc = { csr_mtvec_i[31:8], 8'h00                };\n    endcase\n  end",
        "mutation_code_slice" : ""
    },
    {
        "original_code_slice" : "always_comb begin : fetch_addr_mux\n    unique case (pc_mux_internal)\n      PC_BOOT: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };\n      PC_JUMP: fetch_addr_n = branch_target_ex_i;\n      PC_EXC:  fetch_addr_n = exc_pc;                       // set PC to exception handler\n      PC_ERET: fetch_addr_n = csr_mepc_i;                   // restore PC when returning from EXC\n      PC_DRET: fetch_addr_n = csr_depc_i;\n      // Without branch predictor will never get pc_mux_internal == PC_BP. We still handle no branch\n      // predictor case here to ensure redundant mux logic isn't synthesised.\n      PC_BP:   fetch_addr_n = BranchPredictor ? predict_branch_pc : { boot_addr_i[31:8], 8'h80 };\n      default: fetch_addr_n = { boot_addr_i[31:8], 8'h80 };\n    endcase\n  end",
        "mutation_code_slice" : ""
    },
    {
        "original_code_slice" : "always_ff @(posedge clk_i or negedge rst_ni) begin\n      if (!rst_ni) begin\n        instr_rdata_id_o         <= '0;\n        instr_rdata_alu_id_o     <= '0;\n        instr_fetch_err_o        <= '0;\n        instr_fetch_err_plus2_o  <= '0;\n        instr_rdata_c_id_o       <= '0;\n        instr_is_compressed_id_o <= '0;\n        illegal_c_insn_id_o      <= '0;\n        pc_id_o                  <= '0;\n      end else if (if_id_pipe_reg_we) begin\n        instr_rdata_id_o         <= instr_out;\n        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.\n        instr_rdata_alu_id_o     <= instr_out;\n        instr_fetch_err_o        <= instr_err_out;\n        instr_fetch_err_plus2_o  <= if_instr_err_plus2;\n        instr_rdata_c_id_o       <= if_instr_rdata[15:0];\n        instr_is_compressed_id_o <= instr_is_compressed_out;\n        illegal_c_insn_id_o      <= illegal_c_instr_out;\n        pc_id_o                  <= pc_if_o;\n      end\n    end",
        "mutation_code_slice" : ""
    },
    {
        "original_code_slice" : "always_ff @(posedge clk_i) begin\n      if (if_id_pipe_reg_we) begin\n        instr_rdata_id_o         <= instr_out;\n        // To reduce fan-out and help timing from the instr_rdata_id flops they are replicated.\n        instr_rdata_alu_id_o     <= instr_out;\n        instr_fetch_err_o        <= instr_err_out;\n        instr_fetch_err_plus2_o  <= if_instr_err_plus2;\n        instr_rdata_c_id_o       <= if_instr_rdata[15:0];\n        instr_is_compressed_id_o <= instr_is_compressed_out;\n        illegal_c_insn_id_o      <= illegal_c_instr_out;\n        pc_id_o                  <= pc_if_o;\n      end\n    end",
        "mutation_code_slice" : ""
    }
]
```