```json
[
    {
        "original_code_slice" : "assign instr_rdata_c_id_o       <= if_instr_rdata[15:0];",
        "mutation_code_slice" : "assign instr_rdata_c_id_o       <= {if_instr_rdata[7:0], if_instr_rdata[15:8]};"
    },
    {
        "original_code_slice" : "assign if_instr_rdata   = instr_skid_valid_q ? instr_skid_data_q : fetch_rdata;",
        "mutation_code_slice" : "assign if_instr_rdata   = instr_skid_valid_q ? {instr_skid_data_q[7:0], instr_skid_data_q[15:8], instr_skid_data_q[23:16], instr_skid_data_q[31:24]} : {fetch_rdata[7:0], fetch_rdata[15:8], fetch_rdata[23:16], fetch_rdata[31:24]};"
    },
    {
        "original_code_slice" : "assign fetch_rdata                = fetch_rdata                [31:0];",
        "mutation_code_slice" : "assign fetch_rdata                = {fetch_rdata[7:0], fetch_rdata[15:8], fetch_rdata[23:16], fetch_rdata[31:24]};"
    },
    {
        "original_code_slice" : "assign instr_rdata_id_o         <= instr_out;",
        "mutation_code_slice" : "assign instr_rdata_id_o         <= {instr_out[7:0], instr_out[15:8], instr_out[23:16], instr_out[31:24]};"
    },
    {
        "original_code_slice" : "assign instr_rdata_alu_id_o     <= instr_out;",
        "mutation_code_slice" : "assign instr_rdata_alu_id_o     <= {instr_out[7:0], instr_out[15:8], instr_out[23:16], instr_out[31:24]};"
    },
    {
        "original_code_slice" : "assign instr_decompressed = compressed_decoder_i.instr_o;",
        "mutation_code_slice" : "assign instr_decompressed = {compressed_decoder_i.instr_o[7:0], compressed_decoder_i.instr_o[15:8], compressed_decoder_i.instr_o[23:16], compressed_decoder_i.instr_o[31:24]};"
    },
    {
        "original_code_slice" : "assign instr_rdata_i       (instr_rdata_i[31:0]),",
        "mutation_code_slice" : "assign instr_rdata_i       ({instr_rdata_i[7:0], instr_rdata_i[15:8], instr_rdata_i[23:16], instr_rdata_i[31:24]}),"
    },
    {
        "original_code_slice" : "assign dummy_instr_data_o   (dummy_instr_data),",
        "mutation_code_slice" : "assign dummy_instr_data_o   ({dummy_instr_data[7:0], dummy_instr_data[15:8], dummy_instr_data[23:16], dummy_instr_data[31:24]}),"
    },
    {
        "original_code_slice" : "assign ic_data_wdata_o     (ic_data_wdata_o),",
        "mutation_code_slice" : "assign ic_data_wdata_o     ({ic_data_wdata_o[7:0], ic_data_wdata_o[15:8], ic_data_wdata_o[23:16], ic_data_wdata_o[31:24]}),"
    },
    {
        "original_code_slice" : "assign ic_tag_wdata_o      (ic_tag_wdata_o),",
        "mutation_code_slice" : "assign ic_tag_wdata_o      ({ic_tag_wdata_o[7:0], ic_tag_wdata_o[15:8], ic_tag_wdata_o[23:16], ic_tag_wdata_o[31:24]}),"
    }
]
```