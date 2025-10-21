```json
[
    {
        "original_code_slice" : "logic [31:0]                 instr_rdata_id_o,         // instr for ID stage",
        "mutation_code_slice" : "logic [15:0]                 instr_rdata_id_o,         // instr for ID stage"
    },
    {
        "original_code_slice" : "logic [31:0]                 instr_rdata_alu_id_o,     // replicated instr for ID stage",
        "mutation_code_slice" : "logic [15:0]                 instr_rdata_alu_id_o,     // replicated instr for ID stage"
    },
    {
        "original_code_slice" : "logic [15:0]                 instr_rdata_c_id_o,       // compressed instr for ID stage",
        "mutation_code_slice" : "logic [7:0]                  instr_rdata_c_id_o,       // compressed instr for ID stage"
    },
    {
        "original_code_slice" : "logic [31:0]                 pc_if_o,",
        "mutation_code_slice" : "logic [15:0]                 pc_if_o,"
    },
    {
        "original_code_slice" : "logic [31:0]                 pc_id_o,",
        "mutation_code_slice" : "logic [15:0]                 pc_id_o,"
    },
    {
        "original_code_slice" : "logic [31:0]       fetch_addr_n;",
        "mutation_code_slice" : "logic [15:0]       fetch_addr_n;"
    },
    {
        "original_code_slice" : "logic [31:0]       prefetch_addr;",
        "mutation_code_slice" : "logic [15:0]       prefetch_addr;"
    },
    {
        "original_code_slice" : "logic [31:0]       fetch_rdata;",
        "mutation_code_slice" : "logic [15:0]       fetch_rdata;"
    },
    {
        "original_code_slice" : "logic [31:0]       fetch_addr;",
        "mutation_code_slice" : "logic [15:0]       fetch_addr;"
    },
    {
        "original_code_slice" : "logic [31:0]       instr_decompressed;",
        "mutation_code_slice" : "logic [15:0]       instr_decompressed;"
    }
]
```