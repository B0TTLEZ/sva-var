Here are 10 mutation results using the Constant Mutation operator:

```json
[
    {
        "original_code_slice" : "parameter int unsigned DmHaltAddr        = 32'h1A110800",
        "mutation_code_slice" : "parameter int unsigned DmHaltAddr        = 32'h1A110804"
    },
    {
        "original_code_slice" : "parameter int unsigned DmExceptionAddr   = 32'h1A110808",
        "mutation_code_slice" : "parameter int unsigned DmExceptionAddr   = 32'h1A11080C"
    },
    {
        "original_code_slice" : "parameter bit          DummyInstructions = 1'b0",
        "mutation_code_slice" : "parameter bit          DummyInstructions = 1'b1"
    },
    {
        "original_code_slice" : "parameter bit          ICache            = 1'b0",
        "mutation_code_slice" : "parameter bit          ICache            = 1'b1"
    },
    {
        "original_code_slice" : "parameter bit          ICacheECC         = 1'b0",
        "mutation_code_slice" : "parameter bit          ICacheECC         = 1'b1"
    },
    {
        "original_code_slice" : "parameter bit          PCIncrCheck       = 1'b0",
        "mutation_code_slice" : "parameter bit          PCIncrCheck       = 1'b1"
    },
    {
        "original_code_slice" : "parameter bit          ResetAll          = 1'b0",
        "mutation_code_slice" : "parameter bit          ResetAll          = 1'b1"
    },
    {
        "original_code_slice" : "parameter bit          BranchPredictor   = 1'b0",
        "mutation_code_slice" : "parameter bit          BranchPredictor   = 1'b1"
    },
    {
        "original_code_slice" : "parameter bit          MemECC            = 1'b0",
        "mutation_code_slice" : "parameter bit          MemECC            = 1'b1"
    },
    {
        "original_code_slice" : "fetch_addr_n = { boot_addr_i[31:8], 8'h80 }",
        "mutation_code_slice" : "fetch_addr_n = { boot_addr_i[31:8], 8'h84 }"
    }
]
```