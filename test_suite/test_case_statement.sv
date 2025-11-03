module test_case_statement(  
    input logic [1:0] sel,  
    input logic [7:0] a, b, c, d,  
    output logic [7:0] result  
);  
    logic [7:0] intermediate;  
      
    always_comb begin  
        case (sel)  
            2'b00: intermediate = a;  
            2'b01: intermediate = b;  
            2'b10: intermediate = c;  
            2'b11: intermediate = d;  
        endcase  
    end  
      
    assign result = intermediate + 8'h1;  
endmodule