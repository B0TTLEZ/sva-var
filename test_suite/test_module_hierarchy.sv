module adder(  
    input logic [7:0] a, b,  
    output logic [7:0] sum  
);  
    assign sum = a + b;  
endmodule  
  
module multiplier(  
    input logic [7:0] x, y,  
    output logic [15:0] product  
);  
    assign product = x * y;  
endmodule  
  
module test_module_hierarchy(  
    input logic [7:0] in1, in2, in3,  
    output logic [15:0] final_result  
);  
    logic [7:0] add_result;  
      
    adder u_adder(  
        .a(in1),  
        .b(in2),  
        .sum(add_result)  
    );  
      
    multiplier u_mult(  
        .x(add_result),  
        .y(in3),  
        .product(final_result)  
    );  
endmodule