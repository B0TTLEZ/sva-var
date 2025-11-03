module test_struct_union(  
    input logic clk,  
    input logic [7:0] data_in,  
    output logic [7:0] data_out  
);  
    typedef struct packed {  
        logic [3:0] field1;  
        logic [3:0] field2;  
    } my_struct_t;  
      
    my_struct_t reg_struct;  
      
    always_ff @(posedge clk) begin  
        reg_struct.field1 <= data_in[7:4];  
        reg_struct.field2 <= data_in[3:0];  
    end  
      
    assign data_out = {reg_struct.field2, reg_struct.field1};  
endmodule