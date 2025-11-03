module test_increment_operations(  
    input logic clk,  
    input logic rst,  
    input logic enable,  
    output logic [7:0] counter  
);  
    logic [7:0] internal_counter;  
      
    always_ff @(posedge clk or posedge rst) begin  
        if (rst) begin  
            internal_counter <= 8'h0;  
        end else if (enable) begin  
            internal_counter <= internal_counter + 8'h1;  // 自增操作  
        end  
    end  
      
    assign counter = internal_counter;  
endmodule