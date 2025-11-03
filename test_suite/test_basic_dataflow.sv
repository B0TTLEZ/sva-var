module test_basic_dataflow(  
    input logic clk,  
    input logic rst,  
    input logic [7:0] data_in,  
    output logic [7:0] data_out  
);  
    logic [7:0] temp1, temp2, temp3;  
    logic enable;  
      

    //jhe
    always_ff @(posedge clk or posedge rst) begin  
        if (rst) begin  
            temp1 <= 8'h0;  
            temp2 <= 8'h0;  
            enable <= 1'b0;  
        end else begin  
            temp1 <= data_in;  
            temp2 <= temp1 + 8'h1;  
            enable <= (temp1 > 8'h10);  
        end  
    end  
      
    always_comb begin  
        if (enable) begin  
            temp3 = temp2 << 1;  
        end else begin  
            temp3 = temp2;  
        end  
    end  
      
    assign data_out = temp3;  
endmodule