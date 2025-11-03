module test_nested_conditions(  
    input logic clk,  
    input logic [3:0] mode,  
    input logic [7:0] data_in,  
    output logic [7:0] data_out  
);  
    logic [7:0] buffer [4];  
    logic [7:0] sum;  
      
    always_ff @(posedge clk) begin  
        if (mode[3]) begin  
            if (mode[2]) begin  
                buffer[0] <= data_in;  
            end else begin  
                buffer[1] <= data_in;  
            end  
        end else begin  
            if (mode[1]) begin  
                buffer[2] <= data_in;  
            end else begin  
                buffer[3] <= data_in;  
            end  
        end  
    end  
      
    always_comb begin  
        sum = 8'h0;  
        for (int i = 0; i < 4; i++) begin  
            sum = sum + buffer[i];  
        end  
    end  
      
    assign data_out = sum;  
endmodule