module test_verilog_counter(  
    input clk,  
    input rst,  
    input enable,  
    output reg [7:0] count,  
    output reg overflow  
);  
    reg [7:0] next_count;  
      
    // 组合逻辑:计算下一个计数值  
    always @(*) begin  
        if (enable) begin  
            next_count = count + 1;  
        end else begin  
            next_count = count;  
        end  
    end  
      
    // 时序逻辑:更新计数器  
    always @(posedge clk or posedge rst) begin  
        if (rst) begin  
            count <= 8'h00;  
            overflow <= 1'b0;  
        end else begin  
            count <= next_count;  
            overflow <= (count == 8'hFF) && enable;  
        end  
    end  
endmodule