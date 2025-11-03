// test_verilog_fsm.v  
module test_verilog_fsm(  
    input clk,  
    input rst,  
    input start,  
    input stop,  
    output reg [1:0] state,  
    output reg busy  
);  
    // 状态定义(使用parameter而不是enum)  
    parameter IDLE = 2'b00;  
    parameter RUNNING = 2'b01;  
    parameter PAUSED = 2'b10;  
    parameter DONE = 2'b11;  
      
    reg [1:0] next_state;  
      
    // 组合逻辑:下一状态  
    always @(*) begin  
        case (state)  
            IDLE: begin  
                if (start)  
                    next_state = RUNNING;  
                else  
                    next_state = IDLE;  
            end  
            RUNNING: begin  
                if (stop)  
                    next_state = DONE;  
                else  
                    next_state = RUNNING;  
            end  
            PAUSED: begin  
                if (start)  
                    next_state = RUNNING;  
                else  
                    next_state = PAUSED;  
            end  
            DONE: begin  
                next_state = IDLE;  
            end  
            default: next_state = IDLE;  
        endcase  
    end  
      
    // 时序逻辑:状态更新  
    always @(posedge clk or posedge rst) begin  
        if (rst) begin  
            state <= IDLE;  
        end else begin  
            state <= next_state;  
        end  
    end  
      
    // 输出逻辑  
    always @(*) begin  
        busy = (state == RUNNING) || (state == PAUSED);  
    end  
endmodule