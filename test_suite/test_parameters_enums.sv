module test_parameters_enums #(  
    parameter int WIDTH = 8,  
    parameter int DEPTH = 4  
)(  
    input logic clk,  
    input logic [WIDTH-1:0] data_in,  
    output logic [WIDTH-1:0] data_out  
);  
    typedef enum logic [1:0] {  
        IDLE = 2'b00,  
        ACTIVE = 2'b01,  
        DONE = 2'b10  
    } state_t;  
      
    state_t current_state, next_state;  
    logic [WIDTH-1:0] buffer [DEPTH];  
      
    always_ff @(posedge clk) begin  
        current_state <= next_state;  
        if (current_state == ACTIVE) begin  
            buffer[0] <= data_in;  
        end  
    end  
      
    always_comb begin  
        case (current_state)  
            IDLE: next_state = ACTIVE;  
            ACTIVE: next_state = DONE;  
            DONE: next_state = IDLE;  
            default: next_state = IDLE;  
        endcase  
    end  
      
    assign data_out = buffer[0];  
endmodule