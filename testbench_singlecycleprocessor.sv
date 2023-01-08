// Code your testbench here
// or browse Examples
module tb();
  
  reg clk, reset;
  
  RISC_V_Processor RISCV(.clk(clk), .reset(reset) );
  
  initial
    begin
      
      $dumpfile("dump.vcd");
      $dumpvars();
      
      reset = 1'b1;
      clk = 1'b0;
      
      #2
      
      reset = 1'b0;
      
    end
  
  always
    begin
      #6
      clk = ~clk;
    end
  
endmodule
