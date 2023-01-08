// Code your design here
module MUX (A, B, sel, out);
  
  input [63:0] A;
  input [63:0] B;
  input sel;
  output [63:0] out;
  
  assign out = (sel == 1'b0)? A : B;
  
endmodule

module Parser (ins, opcode, rd, funct3, rs1, rs2, funct7);

  input [31:0] ins;
  
  output [6:0] opcode;
  output [4:0] rd;
  output [2:0] funct3;
  output [4:0] rs1;
  output [4:0] rs2;
  output [6:0] funct7;
  
  assign opcode = ins[6:0];
  assign rd = ins[11:7];
  assign funct3 = ins[14:12];
  assign rs1 = ins[19:15];
  assign rs2 = ins[24:20];
  assign funct7 = ins[31:25];
  
endmodule

module ImmGen (ins, imm_data);
  
  input [31:0] ins;
  output reg [63:0] imm_data;
  
  always @ (ins)
    begin
      if (ins[6:5] == 2'b01)
        begin
          imm_data[4:0] = ins[11:7];
          imm_data[11:5] = ins[31:25];
        end

      else if (ins[6:5] == 2'b00)
        begin
          imm_data[11:0] = ins[31:20];
        end

      else if (ins[6:5] == 2'b11)
        begin
          imm_data[3:0] = ins[11:8];
          imm_data[9:4] = ins[30:25];
          imm_data[10] = ins[7];
          imm_data[11] = ins[31];
        end

      imm_data[63:12] = {52{(ins[31])}};
    end
endmodule


module registerFile(clk, reset, wtData, rs1, rs2, rd, regWrite, rd1, rd2,r1,r2,r3,r4,r22,r23,r20,r21,r19,r18);
  

  input clk, reset;
  input [63:0] wtData;
  input [4:0] rs1;
  input [4:0] rs2;
  input [4:0] rd;
  input regWrite;

  output reg [63:0] rd1;
  output reg [63:0] rd2;
  output reg [63:0] r1,r2,r3,r4,r22,r23,r20,r21,r19,r18;

  reg [63:0] register [31:0];




  initial

    begin

      register[0] = 64'd0;
register[1] = 64'd0;
register[2] = 64'd0;
register[3] = 64'd0;
register[4] = 64'd0;
register[5] = 64'd1;
register[6] = 64'd2;
register[7] = 64'd0;
register[8] = 64'd0;
register[9] = 64'd7;
register[10] = 64'd10;
register[11] = 64'd0;
register[12] = 64'd0;
register[13] = 64'd0;
register[14] = 64'd0;
register[15] = 64'd0;
register[16] = 64'd0;
register[17] = 64'd0;
register[18] = 64'd0;
register[19] = 64'd0;
register[20] = 64'd0;
register[21] = 64'd0;
register[22] = 64'd0;
register[23] = 64'd0;
register[24] = 64'd0;
register[25] = 64'd0;
register[26] = 64'd0;
register[27] = 64'd0;
register[28] = 64'd0;
register[29] = 64'd0;
register[30] = 64'd0;
register[31] = 64'd0;


    end




  always @ (*)

    begin

      rd1 = register[rs1];

      rd2 = register[rs2];




      if (reset == 1'b1)

        begin

          rd1 = 64'd0;

          rd2 = 64'd0;

        end

    end



  always @ (posedge clk)

    begin

      if (regWrite == 1'b1)

        begin

          register[rd] = wtData;

        end


    end
  
  always @ (*)

    begin

      r1=register[3];
      r2=register[4];
      r3=register[16];
      r4=register[6];
      r20=register[20];
      r21=register[21];
      r22=register[22];
      r23=register[23];
      r19= register[19];
      r18=register[20];
    end

endmodule
 


module ALU_64 (a, b, ALUop, result, zero, sign);
  
  input [63:0] a;
  input [63:0] b;
  input [3:0] ALUop;
  
  output reg [63:0] result;
  output reg zero;
  output reg sign;
  
  always @ (*)
    begin
  
      if (ALUop[3:0] == 4'b0000)
        begin
          result = a & b;
        end

      else if (ALUop[3:0] == 4'b0001)
        begin
          result = a | b;
        end

      else if (ALUop[3:0] == 4'b0010)
        begin
          result = a + b;
        end
      
      else if (ALUop[3:0] == 4'b0110)
        begin
          result = a - b;
        end
      
      else if (ALUop[3:0] == 4'b1100)
        begin
          result = ~(a | b);
        end
      
      zero = (result == 0)? 1'b1: 1'b0;
      
      sign = result[63];
      
    end
  
endmodule



module Instruction_Memory (Instr_Add, Instruction);
  
  input [63:0] Instr_Add;
  output [31:0] Instruction;
  
  reg [7:0] iMEM [7:0];
  
  initial
    begin 
      

      {iMEM[3], iMEM[2], iMEM[1], iMEM[0]} = 32'h00052303;
      {iMEM[7], iMEM[6], iMEM[5], iMEM[4]} = 32'h00600233;
      
/*      
{iMEM[3], iMEM[2], iMEM[1], iMEM[0]} = 32'h00000513;
{iMEM[7], iMEM[6], iMEM[5], iMEM[4]} = 32'h00500193;
{iMEM[11], iMEM[10], iMEM[9], iMEM[8]} = 32'h01800593;
{iMEM[15], iMEM[14], iMEM[13], iMEM[12]} = 32'h00300213;
{iMEM[19], iMEM[18], iMEM[17], iMEM[16]} = 32'h00900813;
{iMEM[23], iMEM[22], iMEM[21], iMEM[20]} = 32'h00400993;
{iMEM[27], iMEM[26], iMEM[25], iMEM[24]} = 32'h00800313;
{iMEM[31], iMEM[30], iMEM[29], iMEM[28]} = 32'h00800293;
{iMEM[35], iMEM[34], iMEM[33], iMEM[32]} = 32'h00652023;
{iMEM[39], iMEM[38], iMEM[37], iMEM[36]} = 32'h00352423;
{iMEM[43], iMEM[42], iMEM[41], iMEM[40]} = 32'h00452823;
{iMEM[47], iMEM[46], iMEM[45], iMEM[44]} = 32'h01052c23;
{iMEM[51], iMEM[50], iMEM[49], iMEM[48]} = 32'h00800713;
{iMEM[55], iMEM[54], iMEM[53], iMEM[52]} = 32'h00070913;
{iMEM[59], iMEM[58], iMEM[57], iMEM[56]} = 32'h405909b3;
{iMEM[63], iMEM[62], iMEM[61], iMEM[60]} = 32'h01250ab3;
{iMEM[67], iMEM[66], iMEM[65], iMEM[64]} = 32'h01350a33;
{iMEM[71], iMEM[70], iMEM[69], iMEM[68]} = 32'h000a2b03;
{iMEM[75], iMEM[74], iMEM[73], iMEM[72]} = 32'h000aab83;
{iMEM[79], iMEM[78], iMEM[77], iMEM[76]} = 32'h016bc863;
{iMEM[83], iMEM[82], iMEM[81], iMEM[80]} = 32'h00870713;
{iMEM[87], iMEM[86], iMEM[85], iMEM[84]} = 32'hfeb740e3;
{iMEM[91], iMEM[90], iMEM[89], iMEM[88]} = 32'h00000c63;
{iMEM[95], iMEM[94], iMEM[93], iMEM[92]} = 32'h017a2023;
{iMEM[99], iMEM[98], iMEM[97], iMEM[96]} = 32'h016aa023;
{iMEM[103], iMEM[102], iMEM[101], iMEM[100]} = 32'h40590933;
{iMEM[107], iMEM[106], iMEM[105], iMEM[104]} = 32'hfc0906e3;
{iMEM[111], iMEM[110], iMEM[109], iMEM[108]} = 32'hfc0956e3;
 
 {iMEM[167], iMEM[166], iMEM[165], iMEM[164]} = 32'h00032a03;
{iMEM[171], iMEM[170], iMEM[169], iMEM[168]} = 32'h0003aa83;
{iMEM[175], iMEM[174], iMEM[173], iMEM[172]} = 32'h00042b03;
  */
  end
  
  assign Instruction[7:0] = iMEM[Instr_Add];
  assign Instruction[15:8] = iMEM[Instr_Add + 1'b1];
  assign Instruction[23:16] = iMEM[Instr_Add + 2'b10];
  assign Instruction[31:24] = iMEM[Instr_Add + 2'b11];
  
endmodule



module Data_Memory (Mem_Addr, W_Data, clk, MemWrite, MemRead, Read_Data,d1,d2,d3,d4);
  
  input [63:0] Mem_Addr;
  input [63:0] W_Data;
  input clk, MemWrite, MemRead;
  
  output reg [63:0] Read_Data;
  output reg [63:0] d1,d2,d3,d4;
  
  reg [7:0] DMem [63:0];
  
  initial 
    begin
      DMem[0] = 8'b00000000;
      DMem[1] = 8'b00000000;
      DMem[2] = 8'b00000000;
      DMem[3] = 8'b00000000;
      DMem[4] = 8'b00000000;
      DMem[5] = 8'b00000000;
      DMem[6] = 8'b00000000;
      DMem[7] = 8'b00000000;
      DMem[8] = 8'b00000000;
      DMem[9] = 8'b00000000;
      DMem[10] = 8'd 8;
      DMem[11] = 8'b00000000;
      DMem[12] = 8'b00000000;
      DMem[13] = 8'b00000000;
      DMem[14] = 8'b00000000;
      DMem[15] = 8'b00000000;
      DMem[16] = 8'b00000000;
      DMem[17] = 8'b00000000;
      DMem[18] = 8'b00000000;
      DMem[19] = 8'b00000000;
      DMem[20] = 8'b00000000;
      DMem[21] = 8'b00000000;
      DMem[22] = 8'b00000000;
      DMem[23] = 8'b00000000;
      DMem[24] = 8'b00000000;
      DMem[25] = 8'b00000000;
      DMem[26] = 8'b00000000;
      DMem[27] = 8'b00000000;
      DMem[28] = 8'b00000000;
      DMem[29] = 8'b00000000;
      DMem[30] = 8'b00000000;
      DMem[31] = 8'b00000000;
      DMem[32] = 8'b00000000;
      DMem[33] = 8'b00000000;
      DMem[34] = 8'b00000000;
      DMem[35] = 8'b00000000;
      DMem[36] = 8'b00000000;
      DMem[37] = 8'b00000000;
      DMem[38] = 8'b00000000;
      DMem[39] = 8'b10000000;
      DMem[40] = 8'b10000000;
      DMem[41] = 8'b10000000;
      DMem[42] = 8'b00000000;
      DMem[43] = 8'b00000000;
      DMem[44] = 8'b00000000;
      DMem[45] = 8'b00000000;
      DMem[46] = 8'b00000000;
      DMem[47] = 8'b00000000;
      DMem[48] = 8'b00000000;
      DMem[49] = 8'b00000000;
      DMem[50] = 8'b00000000;
      DMem[51] = 8'b00000000;
      DMem[52] = 8'b00000000;
      DMem[53] = 8'b00000000;
      DMem[54] = 8'b00000000;
      DMem[55] = 8'b00000000;
      DMem[56] = 8'b00000000;
      DMem[57] = 8'b00000000;
      DMem[58] = 8'b00000000;
      DMem[59] = 8'b00000000;
      DMem[60] = 8'b00000000;
      DMem[61] = 8'b00000000;
      DMem[62] = 8'b00000000;
      DMem[63] = 8'b00000000;
    end
  
  always @ (posedge clk)
    
    begin
      
      if (MemWrite == 1'b1)
        begin
          
          DMem[Mem_Addr] = W_Data[7:0];
          DMem[Mem_Addr + 1'b1] = W_Data[15:8];
          DMem[Mem_Addr + 2'b10] = W_Data[23:16];
          DMem[Mem_Addr + 2'b11] = W_Data[31:24];
          DMem[Mem_Addr + 3'b100] = W_Data[39:32];
          DMem[Mem_Addr + 3'b101] = W_Data[47:40];
          DMem[Mem_Addr + 3'b110] = W_Data[55:48];
          DMem[Mem_Addr + 3'b111] = W_Data[63:56];
          
        end
      
    end
  
  always @ (*)
    
    begin
      
      if (MemRead == 1'b1)
        
        begin
          
          Read_Data[7:0] = DMem[Mem_Addr];
          Read_Data[15:8] = DMem[Mem_Addr + 1'b1];
          Read_Data[23:16] = DMem[Mem_Addr + 2'b10];
          Read_Data[31:24] = DMem[Mem_Addr + 2'b11];
          Read_Data[39:32] = DMem[Mem_Addr + 3'b100];
          Read_Data[47:40] = DMem[Mem_Addr + 3'b101];
          Read_Data[55:48] = DMem[Mem_Addr + 3'b110];
          Read_Data[63:56] = DMem[Mem_Addr + 3'b111];
          
        end
    end
  always @ (*)
    begin
      d1 = DMem[40];
      d2 = DMem[48];
      d3 = DMem[56];
      d4 = DMem[64];
      
    end
  
endmodule


module Program_Counter (PC_Write,clk, reset, PC_In, PC_Out);
  
  input clk, reset;
  input [63:0] PC_In;
  input PC_Write;
  
  output reg [63:0] PC_Out;
  
  
  always @ (posedge clk or posedge reset)
    begin
      
      if (reset == 1'b1)
        begin
          
          PC_Out = 64'd0;
        end
      
      else
        begin
          if(PC_Write)
          	PC_Out = PC_In;
        
        end
    
    end
  
endmodule




module Adder (a,b,out);
  
  input [63:0] a;
  input [63:0] b;
  output [63:0] out;
  
  assign out = a + b;
  
endmodule


module Control_Unit (Opcode, funct3, BEQ, BLT, BGE, MemRead, MemtoReg, ALUOp, MemWrite, ALUSrc, RegWrite);
  
  input [6:0] Opcode;
  input [2:0] funct3;
  
  output reg BEQ, BLT, BGE, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite;
  output reg [1:0] ALUOp;
  
  always @ (*)
    begin
      
      case(Opcode)
        
        7'b0110011: begin           // R-Type
          ALUSrc = 1'b0; 
          MemtoReg = 1'b0; 
          RegWrite = 1'b1; 
          MemRead = 1'b0; 
          MemWrite = 1'b0; 
          BEQ = 1'b0;
          BLT = 1'b0;
          BGE = 1'b0;
          ALUOp = 2'b10;
        end
        
        7'b0000011: begin          // I-Type (Load)
          ALUSrc = 1'b1; 
          MemtoReg = 1'b1; 
          RegWrite = 1'b1; 
          MemRead = 1'b1; 
          MemWrite = 1'b0; 
          BEQ = 1'b0;
          BLT = 1'b0;
          BGE = 1'b0;
          ALUOp = 2'b00;
        end
        
        7'b0100011: begin         // S-Type
          ALUSrc = 1'b1; 
          MemtoReg = 1'bx; 
          RegWrite = 1'b0; 
          MemRead = 1'b0; 
          MemWrite = 1'b1; 
          BEQ = 1'b0;
          BLT = 1'b0;
          BGE = 1'b0; 
          ALUOp = 2'b00;
        end
        
        7'b1100011: begin         // B-Type (BEQ)
          
          case(funct3)
            
            3'b000: begin
              ALUSrc = 1'b0; 
              MemtoReg = 1'bx; 
              RegWrite = 1'b0; 
              MemRead = 1'b0; 
              MemWrite = 1'b0; 
              BEQ = 1'b1;
              BLT = 1'b0;
              BGE = 1'b0; 
              ALUOp = 2'b01;
            end
            
            3'b100: begin
              ALUSrc = 1'b0; 
              MemtoReg = 1'bx; 
              RegWrite = 1'b0; 
              MemRead = 1'b0; 
              MemWrite = 1'b0; 
              BEQ = 1'b0;
              BLT = 1'b1;
              BGE = 1'b0; 
              ALUOp = 2'b01;
            end
            
            3'b101: begin
              ALUSrc = 1'b0; 
              MemtoReg = 1'bx; 
              RegWrite = 1'b0; 
              MemRead = 1'b0; 
              MemWrite = 1'b0; 
              BEQ = 1'b0;
              BLT = 1'b0;
              BGE = 1'b1; 
              ALUOp = 2'b01;
            end
          endcase
          
        end
        
        7'b0010011: begin         // I-Type (ADDI)
          ALUSrc = 1'b1; 
          MemtoReg = 1'b0; 
          RegWrite = 1'b1; 
          MemRead = 1'b0; 
          MemWrite = 1'b0; 
          BEQ = 1'b0;
          BLT = 1'b0;
          BGE = 1'b0; 
          ALUOp = 2'b00;
        end
        
        default: begin           // Default
          ALUSrc = 1'b0; 
          MemtoReg = 1'b0; 
          RegWrite = 1'b0; 
          MemRead = 1'b0; 
          MemWrite = 1'b0; 
          BEQ = 1'b0;
          BLT = 1'b0;
          BGE = 1'b0; 
          ALUOp = 2'b00;
        end
        
      endcase
      
    end
  
endmodule


module ALU_Control (ALUOp, Funct, Operation);
  
  input [1:0] ALUOp;
  input [3:0] Funct;
  
  output reg [3:0] Operation;
  
  always @ (*)
    begin
      
      case(ALUOp)
        
        2'b00: Operation = 4'b0010;    // I/S-Type
        
        2'b01: Operation = 4'b0110;    // SB-Type (BEQ)
        
        2'b10: begin                   // R-Type
          
          case(Funct)
            
            4'b0000: Operation = 4'b0010;
            
            4'b1000: Operation = 4'b0110;
            
            4'b0111: Operation = 4'b0000;
            
            4'b0110: Operation = 4'b0001;
            
            default: Operation = 4'b0000;
            
          endcase
          
        end
        
        default: Operation = 4'b0000;
        
      endcase
      
    end
  
endmodule


module Reg_IF_ID (IF_ID_Write,clk, reset, PC_In, ins, PC_Out, ins_out);
  
  input clk, reset;
  input [63:0] PC_In;
  input [31:0] ins;
  input IF_ID_Write;
  
  output reg [63:0] PC_Out;
  output reg [31:0] ins_out;
  
  always @ (posedge clk or posedge reset)
    begin
      
      if (reset == 1'b1)
        begin
          
          PC_Out = 64'd0;
          ins_out = 32'd0;
          
        end
      
      else
        begin
          if(IF_ID_Write)
            begin
          PC_Out = PC_In;
          ins_out = ins;
            end
        end
    end
endmodule


module Reg_ID_EX (MUX_Control_zero,clk, reset, WB_In, WB_Out, M_In, M_Out, EX_In, EX_Out, PC_In, PC_Out, RD1_In, RD1_Out, RD2_In, RD2_Out, Imm_In, Imm_Out, Funct_In, Funct_Out, Wr_Reg_In, Wr_Reg_Out, Rs1_In, Rs1_Out, Rs2_In, Rs2_Out);
  
  input clk, reset;
  input [63:0] PC_In, RD1_In, RD2_In, Imm_In;
  input [3:0] Funct_In;
  input [4:0] Wr_Reg_In, Rs1_In, Rs2_In;
  input [1:0] WB_In;
  input [4:0] M_In; 
  input [2:0] EX_In;
  input MUX_Control_zero;
  
  output reg [63:0] PC_Out, RD1_Out, RD2_Out, Imm_Out;
  output reg [3:0] Funct_Out;
  output reg [4:0] Wr_Reg_Out, Rs1_Out, Rs2_Out;
  output reg [1:0] WB_Out;
  output reg [4:0] M_Out; 
  output reg [2:0] EX_Out;
  
  always @ (posedge clk or posedge reset)
    begin
      
      if (reset == 1'b1 | MUX_Control_zero == 1)
        begin
          
          PC_Out = 64'd0;
          RD1_Out = 64'd0;
          RD2_Out = 64'd0;
          Imm_Out = 64'd0;
          Funct_Out = 4'd0;
          Wr_Reg_Out = 5'd0;
          Rs1_Out = 5'd0;
          Rs2_Out = 5'd0;
          WB_Out = 2'd0;
          M_Out = 5'd0;
          EX_Out = 3'd0;
          
        end
      
      else
        begin
          
          PC_Out = PC_In;
          RD1_Out = RD1_In;
          RD2_Out = RD2_In;
          Imm_Out = Imm_In;
          Funct_Out = Funct_In;
          Wr_Reg_Out = Wr_Reg_In;
          Rs1_Out = Rs1_In;
          Rs2_Out = Rs2_In;
          WB_Out = WB_In;
          M_Out = M_In;
          EX_Out = EX_In;
          
        end
      
    end
  
endmodule


module Reg_EX_MEM (clk, reset, WB_In, WB_Out, M_In, M_Out, PC_In, PC_Out, Zero_In, Zero_Out, Result_In, Result_Out, RD2_In, RD2_Out, Wr_Reg_In, Wr_Reg_Out, Sign_In, Sign_Out);
  
  input clk, reset, Sign_In;
  input [1:0] WB_In;
  input [4:0] M_In;
  input [63:0] PC_In;
  input Zero_In;
  input [63:0] Result_In;
  input [63:0] RD2_In;
  input [4:0] Wr_Reg_In;
  
  output reg [1:0] WB_Out;
  output reg [4:0] M_Out;
  output reg [63:0] PC_Out;
  output reg Zero_Out, Sign_Out;
  output reg [63:0] Result_Out;
  output reg [63:0] RD2_Out;
  output reg [4:0] Wr_Reg_Out;
  
  always @ (posedge clk or posedge reset)
    begin
      
      if (reset == 1'b1)
        begin
          
          WB_Out = 2'd0;
          M_Out = 5'd0;
          PC_Out = 64'd0;
          Zero_Out = 1'b0;
          Result_Out = 64'd0;
          RD2_Out = 64'd0;
          Wr_Reg_Out = 5'd0;
          Sign_Out = 1'b0;
          
        end
      
      else
        begin
          
          WB_Out = WB_In;
          M_Out = M_In;
          PC_Out = PC_In;
          Zero_Out = Zero_In;
          Result_Out = Result_In;
          RD2_Out = RD2_In;
          Wr_Reg_Out = Wr_Reg_In;
          Sign_Out = Sign_In;
          
        end
    end
endmodule


module Reg_MEM_WB (clk, reset, WB_In, WB_Out, RD_In, RD_Out, Result_In, Result_Out, Wr_Reg_In, Wr_Reg_Out);
  
  input clk, reset;
  input [1:0] WB_In;
  input [63:0] RD_In;
  input [63:0] Result_In;
  input [4:0] Wr_Reg_In;
  
  output reg [1:0] WB_Out;
  output reg [63:0] RD_Out;
  output reg [63:0] Result_Out;
  output reg [4:0] Wr_Reg_Out;
  
  always @ (posedge clk or posedge reset)
    begin
      
      if (reset == 1'b1)
        begin
          
          WB_Out = 2'd0;
          RD_Out = 64'd0;
          Result_Out = 64'd0;
          Wr_Reg_Out = 5'd0;
          
        end
      
      else
        begin
          
          WB_Out = WB_In;
          RD_Out = RD_In;
          Result_Out = Result_In;
          Wr_Reg_Out = Wr_Reg_In;
          
        end
      
    end
  
endmodule


module Forward_A (rd1, wtData, prev_result, sel_A, out_FwA);
  
  input [63:0] rd1, wtData, prev_result;
  input [1:0] sel_A;
  
  output reg [63:0] out_FwA;
  
  always @ (*)
    begin
      
      case(sel_A)
        
        2'b00: out_FwA = rd1;
        2'b01: out_FwA = wtData;
        2'b10: out_FwA = prev_result;
        
        default: out_FwA = 64'd0;
        
      endcase
      
    end
  
endmodule


module Forward_B (rd2, wtData, prev_result, sel_B, out_FwB);
  
  input [63:0] rd2, wtData, prev_result;
  input [1:0] sel_B;
  
  output reg [63:0] out_FwB;
  
  always @ (*)
    begin
      
      case(sel_B)
        
        2'b00: out_FwB = rd2;
        2'b01: out_FwB = wtData;
        2'b10: out_FwB = prev_result;
        
        default: out_FwB = 64'd0;
        
      endcase
      
    end
  
endmodule


module Forwarding_Unit (rs1, rs2, EM_rd, MW_rd, EM_regwt, MW_regwt, sel_A, sel_B);
  
  input [4:0] rs1, rs2, EM_rd, MW_rd;
  input EM_regwt, MW_regwt;
  
  output reg [1:0] sel_A, sel_B;
  
  always @ (*)
    begin
      
      if (EM_regwt == 1'b1 && EM_rd != 4'b0000)
        begin
          
          if (EM_rd == rs1)
            begin
              sel_A = 2'b10;
            end
          
          else if (EM_rd == rs2)
            begin
              sel_B = 2'b10;
            end
        end
      
      
      else if (MW_regwt == 1'b1 && MW_rd != 4'b0000)
        begin
          
          if (EM_rd != rs1 && MW_rd == rs1)
            begin
              sel_A = 2'b01;
            end
          
          else if (EM_rd != rs2 && MW_rd == rs2)
            begin
              sel_B = 2'b01;
            end
        end
      
      else
        begin
          sel_A = 2'b00;
          sel_B = 2'b00;
        end
      
    end
  
endmodule
  
module Hazard_detection_block(clk, ID_EX_memRead,Instructions,ID_EX_registerRt,IF_ID_Write,PC_Write,MUX_Control_zero);
  input clk;
  input ID_EX_memRead;
  input [31:0] Instructions;
  input [4:0] ID_EX_registerRt;
  output reg IF_ID_Write;
  output reg PC_Write;
  output reg MUX_Control_zero;
  
  always @(posedge clk)
    begin
      if((ID_EX_memRead) & (ID_EX_registerRt == Instructions[19:15]) & (ID_EX_registerRt == Instructions[24:20])) begin 
      IF_ID_Write= 0;
      PC_Write=0 ;
      MUX_Control_zero=1;
	   end else begin 
        IF_ID_Write = 1;
        PC_Write =1'b1 ;
        MUX_Control_zero =0;
       end
      
         end  
     
        
endmodule


module RISC_V_Processor (clk, reset);
  
  input clk, reset;
  
  wire [63:0] PC_Out;
  wire [63:0] out;
  wire [31:0] Instruction;
  wire [6:0] opcode;
  wire [4:0] rd;
  wire [2:0] funct3;
  wire [4:0] rs1;
  wire [4:0] rs2;
  wire [6:0] funct7;
  wire [63:0] imm_data;
  wire [63:0] rd1;
  wire [63:0] rd2;
  wire BEQ, BLT, BGE, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite;
  wire [1:0] ALUOp;
  wire [63:0] out_M1;
  wire [3:0] Operation;
  wire [63:0] result;
  wire zero;
  wire sign;
  wire [63:0] out_A2;
  wire [63:0] out_M2;
  wire [63:0] out_DM;
  wire [63:0] out_FwA, out_FwB;
  wire [63:0] wtData;
  wire [63:0] d1,d2,d3,d4;
  wire [63:0] r1,r2,r3,r4,r22,r23,r20,r21,r19,r18;
  
  wire [63:0] REG1_PCout;
  wire [31:0] REG1_INSout;
  wire [1:0] WB_Out, sel_A, sel_B;
  wire [4:0] M_Out;
  wire [2:0] EX_Out;
  wire [63:0] REG2_PCout;
  wire [63:0] REG2_RD1out;
  wire [63:0] REG2_RD2out;
  wire [63:0] Imm_Out;
  wire [3:0] Funct_Out;
  wire [4:0] REG2_Wr_Reg_Out, Rs1_Out, Rs2_Out;
  wire [1:0] WBout_S3;
  wire [4:0] Mout_S3;
  wire [63:0] PCout_S3;
  wire Zero_Out, sign_out;
  wire [63:0] Result_Out;
  wire [63:0] RD2out_S3;
  wire [4:0] RegOut_S3;
  wire [1:0] WBout_S4;
  wire [63:0] RDout_S4;
  wire [63:0] Resultout_S4;
  wire [4:0] RegOut_S4;

  wire IF_ID_Write, PC_Write;
  
  Program_Counter PC1(.PC_Write(PC_Write),.clk(clk), .reset(reset), .PC_In(out_M2), .PC_Out(PC_Out) );


  Adder A1 (.a(PC_Out), .b(64'd4), .out(out) );


  Instruction_Memory I1(.Instr_Add(PC_Out), .Instruction(Instruction) );
  
  Reg_IF_ID S1 (.IF_ID_Write(IF_ID_Write),.clk(clk), .reset(reset), .PC_In(PC_Out), .ins(Instruction), .PC_Out(REG1_PCout), .ins_out(REG1_INSout) );
  
  Parser P1( .ins(REG1_INSout), .opcode(opcode), .rd(rd), .funct3(funct3), .rs1(rs1), .rs2(rs2), .funct7(funct7) );
  
  Control_Unit C1(.Opcode(opcode), .funct3(funct3), .BEQ(BEQ), .BLT(BLT), .BGE(BGE), .MemRead(MemRead), .MemtoReg(MemtoReg), .ALUOp(ALUOp), .MemWrite(MemWrite), .ALUSrc(ALUSrc), .RegWrite(RegWrite));
  
  ImmGen G1 (.ins(REG1_INSout), .imm_data(imm_data) );
  
  Hazard_detection_block f6 (.clk(clk), .ID_EX_memRead(M_Out[3]),.Instructions(Instruction),.ID_EX_registerRt(Rs2_Out),.IF_ID_Write(IF_ID_Write),.PC_Write(PC_Write),.MUX_Control_zero(MUX_Control_zero));
  
  registerFile R1( .clk(clk), .reset(reset), .wtData(wtData), .rs1(rs1), .rs2(rs2), .rd(RegOut_S4), .regWrite(WBout_S4[1]), .rd1(rd1), .rd2(rd2) ,.r1(r1),.r2(r2),.r3(r3),.r4(r4),.r22(r22),.r23(r23),.r20(r20),.r21(r21),.r19(r19),.r18(r18));
  
  
  Reg_ID_EX S2 (.MUX_Control_zero(MUX_Control_zero),.clk(clk), .reset(reset), .WB_In({RegWrite, MemtoReg}), .WB_Out(WB_Out), .M_In({BEQ, BLT, BGE, MemRead, MemWrite}), .M_Out(M_Out), .EX_In({ALUOp, ALUSrc}), .EX_Out(EX_Out), .PC_In(REG1_PCout), .PC_Out(REG2_PCout), .RD1_In(rd1), .RD1_Out(REG2_RD1out), .RD2_In(rd2), .RD2_Out(REG2_RD2out), .Imm_In(imm_data), .Imm_Out(Imm_Out), .Funct_In({REG1_INSout[30], funct3}), .Funct_Out(Funct_Out), .Wr_Reg_In(rd), .Wr_Reg_Out(REG2_Wr_Reg_Out), .Rs1_In(rs1), .Rs1_Out(Rs1_Out), .Rs2_In(rs2), .Rs2_Out(Rs2_Out) );
  
  
  Forwarding_Unit FU (.rs1(Rs1_Out), .rs2(Rs2_Out), .EM_rd(RegOut_S3), .MW_rd(RegOut_S4), .EM_regwt(WB_Out[1]), .MW_regwt(WBout_S4[1]), .sel_A(sel_A), .sel_B(sel_B) );
  
  Forward_A FA (.rd1(REG2_RD1out), .wtData(wtData), .prev_result(Result_Out), .sel_A(sel_A), .out_FwA(out_FwA) );
  
  Forward_B FB (.rd2(REG2_RD2out), .wtData(wtData), .prev_result(Result_Out), .sel_B(sel_B), .out_FwB(out_FwB) );
  
  
  MUX M1(.A(out_FwB), .B(Imm_Out), .sel(EX_Out[0]), .out(out_M1));
  
  ALU_Control C2( .ALUOp(EX_Out[2:1]), .Funct(Funct_Out), .Operation(Operation) );
  
  Adder A2 (.a(REG2_PCout), .b(Imm_Out << 1), .out(out_A2) );
  
  ALU_64 AL( .a(out_FwA), .b(out_M1), .ALUop(Operation), .result(result), .zero(zero), .sign(sign) );
  
  
  
  Reg_EX_MEM S3 (.clk(clk), .reset(reset), .WB_In(WB_Out), .WB_Out(WBout_S3), .M_In(M_Out), .M_Out(Mout_S3), .PC_In(out_A2), .PC_Out(PCout_S3), .Zero_In(zero), .Zero_Out(Zero_Out), .Result_In(result), .Result_Out(Result_Out), .RD2_In(REG2_RD2out), .RD2_Out(RD2out_S3), .Wr_Reg_In(REG2_Wr_Reg_Out), .Wr_Reg_Out(RegOut_S3), .Sign_In(sign), .Sign_Out(sign_out) );
  
  MUX M2 (.A(out), .B(PCout_S3), .sel((Zero_Out & Mout_S3[4]) || (sign_out & Mout_S3[3]) || (~sign_out & Mout_S3[2])), .out(out_M2));
  
  
  Data_Memory D1(.Mem_Addr(Result_Out), .W_Data(RD2out_S3), .clk(clk), .MemWrite(Mout_S3[0]), .MemRead(Mout_S3[1]), .Read_Data(out_DM),.d1(d1),.d2(d2),.d3(d3),.d4(d4));
  
  Reg_MEM_WB S4 (.clk(clk), .reset(reset), .WB_In(WBout_S3), .WB_Out(WBout_S4), .RD_In(out_DM), .RD_Out(RDout_S4), .Result_In(Result_Out), .Result_Out(Resultout_S4), .Wr_Reg_In(RegOut_S3), .Wr_Reg_Out(RegOut_S4) );
  
  MUX M3 (.A(Resultout_S4), .B(RDout_S4), .sel(WBout_S4[0]), .out(wtData) );
  
  
endmodule
  