// Single Cycle MIPS
//=========================================================
// Input/Output Signals:
// positive-edge triggered         clk
// active low asynchronous reset   rst_n
// instruction memory interface    IR_addr, IR
// output for testing purposes     RF_writedata  
//=========================================================
// Wire/Reg Specifications:
// control signals             MemToReg, MemRead, MemWrite, 
//                             RegDST, RegWrite, Branch, 
//                             Jump, ALUSrc, ALUOp
// ALU control signals         ALUctrl
// ALU input signals           ALUin1, ALUin2
// ALU output signals          ALUresult, ALUzero
// instruction specifications  r, j, jal, jr, lw, sw, beq
// sign-extended signal        SignExtend
// MUX output signals          MUX_RegDST, MUX_MemToReg, 
//                             MUX_Src, MUX_Branch, MUX_Jump
// registers input signals     Reg_R1, Reg_R2, Reg_W, WriteData 
// registers                   Register
// registers output signals    ReadData1, ReadData2
// data memory contral signals CEN, OEN, WEN
// data memory output signals  ReadDataMem
// program counter/address     PCin, PCnext, JumpAddr, BranchAddr
//=======================================================================================================================================

module SingleCycle_MIPS( 
    clk,
    rst_n,
    IR_addr,
    IR,
    RF_writedata,
    ReadDataMem,
    CEN,
    WEN,
    A,
    ReadData2,
    OEN
);

//==== in/out declaration ===============================================================================================================
    //-------- processor ----------------------------------
    input         clk, rst_n;
    input  [31:0] IR;
    output [31:0] IR_addr, RF_writedata;
	
    //-------- data memory --------------------------------
    input  [31:0] ReadDataMem;  // read_data from memory
    output        CEN;  // chip_enable, 0 when you read/write data from/to memory
    output        WEN;  // write_enable, 0 when you write data into SRAM & 1 when you read data from SRAM
    output  [6:0] A;  // address
    output [31:0] ReadData2;  // write_data to memory
    output        OEN;  // output_enable, 0

//==== reg/wire declaration ==============================================================================================================
	
	wire [5:0] Opcode;
	assign Opcode = IR[31:26];
	//-------- INSTRUCTION for R -------------------------
	wire [4:0]rs;
	assign rs = IR[25:21];
	wire [4:0]rt;
	assign rt = IR[20:16];
	wire [4:0]rd;
	assign rd = IR[15:11];
	wire [4:0]shamt;
	assign shamt = IR[10:6];
	wire [5:0]funct;
	assign funct = IR[5:0];
	//--------- INSTRUCTION for I -------------------------
	wire [15:0]offset;
	assign offset = IR[15:0];
	//--------- INSTRUCTION for J -------------------------
	wire [25:0]address;
	assign address = IR[25:0];
	
	
	//------- PC ---------------
	wire [31:0] PC_nxt;
	//------- register -----------------
	wire [31:0] ReadData1;
	//------- control signal-------------
	wire RegDst, Branch, Jump, Jal, Jr, MemRead, MemtoReg,  MemWrite, ALUSrc, RegWrite;
	assign Jr = (Opcode==6'b000000&funct==6'b001000)? 1:0;
	wire [1:0] ALUOp;
	//-------- ALUop -------------------------
	wire [31:0] ALUSrc2;
	wire [31:0] ALUResult;
	assign A = ALUResult[8:2];
	//-------- ALUCtrl ------------------
	wire [3:0] ALUCtrl;
	//------- wire -----------------
	wire [4:0] W_R1;
	wire [4:0] W_R2;
	wire [31:0] W_D;
	wire [31:0] PCadd4;
	wire [31:0] S_EX1;
	wire [31:0] S_EX2;
	wire [27:0] addr_shf;
	wire [31:0] PCresult;
	wire PCSrc;
	wire [31:0]PC1;
	wire [31:0]PC2;
	wire [31:0]PC3;
	wire [31:0]JumpAddr;
	wire zero;
	reg [31:0] PC_in;
	assign IR_addr =  PC_in;
	assign JumpAddr = {PCadd4[31:28],addr_shf[27:0]};
	assign PCSrc = Branch & zero;
	
	
	
	
//==== combinational part ====================================================================================================================
	Control control(Opcode, RegDst, Branch, Jump, Jal, MemRead, MemtoReg, ALUOp, MemWrite, ALUSrc, RegWrite);
	MUX_2to1_5bit mux1(rt, rd, RegDst, W_R1);
	MUX_2to1_5bit jalmux1(W_R1, 5'b11111, Jal, W_R2);
	MUX_2to1 jalmux2(RF_writedata, PCadd4, Jal, W_D);
	MUX_2to1 jalmux3(PC2, JumpAddr, Jal, PC3);
	MUX_2to1 jrmux(PC3, ReadData1, Jr, PC_nxt);
	SignExtender_16to32 signextend (offset, S_EX1);
	LeftShifter_2bit leftshifter1(S_EX1, S_EX2);
	Adder32Bit PCadder(PC_in, 4, PCadd4);
	LeftShifter_26to28 leftshifter2(address,addr_shf);
	Adder32Bit adder(PCadd4, S_EX2, PCresult);
	MUX_2to1 mux2(ReadData2, S_EX1, ALUSrc, ALUSrc2);
	MUX_2to1 mux3(ALUResult, ReadDataMem, MemtoReg, RF_writedata);
	MUX_2to1 mux4(PCadd4, PCresult, PCSrc, PC1);
	MUX_2to1 mux5(PC1, JumpAddr, Jump, PC2); 
	ALU_Control alu_ctrl(funct, ALUOp, ALUCtrl);
	ALU_Core alucore(ReadData1 , ALUSrc2 , ALUCtrl , ALUResult , zero);
	
	assign CEN = 0;
	assign OEN = 0;
	assign WEN = (MemWrite==1)? 0 : 1;

//==== sequential part ====================================
	//-------- PC ------------------------------------
	always @(posedge clk or negedge rst_n )begin
	if (rst_n==1'b0)begin
	 PC_in <= 0;
	end
	else
	begin
	 PC_in <= PC_nxt;
	end
end	
	//-------- Register -------------------------------
	Register register1(clk, rst_n, RegWrite, rs, rt, W_R2, W_D, ReadData1, ReadData2);
	
	
		
	

//=========================================================
endmodule

module Adder32Bit(input1, input2, out);
  
  input [31:0] input1, input2;
  output [31:0] out;
  reg [31:0]out;
  
  
      always@(input1 or input2)
        begin
          
          out  = input1 + input2;
          
        end
    
endmodule

module ALU_Control(FunctField, ALUOp, ALUCtrl);
input [5:0]FunctField;
input [1:0]ALUOp;
output [3:0]ALUCtrl;
reg [3:0]ALUCtrl;

always@(FunctField or ALUOp)
begin
    if(ALUOp == 2'b10)      //'Arithmetic' Type Instructions
    begin
      case(FunctField)        
      //begin
        6'b100000: ALUCtrl = 4'b0010;    //ADDITION in 'R' Type
        6'b100010: ALUCtrl = 4'b0110;    //SUBTRACTION in 'R' Type
        6'b100100: ALUCtrl = 4'b0000;    //AND in 'R' Type
        6'b100101: ALUCtrl = 4'b0001;    //OR in 'R' Type
        6'b101010: ALUCtrl = 4'b0111;    //SLT in 'R' Type
		6'b100111: ALUCtrl = 4'b1100;	 //NOR in 'R' Type
		default ALUCtrl = 4'b0010;
     // end
    endcase
    end
    
    else if(ALUOp == 2'b00)     // 'LW/SW' Type Instructions
    begin
        ALUCtrl = 4'b0010;               //ADDITION irrespective of the FunctField.
    end
    
    else //(ALUOp == 2'b01)    //   'BEQ', 'BNE' Type Instructions
    begin
        ALUCtrl = 4'b0110;               //SUBTRACTION irrespective of the FunctField.
    end        
    

    
end   //always block 

endmodule  

module ALU_Core(ALUSrc1 , ALUSrc2 , ALUCtrl , ALUResult , Zero);
  input[31:0] ALUSrc1;
  input[31:0] ALUSrc2;
  input[3:0] ALUCtrl;
  
  output Zero;
  reg Zero;
    
  output [31:0]ALUResult;
  reg [31:0]ALUResult;
  
  
  always @(ALUSrc1 or ALUSrc2 or ALUCtrl)
    begin
          
          if(ALUCtrl == 4'b0010) //'add'
          begin
               ALUResult = ALUSrc1 + ALUSrc2; 
               if(ALUResult == 32'h0000)
               begin
                      Zero = 1'b1;
               end 
               else
                 begin
                      Zero = 1'b0;
                 end
          end
          
          else if(ALUCtrl == 4'b0110) // 'sub'
          begin
               ALUResult = ALUSrc1 - ALUSrc2; 
               if(ALUResult == 32'h0000)
               begin
                      Zero = 1'b1;
               end 
               else
                 begin
                      Zero = 1'b0;
                 end
          end
          
          else if(ALUCtrl == 4'b0000) // 'and'
          begin
               ALUResult = ALUSrc1 & ALUSrc2; 
               if(ALUResult == 32'h0000)
               begin
                      Zero = 1'b1;
               end 
               else
                 begin
                      Zero = 1'b0;
                 end
          end
               
          else if(ALUCtrl == 4'b0001) // 'or'
          begin
               ALUResult = ALUSrc1 | ALUSrc2; 
               if(ALUResult == 32'h0000)
               begin
                      Zero = 1'b1;
               end 
               else
                 begin
                      Zero = 1'b0;
                 end
          end     
          
          else //(ALUCtrl == 4'b0111) // 'slt'
          begin
               ALUResult = (ALUSrc1 < ALUSrc2)? 1:0; 
               if(ALUResult == 1)
               begin
                      Zero = 1'b1;
               end 
               else
                 begin
                      Zero = 1'b0;
                 end
          end
		  
		  
		/*  if(ALUCtrl == 3'b1100) // 'nor'
          begin
               ALUResult = ~(ALUSrc1 | ALUSrc2); 
               if(ALUResult == 32'h0000)
               begin
                      Zero = 1'b1;
               end 
               else
                 begin
                      Zero = 1'b0;
                 end
          end
        */
    end
  
endmodule

module Control(OpCode, RegDst, Branch, Jump, Jal, MemRead, MemtoReg, ALUOp, MemWrite, ALUSrc, RegWrite);

input [5:0] OpCode;
output reg RegDst, Branch, Jump, Jal,  MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite;
output reg [1:0]  ALUOp;

always @(*)



begin 
case(OpCode)
	6'b000000:  
	// R type
		begin
			  ALUOp = 2'b10;   
              RegDst = 1;
              Branch = 0;
              MemRead = 0;
              MemWrite = 0;
              ALUSrc = 0;
              MemtoReg = 0;
              RegWrite = 1;
			  Jump = 0;
			  Jal = 0;
			  
		end
	6'b100011:  
	// lw 
	
		begin
			  ALUOp = 2'b00;   
              RegDst = 0;
              Branch = 0;
              MemRead = 1;
              MemWrite = 0;
              ALUSrc = 1;
              MemtoReg = 1;
			  RegWrite = 1;
			  Jump = 0;
			  Jal = 0;
			  
		end
	6'b101011:  
	// sw
		begin
			  ALUOp = 2'b00;   
              RegDst = 0;  //irrelevant as data not being written into regfile.
              Branch = 0;
              MemRead = 0;
              MemWrite = 1;
              ALUSrc = 1;
              MemtoReg = 1; //irrelevant
              RegWrite = 0;
			  Jump = 0;
			  Jal = 0;
			  
		end
	6'b000100: // beq
		begin
			  ALUOp = 2'b01;   
              RegDst = 0;  //irrelevant
              Branch = 1;
              MemRead = 0;
              MemWrite = 0;
              ALUSrc = 0; 
              MemtoReg = 0; //irrelevant
              RegWrite = 0; //irrelevant
			  Jump = 0;
			  Jal = 0;
			  
		end
	6'b000010: 
	//j
		begin
			  ALUOp = 2'b10;   
              RegDst = 0;
              Branch = 0;
              MemRead = 0;
              MemWrite = 0;
              ALUSrc = 0;
              MemtoReg = 0;
              RegWrite = 0;
			  Jump = 1;
			  Jal = 0;
			 
			
		end
	6'b000011: //jal
		begin
			ALUOp = 2'b10;   
            RegDst = 0;
            Branch = 0;
            MemRead = 0;
            MemWrite = 0;
            ALUSrc = 0;
            MemtoReg = 0;
            RegWrite = 1;
			Jump = 0;
			Jal = 1;
			 
		end

	
	default:
		begin
		ALUOp = 2'b10;   
        RegDst = 0;
        Branch = 0;
              MemRead = 0;
              MemWrite = 0;
              ALUSrc = 0;
              MemtoReg = 0;
              RegWrite = 0;
			  Jump = 0;
			  Jal = 0;
			 
		end

endcase
end
endmodule

module LeftShifter_26to28(inData,outData);
  
  input [25:0]inData;
  output [27:0]outData;
  reg [27:0]outData;
  
  always@(inData)
    begin
      
      outData={2'b00,inData}<<2;
  
    end
    
endmodule    

module LeftShifter_2bit(inData,outData);
  
  input [31:0]inData;
  output [31:0]outData;
  reg [31:0]outData;
  
  always@(inData)
    begin
      
      outData=inData<<2;
  
    end
    
endmodule    

module MUX_2to1( input1 , input2, select, out );
  input [31:0] input1, input2;
  input select;
  output [31:0]out;
  reg [31:0]out;
  
  always @(input1 or input2 or select )
    begin 
      case(select)
       
          1'b0:  out=input1;
          1'b1:  out=input2;
          
      endcase
    end
 endmodule   
 
 module MUX_2to1_5bit( input1 , input2, select, out );
  input [4:0] input1, input2;
  input select;
  output [4:0]out;
  reg [4:0]out;
  
  always @(input1 or input2 or select )
    begin 
      case(select)
       
          1'b0:  out=input1;
          1'b1:  out=input2;
          
      endcase
    end
 endmodule   
 
 module SignExtender_16to32(inputData, outputData);
  
  input[15:0] inputData;
  output[31:0] outputData;
  reg [31:0] outputData;
  
  always@(inputData)
    begin
      
      outputData[15:0]  = inputData[15:0];
      outputData[31:16] = {16{inputData[15]}};
      
    end
endmodule

module Register(clk, rst_n, RegWrite, ReadReg1, ReadReg2, WriteReg, WriteData, ReadData1, ReadData2);

	input clk;
	input rst_n;
	input RegWrite;
	input [4:0] ReadReg1;
	input [4:0] ReadReg2;
	input [4:0] WriteReg;
	input [31:0] WriteData;
	output [31:0] ReadData1;
	output [31:0] ReadData2;
	integer i;
	reg [31:0] RegMemory[0:31];
	
assign ReadData1 = RegMemory[ReadReg1];
assign ReadData2 = RegMemory[ReadReg2];

always @(posedge clk or negedge rst_n)
	
	if (rst_n==1'b0)begin
		for(i=0;i<32;i=i+1)
			RegMemory[i] <= 0;
	end
	else
	begin
		if (RegWrite)begin
		RegMemory[WriteReg] <= WriteData;
		end
	end	
endmodule
