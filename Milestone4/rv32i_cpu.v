//
//  Author: Prof. Taeweon Suh
//          Computer Science & Engineering
//          Korea University
//  Date: July 14, 2020
//  Description: Skeleton design of RV32I Single-cycle CPU
//
    // ###### Kyumin Kim: Start #######

    // ###### Kyumin Kim: End #######

`timescale 1ns/1ns
`define simdelay 1

module rv32i_cpu (
		      input         clk, reset,
            output [31:0] pc,		  		// program counter for instruction fetch
            // ###### Kyumin Kim: Start #######
            input  [31:0] inst, 			// incoming instruction
            // ###### Kyumin Kim: End #######
            output        Memwrite, 	// 'memory write' control signal
            output [31:0] Memaddr,  	// memory address 
            output [31:0] MemWdata, 	// data to write to memory
            input  [31:0] MemRdata); 	// data read from memory

  wire        auipc, lui;
    // ###### Kyumin Kim: Start #######
  wire        alusrc_dec;
    // ###### Kyumin Kim: End #######
  wire [4:0]  alucontrol;
  wire        regwrite;
  wire        memtoreg, memwrite;
  wire        branch, jal, jalr;
	// ###### Kyumin Kim: Start #######
  reg [31:0] inst_fetch;    
  wire stall;
   // ###### Kyumin Kim: End #######


  // assign Memwrite = memwrite ;
  
    // ###### Kyumin Kim: Start #######
    //always @(posedge clk)
    always @(posedge clk)
    begin
      if(stall) inst_fetch <= inst_fetch;
      else  inst_fetch <= inst;   // IF/ID instruction at posedge
    end
    // ###### Kyumin Kim: End #######


  // Instantiate Controller
  controller i_controller(
      // ###### Kyumin Kim: Start #######
      .opcode		(inst_fetch[6:0]), 
		.funct7		(inst_fetch[31:25]), 
		.funct3		(inst_fetch[14:12]), 
        // ###### Kyumin Kim: End #######
		.auipc		(auipc),
		.lui			(lui),
		.memtoreg	(memtoreg),
		.memwrite	(memwrite),
		.branch		(branch),
		.alusrc		(alusrc_dec),
		.regwrite	(regwrite),
		.jal			(jal),
		.jalr			(jalr),
		.alucontrol	(alucontrol));

  // Instantiate Datapath
  datapath i_datapath(
		.clk				(clk),
		.reset			(reset),
		.auipc			(auipc),
		.lui				(lui),
		.memtoreg		(memtoreg),
		.memwrite		(memwrite),
		.branch			(branch),
		 // ###### Kyumin Kim: Start #######
		.alusrc_dec			(alusrc_dec),
        // ###### Kyumin Kim: End #######
		.regwrite		(regwrite),
		.jal				(jal),
		.jalr				(jalr),
		.alucontrol_dec		(alucontrol),
		.pc				(pc),
		// ###### Kyumin Kim: Start #######
		.inst				(inst_fetch),
		// ###### Kyumin Kim: End #######
		.aluout_mem			(Memaddr), 
		.MemWdata_mem		(MemWdata),
        // ###### Kyumin Kim: Start #######
        .memwrite_ (Memwrite),
		.MemRdata_mem		(MemRdata),
    .stall_exec     (stall));
        // ###### Kyumin Kim: End #######

endmodule


//
// Instruction Decoder 
// to generate control signals for datapath
//
module controller(input  [6:0] opcode,
                  input  [6:0] funct7,
                  input  [2:0] funct3,
                  output       auipc,
                  output       lui,
                  output       alusrc,
                  output [4:0] alucontrol,
                  output       branch,
                  output       jal,
                  output       jalr,
                  output       memtoreg,
                  output       memwrite,
                  output       regwrite);

	maindec i_maindec(
		.opcode		(opcode),
		.auipc		(auipc),
		.lui			(lui),
		.memtoreg	(memtoreg),
		.memwrite	(memwrite),
		.branch		(branch),
		.alusrc		(alusrc),
		.regwrite	(regwrite),
		.jal			(jal),
		.jalr			(jalr));

	aludec i_aludec( 
		.opcode     (opcode),
		.funct7     (funct7),
		.funct3     (funct3),
		.alucontrol (alucontrol));


endmodule


//
// RV32I Opcode map = Inst[6:0]
//
`define OP_R			7'b0110011
`define OP_I_ARITH	7'b0010011
`define OP_I_LOAD  	7'b0000011
`define OP_I_JALR  	7'b1100111
`define OP_S			7'b0100011
`define OP_B			7'b1100011
`define OP_U_LUI		7'b0110111
`define OP_J_JAL		7'b1101111
`define OP_U_AUIPC	7'b0010111			//ADDED for auipc


//
// Main decoder generates all control signals except alucontrol 
//
//
module maindec(input  [6:0] opcode,
               output       auipc,
               output       lui,
               output       regwrite,
               output       alusrc,
               output       memtoreg, memwrite,
               output       branch, 
               output       jal,
               output       jalr);

  reg [8:0] controls;

  assign {auipc, lui, regwrite, alusrc, 
			 memtoreg, memwrite, branch, jal, 
			 jalr} = controls;

  always @(*)
  begin
    case(opcode)
      `OP_R: 			controls <= #`simdelay 9'b0010_0000_0; // R-type
      `OP_I_ARITH: 	controls <= #`simdelay 9'b0011_0000_0; // I-type Arithmetic
      `OP_I_LOAD: 	controls <= #`simdelay 9'b0011_1000_0; // I-type Load
      `OP_S: 			controls <= #`simdelay 9'b0001_0100_0; // S-type Store
      `OP_B: 			controls <= #`simdelay 9'b0000_0010_0; // B-type Branch
      `OP_U_LUI: 		controls <= #`simdelay 9'b0111_0000_0; // LUI
      `OP_J_JAL: 		controls <= #`simdelay 9'b0011_0001_0; // JAL
		`OP_I_JALR: 	controls <= #`simdelay 9'b0011_0000_1; // JALR
      `OP_U_AUIPC:	controls <= #`simdelay 9'b1010_0000_0; // AUIpc 		ADDED
      default:    	controls <= #`simdelay 9'b0000_0000_0; // ???
    endcase
  end

endmodule

//
// ALU decoder generates ALU control signal (alucontrol)
//
module aludec(input      [6:0] opcode,
              input      [6:0] funct7,
              input      [2:0] funct3,
              output reg [4:0] alucontrol);

  always @(*)

    case(opcode)

      `OP_R:   		// R-type
		begin
			case({funct7,funct3})
			 10'b0000000_000: alucontrol <= #`simdelay 5'b00000; // addition (add)
			 10'b0100000_000: alucontrol <= #`simdelay 5'b10000; // subtraction (sub)
			 10'b0000000_111: alucontrol <= #`simdelay 5'b00001; // and (and)
			 10'b0000000_110: alucontrol <= #`simdelay 5'b00010; // or (or)
			 10'b0000000_100: alucontrol <= #`simdelay 5'b00011; // xor (or)
			 10'b0000000_001: alucontrol <= #`simdelay 5'b00100; // sll 			ADDED
			 10'b0000000_101: alucontrol <= #`simdelay 5'b00101; // srl 			ADDED
			 10'b0100000_101: alucontrol <= #`simdelay 5'b00110; // sra 			ADDED
          default:         alucontrol <= #`simdelay 5'bxxxxx; // ???
        endcase
		end

      `OP_I_ARITH:   // I-type Arithmetic
		begin
			casez({funct7,funct3})												//FIXED to casez
			 10'b???????_000:  alucontrol <= #`simdelay 5'b00000; // addition (addi)	fixed to 10'b
			 10'b???????_110:  alucontrol <= #`simdelay 5'b00010; // or (ori)				fixed to 10'b
			 10'b???????_111:  alucontrol <= #`simdelay 5'b00001; // and (andi)			fixed to 10'b
			 10'b???????_100:  alucontrol <= #`simdelay 5'b00011; // xor (xori)			fixed to 10'b
			 10'b0000000_001:  alucontrol <= #`simdelay 5'b00100; // slli 			ADDED
			 10'b0000000_101:  alucontrol <= #`simdelay 5'b00101; // srli 			ADDED
			 10'b0100000_101:  alucontrol <= #`simdelay 5'b00110; // srai 			ADDED
          default: alucontrol <= #`simdelay 5'bxxxxx; // ???
        endcase
		end

      `OP_I_LOAD: 	// I-type Load (LW, LH, LB...)
      	alucontrol <= #`simdelay 5'b00000;  // addition 

      `OP_B:   		// B-type Branch (BEQ, BNE, ...)
      	alucontrol <= #`simdelay 5'b10000;  // subtraction 

      `OP_S:   		// S-type Store (SW, SH, SB)
      	alucontrol <= #`simdelay 5'b00000;  // addition 

      `OP_U_LUI: 		// U-type (LUI)
      	alucontrol <= #`simdelay 5'b00000;  // addition
		`OP_I_JALR: 		// I-type (JALR)
      	alucontrol <= #`simdelay 5'b00000;  // addition ->?????				ADDED
		`OP_U_AUIPC: 	// U-type (AUIPC)
      	alucontrol <= #`simdelay 5'b00000;  // addition		??					ADDED
      default: 
      	alucontrol <= #`simdelay 5'b00000;  // 

    endcase
    
endmodule


//
// CPU datapath
//
module datapath(input         clk, reset,
                input  [31:0] inst,
                input         auipc,
                input         lui,
                input         regwrite,
                input         memtoreg,
                input         memwrite,
                input         alusrc_dec, 
                input  [4:0]  alucontrol_dec,
                input         branch,
                input         jal,
                input         jalr,

                output reg [31:0] pc,
                output reg [31:0] aluout_mem,
                output reg [31:0] MemWdata_mem,
                // ###### Kyumin Kim: Start #######
                output reg memwrite_,
                output reg stall_exec,
                // ###### Kyumin Kim: End #######
                input  [31:0] MemRdata_mem);

  wire [4:0]  rs1, rs2, rd;
  wire [2:0]  funct3;
  reg  [31:0] rd_data;
  wire [20:1] jal_imm;
  wire [31:0] se_jal_imm;
  wire [12:1] br_imm;
  wire [31:0] se_br_imm;
//   wire [31:0] se_imm_itype;
//   wire [31:0] se_imm_stype;
  wire [31:0] auipc_lui_imm;
  reg  [31:0] alusrc1;
  reg  [31:0] alusrc2;
  wire [31:0] branch_dest, jal_dest, jalr_dest;
  wire		  Nflag, Zflag, Cflag, Vflag;
  wire		  f3beq, f3blt, f3bgeu;
  wire		  beq_taken;
  wire		  blt_taken;
  wire		  bgeu_taken;
// ###### Kyumin Kim: Start #######
// Variable declaration
  // DataPath
  reg [31:0] pc_dec, pc_exec, pc_mem, pc_wb;         // PC for each stage

  wire [31:0] rs1_data_dec_wire, rs2_data_dec_wire; //WIRE for RF <-> ID/EX


  reg [31:0] rs1_exec, rs2_exec;                     // EX rs1, rs2, rd for fowarding
  reg [31:0] rs1_data_exec, rs1_data_dec;           // ID/EX rs1_data 
  reg [31:0] rs2_data_exec, rs2_data_dec;           // ID/EX rs2_data 
  reg [4:0]  rd_wb, rd_mem, rd_exec;                // WB/MEM/EX rd

  reg [31:0] auipc_lui_imm_exec, auipc_lui_imm_dec;  // ID/EX auipc/lui_imm 
  reg [31:0] se_imm_stype_exec, se_imm_stype_dec;   // ID/EX sw_Stype_imm  
  reg [31:0] se_imm_itype_exec, se_imm_itype_dec;   // ID/EX process_Itype_imm 
  reg [31:0] aluout_wb;                  // MEM/WB aluout
  wire [31:0] aluout_exec;
  reg [31:0] MemRdata_wb;                            // MEM/WB MemRdata
  reg [31:0] MemWdata_exec;            // EX/MEM MemRdata

  //Controls
  reg       alusrc_exec;      // alusrc control EX
  reg [4:0] alucontrol_exec;  // alucontrol control EX
  reg       branch_mem, branch_exec;      // branch control EX/MEM
  reg       memwrite_mem, memwrite_exec;    // memwrite control EX/MEM
  reg       memtoreg_wb, memtoreg_mem, memtoreg_exec;  // mem2reg EX/MEM/WB
  reg       regwrite_wb, regwrite_mem, regwrite_exec;  // regwrite EX/MEM/WB
  reg       auipc_exec;                               // auipc EX
  reg       lui_exec;                                 //lui EX
  reg       jal_exec, jal_mem, jal_wb;                // jal EX/MEM/ WB 
  reg       jalr_exec, jalr_mem, jalr_wb;             // jal EX/MEM/WB

// ###### Kyumin Kim: End #######



  assign rs1 = inst[19:15];
  assign rs2 = inst[24:20];
  assign rd  = inst[11:7];
  assign funct3  = inst[14:12];

  //
  // PC (Program Counter) logic 
  //
  assign f3beq  = (funct3 == 3'b000);
  assign f3blt  = (funct3 == 3'b100);
  assign f3bgeu  = (funct3 == 3'b111);

  assign beq_taken  =  branch_mem & f3beq & Zflag;
  assign blt_taken  =  branch_mem & f3blt & (Nflag != Vflag);
  assign bgeu_taken  =  branch_mem & f3bgeu & Cflag;
  
      // ###### Kyumin Kim: Start #######
  assign branch_dest = (pc_dec + se_br_imm);
  assign jal_dest 	= (pc_dec + se_jal_imm);
  assign jalr_dest	= (aluout_mem[31:0]);				// DOES IT NEED 2'b00 ??
    // ###### Kyumin Kim: End #######

  always @(posedge clk, posedge reset)
  begin
     if (reset)  pc <= 32'b0;
	  else 
	  begin
	      if (beq_taken | blt_taken | bgeu_taken ) // branch_taken
				pc <= #`simdelay branch_dest;
		   else if (jal) // jal
				// pc <= #`simdelay jal_dest;
        pc <=  jal_dest;
			else if (jalr) // jalr
				pc <= #`simdelay jalr_dest;
        // ###### Kyumin Kim: Start #######
      else if (stall_exec)            // Stall IF stage on stall signal
        pc <= pc;		
        // ###### Kyumin Kim: End #######
		   else 
				pc <= #`simdelay (pc + 4);
	  end
  end


  // JAL immediate
  assign jal_imm[20:1] = {inst[31],inst[19:12],inst[20],inst[30:21]};
  assign se_jal_imm[31:0] = {{11{jal_imm[20]}},jal_imm[20:1],1'b0};

  // Branch immediate
  assign br_imm[12:1] = {inst[31],inst[7],inst[30:25],inst[11:8]};
  assign se_br_imm[31:0] = {{19{br_imm[12]}},br_imm[12:1],1'b0};



  // 
  // Register File 
  //
  regfile i_regfile(
    .clk			(clk),
    .we			(regwrite_wb),
    .rs1			(rs1),
    .rs2			(rs2),
    .rd			(rd_wb),
    .rd_data	(rd_data),
    .rs1_data	(rs1_data_dec_wire),
    .rs2_data	(rs2_data_dec_wire));

    // ###### Kyumin Kim: Start #######

    // Pipelining -> with flip-flops
    
    always @(posedge clk)
    begin

      //if(jal)
      //begin
      //  inst[31:0] <= 32'h0000_0013;      // nop 0 * 24  0001 0011
      //  pc_dec <= 32'h0000_0000;
      //end
      
    

      if(stall_exec)
      begin
          pc_dec <= pc_dec;                    // IF/ID pc datapath
          pc_exec <= 32'b0;
          rs1_exec <= 0;                  //for fowarding
          rs2_exec <= 0;                     //for fowarding
          rd_exec <= rd;                      // ID/EX rd datapath
          alusrc_exec <= 0;           // ID/EX alusrc control
          alucontrol_exec <= 0;   // ID/EX alucontrol control
          branch_exec <= 0;               // ID/EX branch control
          memwrite_exec <= 0;           // ID/EX  memwrite control
          memtoreg_exec <= 0;           // ID/EX memtoreg control
          regwrite_exec <= 0;           // ID/EX regwrite control
          auipc_exec <= 0;                 // ID/EX auipc control
          lui_exec <= 0;                     // ID/EX lui control
      end
      else
      begin
        pc_dec <= pc;                    // IF/ID pc datapath
        pc_exec <= pc_dec;                    // ID/EX pc datapath
        rs1_exec <= rs1;                    //for fowarding
        rs2_exec <= rs2;                     //for fowarding
        rd_exec <= rd;                      // ID/EX rd datapath
        alusrc_exec <= alusrc_dec;           // ID/EX alusrc control
        alucontrol_exec <= alucontrol_dec;   // ID/EX alucontrol control
        branch_exec <= branch;               // ID/EX branch control
        memwrite_exec <= memwrite;           // ID/EX  memwrite control
        memtoreg_exec <= memtoreg;           // ID/EX memtoreg control
        regwrite_exec <= regwrite;           // ID/EX regwrite control
        auipc_exec <= auipc;                 // ID/EX auipc control
        lui_exec <= lui;                     // ID/EX lui control
      end



        // pc_exec <= pc_dec;                    // ID/EX pc datapath
        pc_mem <= pc_exec;                    // EX/MEM pc datapath
        pc_wb <= pc_mem;                    // MEM/WB pc datapath

        
        rs1_data_exec <= rs1_data_dec;   // ID/EX rs1_data datapath
        
        rs2_data_exec <= rs2_data_dec;   // ID/EX rs2_data datapath
        
        auipc_lui_imm_exec <= auipc_lui_imm_dec;   // ID/EX auipc/lui_imm datapath
        se_imm_stype_exec <= se_imm_stype_dec;   // ID/EX sw_Stype_imm datapath
        se_imm_itype_exec <= se_imm_itype_dec;   // ID/EX process_Itype_imm datapath

        aluout_mem <= aluout_exec;           // EX/MEM aluout datapath
        aluout_wb <= aluout_mem;            // MEM/WB aluout datapath

        rd_mem <= rd_exec;                  // EX/MEM rd datapath
        rd_wb <= rd_mem;                    // MEM/WB rd datapath

        MemRdata_wb <= MemRdata_mem;           // MEM/WB MemRdata datapath

        MemWdata_mem <= MemWdata_exec;          // EX/MEM MemWdata datapath
        


        branch_mem <= branch_exec;           // EX/MEM branch control

        memwrite_mem <= memwrite_exec;       // EX/MEM memwrite control

        memtoreg_mem <= memtoreg_exec;       // EX/MEM memtoreg control
        memtoreg_wb <= memtoreg_mem;         // MEM/WB memtoreg control

        regwrite_mem <= regwrite_exec;       // EX/MEM regwrite control
        regwrite_wb <= regwrite_mem;         // MEM/WB regwrite control


        jal_exec <= jal;
        jal_mem <= jal_exec;
        jal_wb <= jal_mem;

        jalr_exec <= jalr;
        jalr_mem <= jalr_exec;
        jalr_wb <= jalr_mem;
       
    end

    always@(*)
    begin
    // WB lw -> EX sw
      if((rd_wb == rs2_exec) && (memtoreg_wb) && (memwrite_exec) ) MemWdata_exec = MemRdata_wb;
		// S-type Fowarding
	   else if ((rd_wb == rs2_exec) && (regwrite_wb && ~memtoreg_wb) && (memwrite_exec) ) MemWdata_exec = aluout_wb;
	   else MemWdata_exec = rs2_data_exec;
    end
      
    always@(*)
	 begin
      memwrite_ = memwrite_mem;
		end

    always@(*)
    begin
      // WB -> ID FOWARDING rs1 - load-use
     if ((rd_wb == rs1) && (memtoreg_wb)&& (regwrite || memwrite)) rs1_data_dec = MemRdata_wb;
     //WB -> ID FOWARDING GENERAL rs1
     else if ((rd_wb == rs1) && (regwrite_wb) && (regwrite || memwrite)) rs1_data_dec = rd_data;
     else      rs1_data_dec = rs1_data_dec_wire;
    end

    always@(*)
    begin
	       // WB -> ID FOWARDING rs2 - load-use
      if ((rd_wb == rs2) && (memtoreg_wb)&& (regwrite || memwrite)) rs2_data_dec = MemRdata_wb;
		     //WB -> ID FOWARDING GENERAL rs2
      else if ((rd_wb == rs2) && (regwrite_wb) && (regwrite || memwrite)) rs2_data_dec = rd_data;
      else      rs2_data_dec = rs2_data_dec_wire;
    end


    // hazard-detection load-use case 
    always@(*)
    begin
      if((memtoreg_exec) && ((rd_exec == rs1) || (rd_exec == rs2))) stall_exec = 1;
      else stall_exec = 0;
    end


    // ###### Kyumin Kim: End #######


	//
	// ALU 
	//
	alu i_alu(
		.a			(alusrc1),
		.b			(alusrc2),
		.alucont	(alucontrol_exec),
		.result	(aluout_exec),
		.N			(Nflag),
		.Z			(Zflag),
		.C			(Cflag),
		.V			(Vflag));

	// 1st source to ALU (alusrc1)
	always@(*)
	begin
        // ###### Kyumin Kim: Start #######
		if      (auipc_exec)	alusrc1[31:0]  =  pc_exec;  
		else if (lui_exec) 		alusrc1[31:0]  =  32'b0;
    // WB -> EX FOWARDING - load-use
    // WB : I(lw) -> EX : R, I, I(lw), S(sw), U type rs1
    else if ((rd_wb == rs1_exec) && (memtoreg_wb) && (regwrite_exec || memwrite_exec)) alusrc1[31:0] = MemRdata_wb;
    
    //MEM -> EX FOWARDING
    else if ((rd_mem == rs1_exec) && (regwrite_mem) && (regwrite_exec || memwrite_exec)) alusrc1[31:0] = aluout_mem;     
    // WB -> EX FOWARDING
    // WB : R, I, U type rd -> EX : R, I, I(lw), S(sw), U type rs1
    else if ((rd_wb == rs1_exec) && (regwrite_wb) && (regwrite_exec || memwrite_exec))   alusrc1[31:0] = aluout_wb;
    else          		alusrc1[31:0]  =  rs1_data_exec[31:0];
        // ###### Kyumin Kim: End #######
	end
	
	// 2nd source to ALU (alusrc2)
	always@(*)
	begin
        // ###### Kyumin Kim: Start #######
		if	     (auipc_exec | lui_exec)	    alusrc2[31:0] = auipc_lui_imm_exec[31:0];
		else if (alusrc_exec & memwrite_exec)	alusrc2[31:0] = se_imm_stype_exec[31:0];
		else if (alusrc_exec)		              alusrc2[31:0] = se_imm_itype_exec[31:0];
    // WB -> EX FOWARDING - load-use
    // WB : I(lw) -> EX : R, U(lui) type rs2
    else if ((rd_wb == rs2_exec) && (memtoreg_wb) && (regwrite_exec) && ((~alusrc_exec) )) alusrc2[31:0] = MemRdata_wb; // ~alusrc  sw : alusrc_exec = 1
    //MEM -> EX FOWARDING
    else if ((rd_mem == rs2_exec) && (regwrite_mem) && (regwrite_exec)  && (~alusrc_exec)) alusrc2[31:0] = aluout_mem;     
    // WB -> EX FOWARDING
    else if ((rd_wb == rs2_exec) && (regwrite_wb) && (regwrite_exec) && (~alusrc_exec) )   alusrc2[31:0] = aluout_wb;
    
    else   alusrc2[31:0] = rs2_data_exec[31:0];
        // ###### Kyumin Kim: End #######
	end

    always@(*)
    begin
        // ###### Kyumin Kim: Start #######
         se_imm_itype_dec[31:0] <= {{20{inst[31]}},inst[31:20]};
         se_imm_stype_dec[31:0] <= {{20{inst[31]}},inst[31:25],inst[11:7]};
         auipc_lui_imm_dec[31:0] <= {inst[31:12],12'b0};
        // ###### Kyumin Kim: End #######
    end


	// Data selection for writing to RF
	always@(*)
	begin
        // ###### Kyumin Kim: Start #######
		if	     (jal_wb)			rd_data[31:0] = pc_wb + 4;
		else if (memtoreg_wb)	rd_data[31:0] = MemRdata_wb;
		else						rd_data[31:0] = aluout_wb;
        // ###### Kyumin Kim: End #######
	end
    
	
endmodule
