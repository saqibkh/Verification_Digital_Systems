`include "constants.vh"
`include "rv32_opcodes.vh"
`include "alu_ops.vh"

//Write your properties in a module here.
module decoder_test(
  input clk,
  input reset,
  input [31:0]                  inst,
  input [`IMM_TYPE_WIDTH-1:0]   imm_type,
  input [`REG_SEL-1:0]         rs1,
  input [`REG_SEL-1:0]         rs2,
  input [`REG_SEL-1:0]         rd,
  input [`SRC_A_SEL_WIDTH-1:0]  src_a_sel,
  input [`SRC_B_SEL_WIDTH-1:0]  src_b_sel,
  input                         wr_reg,
  input                         uses_rs1,
  input                         uses_rs2,
  input                         illegal_instruction,
  input [`ALU_OP_WIDTH-1:0]     alu_op,
  input [`RS_ENT_SEL-1:0]       rs_ent,

  input [2:0]                  dmem_size,
  input [`MEM_TYPE_WIDTH-1:0]  dmem_type,
  input [`MD_OP_WIDTH-1:0]      md_req_op,
  input                         md_req_in_1_signed,
  input                         md_req_in_2_signed,
  input [`MD_OUT_SEL_WIDTH-1:0] md_req_out_sel
);


wire [6:0]               opcode  = inst[6:0];
wire [6:0]               funct7  = inst[31:25];
wire [11:0]              funct12 = inst[31:20];
wire [2:0]               funct3  = inst[14:12];

// 1) wr_reg is set to 1/0 as per the value in inst [6:0] (opcode). You can use the Execution column in RISC-V-Subset.xls to figure out how wr_reg should be assigned
assert_wr_reg_RV32_LUI: assert property(@(posedge clk) (opcode == `RV32_LUI) |-> (wr_reg == 1));

assert_wr_reg_RV32_AUIPC: assert property(@(posedge clk) (opcode == `RV32_AUIPC) |-> (wr_reg == 1));
assert_wr_reg_RV32_LOAD: assert property(@(posedge clk) (opcode == `RV32_LOAD) |-> (wr_reg == 1));
assert_wr_reg_RV32_STORE: assert property(@(posedge clk) (opcode == `RV32_STORE) |-> (wr_reg == 0));
assert_wr_reg_RV32_JAL: assert property(@(posedge clk) (opcode == `RV32_JAL) |-> (wr_reg == 1));
assert_wr_reg_RV32_BRANCH: assert property(@(posedge clk) (opcode == `RV32_BRANCH) |-> (wr_reg == 0));
assert_wr_reg_RV32_OP: assert property(@(posedge clk) (opcode == `RV32_OP) |-> (wr_reg == 1));


// 2) md_req_out_sel is set to 1/0 as per the specifications.
//assert_md_req_out_sel_AUIPC: assert property(@(posedge clk) (opcode == `RV32_AUIPC) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_LOAD: assert property(@(posedge clk) (opcode == `RV32_LOAD) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_STORE: assert property(@(posedge clk) (opcode == `RV32_STORE) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_JAL: assert property(@(posedge clk) (opcode == `RV32_JAL) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_BRANCH: assert property(@(posedge clk) (opcode == `RV32_BRANCH) |-> (md_req_out_sel == `MD_OUT_LO));


//assert_md_req_out_sel_RV32_OP_ADD_SUB: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_ADD_SUB)) |-> (md_req_out_sel == `MD_OUT_LO)); 
//assert_md_req_out_sel_RV32_OP_SLL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLL)) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_RV32_OP_SLT: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLT)) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_RV32_OP_SLTU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLTU)) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_RV32_OP_XOR: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_XOR)) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_RV32_OP_SRA_SRL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SRA_SRL)) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_RV32_OP_OR: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_OR)) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_RV32_OP_AND: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_AND)) |-> (md_req_out_sel == `MD_OUT_LO));
assert_md_req_out_sel_RV32_OP_MUL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MUL)) |-> (md_req_out_sel == `MD_OUT_LO));
assert_md_req_out_sel_RV32_OP_MULH: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MULH)) |-> (md_req_out_sel == `MD_OUT_HI));
assert_md_req_out_sel_RV32_OP_MULHSU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MULHSU)) |-> (md_req_out_sel == `MD_OUT_HI));
assert_md_req_out_sel_RV32_OP_MULHU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MULHU)) |-> (md_req_out_sel == `MD_OUT_HI));
//assert_md_req_out_sel_RV32_OP_DIV: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_DIV)) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_RV32_OP_DIVU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_DIVU)) |-> (md_req_out_sel == `MD_OUT_LO));
//assert_md_req_out_sel_RV32_OP_REM: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_REM)) |-> (md_req_out_sel == `MD_OUT_REM));
//assert_md_req_out_sel_RV32_OP_REMU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_REMU)) |-> (md_req_out_sel == `MD_OUT_REM));



// 3) md_req_in_1_signed is set to 1 or 0 as per the specifications.
//assert_md_req_in_1_signed_RV32_OP_ADD_SUB: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_ADD_SUB)) |-> (md_req_in_1_signed == 0));
//assert_md_req_in_1_signed_RV32_OP_SLL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLL)) |-> (md_req_in_1_signed == 0));
//assert_md_req_in_1_signed_RV32_OP_SLT: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLT)) |-> (md_req_in_1_signed == 0));
//assert_md_req_in_1_signed_RV32_OP_SLTU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLTU)) |-> (md_req_in_1_signed == 0));
//assert_md_req_in_1_signed_RV32_OP_XOR: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_XOR)) |-> (md_req_in_1_signed == 0));
//assert_md_req_in_1_signed_RV32_OP_SRA_SRL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SRA_SRL)) |-> (md_req_in_1_signed == 0));
//assert_md_req_in_1_signed_RV32_OP_OR: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_OR)) |-> (md_req_in_1_signed == 0));
//assert_md_req_in_1_signed_RV32_OP_AND: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_AND)) |-> (md_req_in_1_signed == 0));

assert_md_req_in_1_signed_RV32_OP_MUL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MUL)) |-> (md_req_in_1_signed == 0));
assert_md_req_in_1_signed_RV32_OP_MULH: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MULH)) |-> (md_req_in_1_signed == 1));
assert_md_req_in_1_signed_RV32_OP_MULHSU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MULHSU)) |-> (md_req_in_1_signed == 1));
assert_md_req_in_1_signed_RV32_OP_MULHU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MULHU)) |-> (md_req_in_1_signed == 0));
assert_md_req_in_1_signed_RV32_OP_DIV: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_DIV)) |-> (md_req_in_1_signed == 1));
assert_md_req_in_1_signed_RV32_OP_DIVU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_DIVU)) |-> (md_req_in_1_signed == 0));
assert_md_req_in_1_signed_RV32_OP_REM: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_REM)) |-> (md_req_in_1_signed == 1));
assert_md_req_in_1_signed_RV32_OP_REMU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_REMU)) |-> (md_req_in_1_signed == 0));



// 4) md_req_in_2 signed is set to 1 or 0 as per the specifications.
//assert_md_req_in_2_signed_RV32_OP_ADD_SUB: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_ADD_SUB)) |-> (md_req_in_2_signed == 0));
//assert_md_req_in_2_signed_RV32_OP_SLL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLL)) |-> (md_req_in_2_signed == 0));
//assert_md_req_in_2_signed_RV32_OP_SLT: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLT)) |-> (md_req_in_2_signed == 0));
//assert_md_req_in_2_signed_RV32_OP_SLTU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLTU)) |-> (md_req_in_2_signed == 0));
//assert_md_req_in_2_signed_RV32_OP_XOR: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_XOR)) |-> (md_req_in_2_signed == 0));
//assert_md_req_in_2_signed_RV32_OP_SRA_SRL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SRA_SRL)) |-> (md_req_in_2_signed == 0));
//assert_md_req_in_2_signed_RV32_OP_OR: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_OR)) |-> (md_req_in_2_signed == 0));
//assert_md_req_in_2_signed_RV32_OP_AND: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_AND)) |-> (md_req_in_2_signed == 0));

assert_md_req_in_2_signed_RV32_OP_MUL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MUL)) |-> (md_req_in_2_signed == 0));
assert_md_req_in_2_signed_RV32_OP_MULH: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MULH)) |-> (md_req_in_2_signed == 1));
assert_md_req_in_2_signed_RV32_OP_MULHSU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MULHSU)) |-> (md_req_in_2_signed == 0));
assert_md_req_in_2_signed_RV32_OP_MULHU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_MULHU)) |-> (md_req_in_2_signed == 0));
assert_md_req_in_2_signed_RV32_OP_DIV: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_DIV)) |-> (md_req_in_2_signed == 1));
assert_md_req_in_2_signed_RV32_OP_DIVU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_DIVU)) |-> (md_req_in_2_signed == 0));
assert_md_req_in_2_signed_RV32_OP_REM: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_REM)) |-> (md_req_in_2_signed == 1));
assert_md_req_in_2_signed_RV32_OP_REMU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct3 == `RV32_FUNCT3_REMU)) |-> (md_req_in_2_signed == 0));


// 5) Based on funct3, funct7, opcode values as defined in RISC-V SUBSET.xls, verify if the right alu_op has been assigned for ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND under all possible combinations in inst [31:0].
//assert_alu_op_BEQ: assert property(@(posedge clk) ((opcode == `RV32_BRANCH) && (funct3 == 0)) |-> (alu_op == 8));
//assert_alu_op_BNE: assert property(@(posedge clk) ((opcode == `RV32_BRANCH) && (funct3 == 1)) |-> (alu_op == 9));
//assert_alu_op_BLT: assert property(@(posedge clk) ((opcode == `RV32_BRANCH) && (funct3 == 4)) |-> (alu_op == 12));
//assert_alu_op_BGE: assert property(@(posedge clk) ((opcode == `RV32_BRANCH) && (funct3 == 5)) |-> (alu_op == 14));
//assert_alu_op_BLTU: assert property(@(posedge clk) ((opcode == `RV32_BRANCH) && (funct3 == 6)) |-> (alu_op == 13));
//assert_alu_op_BGEU: assert property(@(posedge clk) ((opcode == `RV32_BRANCH) && (funct3 == 7)) |-> (alu_op == 15));
assert_alu_op_ADD: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[5] == 0) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_ADD_SUB)) |-> (alu_op == 0));
assert_alu_op_SUB: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[5] == 1) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_ADD_SUB)) |-> (alu_op == 10));
assert_alu_op_SLL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLL)) |-> (alu_op == 1));
assert_alu_op_SLT: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLT)) |-> (alu_op == 12));
assert_alu_op_SLTU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SLTU)) |-> (alu_op == 14));
assert_alu_op_XOR: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_XOR)) |-> (alu_op == 4));
assert_alu_op_SRL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[5] == 1) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SRA_SRL)) |-> (alu_op == 5));
assert_alu_op_SRA: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[5] == 0) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_SRA_SRL)) |-> (alu_op == 11));
assert_alu_op_OR: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[5] == 0) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_OR)) |-> (alu_op == 6));
assert_alu_op_AND: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[5] == 0) && (funct7[0] == 0) && (funct3 == `RV32_FUNCT3_AND)) |-> (alu_op == 7));
//assert_alu_op_MUL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct7[5] == 0) && (funct3 == `RV32_FUNCT3_MUL)) |-> (alu_op == NA));
//assert_alu_op_MULH: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct7[5] == 0) && (funct3 == `RV32_FUNCT3_MULH)) |-> (alu_op == NA));
//assert_alu_op_MULHSU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct7[5] == 0) && (funct3 == `RV32_FUNCT3_MULHSU)) |-> (alu_op == NA));
//assert_alu_op_MULHU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct7[5] == 0) && (funct3 == `RV32_FUNCT3_MULHSU)) |-> (alu_op == NA));
//assert_alu_op_DIV: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct7[5] == 0) && (funct3 == `RV32_FUNCT3_DIV)) |-> (alu_op == NA));
//assert_alu_op_DIVU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct7[5] == 0) && (funct3 == `RV32_FUNCT3_DIVU)) |-> (alu_op == NA));
//assert_alu_op_REM: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct7[5] == 0) && (funct3 == `RV32_FUNCT3_REM)) |-> (alu_op == NA));
//assert_alu_op_REMU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7[0] == 1) && (funct7[5] == 0) && (funct3 == `RV32_FUNCT3_REMU)) |-> (alu_op == NA));



// 6) For 2,3,4,5 write proper assume properties on funct7.

// If funct7[0]==1 then funct7[5]==0
//If funct7[5]==1 then funct7[0]==0

property funct7_0_1_and_funct7_5_0;
  @(posedge clk) ((funct7[0]==1) |-> (funct7[5]==0));
endproperty
assume_valid_funct7_0: assume property(funct7_0_1_and_funct7_5_0);

property funct7_5_1_and_funct7_0_0;
  @(posedge clk) ((funct7[5]==1) |-> (funct7[0]==0));
endproperty
assume_valid_funct7_5: assume property(funct7_5_1_and_funct7_0_0);

// 7) Verify if the signal rs ent is assigned the right value based on inst [6:0].
//assert_rs_ent_RV32_LUI: assert property(@(posedge clk) (opcode == `RV32_LUI) |-> (rs_ent == ));
//assert_rs_ent_RV32_AUIPC: assert property(@(posedge clk) (opcode == `RV32_AUIPC) |-> (rs_ent == ));
assert_rs_ent_RV32_LOAD: assert property(@(posedge clk) (opcode == `RV32_LOAD) |-> (rs_ent == `RS_ENT_LDST));
assert_rs_ent_RV32_STORE: assert property(@(posedge clk) (opcode == `RV32_STORE) |-> (rs_ent == `RS_ENT_LDST));
assert_rs_ent_RV32_JAL: assert property(@(posedge clk) (opcode == `RV32_JAL) |-> (rs_ent == `RS_ENT_JAL));
assert_rs_ent_RV32_JALR: assert property(@(posedge clk) (opcode == `RV32_JALR) |-> (rs_ent == `RS_ENT_JALR));
assert_rs_ent_RV32_BRANCH: assert property(@(posedge clk) (opcode == `RV32_BRANCH) |-> (rs_ent == `RS_ENT_BRANCH));

assert_rs_ent_RV32_OP_MUL: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7 == `RV32_FUNCT7_MUL_DIV) && (funct3 == `RV32_FUNCT3_MUL)) |-> (rs_ent == `RS_ENT_MUL));
assert_rs_ent_RV32_OP_MULH: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7 == `RV32_FUNCT7_MUL_DIV) && (funct3 == `RV32_FUNCT3_MULH)) |-> (rs_ent == `RS_ENT_MUL));
assert_rs_ent_RV32_OP_MULHSU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7 == `RV32_FUNCT7_MUL_DIV) && (funct3 == `RV32_FUNCT3_MULHSU)) |-> (rs_ent == `RS_ENT_MUL));
assert_rs_ent_RV32_OP_MULHU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7 == `RV32_FUNCT7_MUL_DIV) && (funct3 == `RV32_FUNCT3_MULHU)) |-> (rs_ent == `RS_ENT_MUL));

assert_rs_ent_RV32_OP_DIV: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7 == `RV32_FUNCT7_MUL_DIV) && (funct3 == `RV32_FUNCT3_DIV)) |-> (rs_ent == `RS_ENT_DIV));
assert_rs_ent_RV32_OP_DIVU: assert property(@(posedge clk) ((opcode == `RV32_OP) && (funct7 == `RV32_FUNCT7_MUL_DIV) && (funct3 == `RV32_FUNCT3_DIVU)) |-> (rs_ent == `RS_ENT_DIV));


// 9) In addition to the assert and assume, develop your own cover properties that cover all the ISA (refer to RISC-V-subset.xlsx)
cover_RV32_LUI: cover property(@(posedge clk) (opcode == `RV32_LUI));
cover_RV32_AUIPC: cover property(@(posedge clk) (opcode == `RV32_AUIPC));
cover_RV32_LOAD: cover property(@(posedge clk) (opcode == `RV32_LOAD));
cover_RV32_STORE: cover property(@(posedge clk) (opcode == `RV32_STORE));
cover_RV32_JAL: cover property(@(posedge clk) (opcode == `RV32_JAL));
cover_RV32_JALR: cover property(@(posedge clk) (opcode == `RV32_JALR));
cover_RV32_BRANCH: cover property(@(posedge clk) (opcode == `RV32_BRANCH));
cover_RV32_OP: cover property(@(posedge clk) (opcode == `RV32_OP));

cover_RV32_OP_ADD_SUB: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_ADD_SUB)));
cover_RV32_OP_SLL: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_SLL)));
cover_RV32_OP_SLT: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_SLT)));
cover_RV32_OP_SLTU: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_SLTU)));
cover_RV32_OP_XOR: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_XOR)));
cover_RV32_OP_SRA_SRL: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_SRA_SRL)));
cover_RV32_OP_OR: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_OR)));
cover_RV32_OP_AND: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_AND)));
cover_RV32_OP_BEQ: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_BEQ)));
cover_RV32_OP_BNE: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_BNE)));
cover_RV32_OP_BLT: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_BLT)));
cover_RV32_OP_BGE: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_BGE)));
cover_RV32_OP_BLTU: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_BLTU)));
cover_RV32_OP_BGEU: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_BGEU)));

cover_RV32_OP_MUL: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_MUL)));
cover_RV32_OP_MULH: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_MULH)));
cover_RV32_OP_MULHSU: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_MULHSU)));
cover_RV32_OP_MULHU: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_MULHU)));
cover_RV32_OP_DIV: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_DIV)));
cover_RV32_OP_DIVU: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_DIVU)));
cover_RV32_OP_REM: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_REM)));
cover_RV32_OP_REMU: cover property(@(posedge clk) ((opcode == `RV32_OP) && (funct3 == `RV32_FUNCT3_REMU)));

endmodule

module Wrapper;
//BIND HERE
bind decoder decoder_test u_decoder_test(
  .clk(clk),
  .reset(reset),
  .inst(inst),
  .imm_type(imm_type),
  .rs1(rs1),
  .rs2(rs2),
  .rd(rd),
  .src_a_sel(src_a_sel),
  .src_b_sel(src_b_sel),
  .wr_reg(wr_reg),
  .uses_rs1(uses_rs1),
  .uses_rs2(uses_rs2),
  .illegal_instruction(illegal_instruction),
  .alu_op(alu_op),
  .rs_ent(rs_ent),
  .dmem_size(dmem_size),
  .dmem_type(dmem_type),
  .md_req_op(md_req_op),
  .md_req_in_1_signed(md_req_in_1_signed),
  .md_req_in_2_signed(md_req_in_2_signed),
  .md_req_out_sel(md_req_out_sel)
);

endmodule                                                                                                              
