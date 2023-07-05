// Pipelined RISC-V CPU core

`define STATIC_PREDICT

module nanorv32
  (
  input clk,
  input reset_l,

  // Stall the pipeline, suppress all writes
  // Assert this for each cycle that dmem or imem is late- meaning
  //  it's high on the cycle the data is supposed to be there, but isn't.
  // It's safe to insert random stalls unrelated to the memory
  // dmem_rd_req and dmem_wr_req will remain low on any cycle
  // that stall is high.
  input stall,

  // Interrupt requests
  input [31:0] irq,

  // Read from instruction memory with a one flop delay
  //  new imem_rd_addr given in cycle 0
  //  data at location imem_rd_addr appears in cycle 1
  //  data remains unchanged until next change to imem_rd_addr
  output wire [31:0] imem_rd_addr,
  input [31:0] imem_rd_data,


  // Read from data memory with a one flop delay
  //  new dmem_rd_addr and dmem_rd_req given in cycle 0
  //  data at location dmem_rd_addr appears in cycle 1
  //  data remains unchanged until one cycle after after
  //  next dmem_rd_req pulse
  output wire [31:0] dmem_rd_addr,
  output wire dmem_rd_req, // Read request: read data available next cycle
  input [31:0] dmem_rd_data,

  // Write to data memory
  //  dmem_wr_addr, dmem_wr_data, dmem_wr_be and dmem_wr_req all given
  //  in the same cycle.
  // Data memory should be bypassed so that if you write
  // and read to the same address in the same cycle, the
  // returned read data is the write data.
  output wire [31:0] dmem_wr_addr,
  output wire [31:0] dmem_wr_data,
  output wire [3:0] dmem_wr_be, // Byte enables
  output wire dmem_wr_req // Write request: write completes this cycle
  );

reg hazard;

//
// Stage 1: Fetch
//

// 'pc' holds the address of the instruction currently
// appearing on imem_rd_data (unless stall is high- in this
// case pc holds address of instruction that is supposed
// to be there, but instruction is treated as invalid).
reg [31:0] pc, ns_pc;

reg jump;
reg [31:0] jump_to;

always @(posedge clk)
  if (!reset_l)
    pc <= 0;
  else
    pc <= ns_pc;

wire [31:0] insn_1 = imem_rd_data;

wire [31:0] jump_imm20_1 = { { 19 { insn_1[31] } }, insn_1[31], insn_1[19:12], insn_1[20], insn_1[30:21], 1'd0 }; // J-type (WTF?)
wire [31:0] branch_imm12_1 = { { 19 { insn_1[31] } }, insn_1[31], insn_1[7], insn_1[30:25], insn_1[11:8], 1'd0 }; // B-Type (WTF?)
reg ns_jumpimm_2;
reg ns_branch_2;

always @*
  begin
    ns_pc = pc;
    if (!stall && !hazard)
      if (jump)
        ns_pc = jump_to;
`ifdef STATIC_PREDICT
      else if (ns_jumpimm_2)
        ns_pc = pc + jump_imm20_1;
      else if (ns_branch_2 && branch_imm12_1[31]) // Assume backward branches are taken, forward branches are not
        ns_pc = pc + branch_imm12_1;
`endif
      else
        ns_pc = pc + 32'h4;
    if (!reset_l)
      ns_pc = 0;
  end

assign imem_rd_addr = ns_pc;

// Outputs to next stage:

wire [31:0] pc_1 = pc;

//
// Stage 2: Decode and read registers
//

// Register file

reg ns_force_rs1_zero, force_rs1_zero;

wire [4:0] rs1_rd_addr = hazard ? (force_rs1_zero ? 5'd0 : insn_2[19:15]) : (ns_force_rs1_zero ? 5'd0 : insn_1[19:15]);
reg [4:0] rs1_rd_addr_2;
wire [31:0] rs1_rd_data;

wire [4:0] rs2_rd_addr = hazard ? insn_2[24:20] : insn_1[24:20];
reg [4:0] rs2_rd_addr_2;
wire [31:0] rs2_rd_data;

wire [4:0] rd_wr_addr;
wire [31:0] rd_wr_data;
wire rd_we;

ram_dist_dp #(.DATAWIDTH(32), .ADDRWIDTH(5)) rs1_ram
  (
  .clk (clk),
  .rd_addr (rs1_rd_addr),
  .rd_data (rs1_rd_data),
  .wr_addr (rd_wr_addr),
  .wr_data (rd_wr_data),
  .we (rd_we && !stall && rd_wr_addr != 5'd0) // Don't write to x0
  );

ram_dist_dp #(.DATAWIDTH(32), .ADDRWIDTH(5)) rs2_ram
  (
  .clk (clk),
  .rd_addr (rs2_rd_addr),
  .rd_data (rs2_rd_data),
  .wr_addr (rd_wr_addr),
  .wr_data (rd_wr_data),
  .we (rd_we && !stall && rd_wr_addr != 5'd0) // Don't write to x0
  );

// Outputs to next stage:

reg [31:0] insn_2;
reg [31:0] pc_2;
wire [31:0] rs1_2 = rs1_rd_data;
wire [31:0] rs2_2 = rs2_rd_data;

// Control bits
reg write_2, ns_write_2; // Save result in rd
reg load_2, ns_load_2; // Modified by signed
reg fake_2, ns_fake_2;
reg store_2, ns_store_2; // Save register to memory
reg mret_2, ns_mret_2;
reg branch_2;
reg jump_2, ns_jump_2;
reg csr_2, ns_csr_2;

// ALU arg2 input select
reg auipc_2, ns_auipc_2;

reg arg2_imm_2, ns_arg2_imm_2;
reg arg2_rs2_2, ns_arg2_rs2_2;
reg arg2_upper_imm_2, ns_arg2_upper_imm_2;

// Operation
reg byte_2, ns_byte_2;
reg half_2, ns_half_2;
reg signed_2, ns_signed_2;
reg shift_left_2, ns_shift_left_2;
reg shift_right_2, ns_shift_right_2; // Modified by signed
reg set_less_than_2, ns_set_less_than_2; // Modified by signed
reg add_2, ns_add_2;
reg sub_2, ns_sub_2;
reg xor_2, ns_xor_2;
reg or_2, ns_or_2;
reg and_2, ns_and_2;
reg eq_2, ns_eq_2;
reg ne_2, ns_ne_2;
reg lt_2, ns_lt_2; // Modified by signed
reg ge_2, ns_ge_2; // Modified by signed
reg mul_2, ns_mul_2; // Modified by signed when upper is set
reg upper_2, ns_upper_2; // Modified by signed
reg mixed_2, ns_mixed_2;
reg div_2, ns_div_2; // Modified by signed
reg rem_2, ns_rem_2; // Modified by signed
reg jumpimm_2;
reg csr_set_2, ns_csr_set_2;
reg csr_clr_2, ns_csr_clr_2;
reg csr_imm_2, ns_csr_imm_2;
reg uses_rs1_2, ns_uses_rs1_2;
reg uses_rs2_2, ns_uses_rs2_2;

always @(posedge clk)
  if (!reset_l)
    begin
      insn_2 <= 0;
      pc_2 <= 0;
      write_2 <= 0;
      load_2 <= 0;
      fake_2 <= 0;
      store_2 <= 0;
      mret_2 <= 0;
      branch_2 <= 0;
      jump_2 <= 0;
      csr_2 <= 0;
      auipc_2 <= 0;
      arg2_imm_2 <= 0;
      arg2_rs2_2 <= 0;
      arg2_upper_imm_2 <= 0;
      byte_2 <= 0;
      half_2 <= 0;
      signed_2 <= 0;
      shift_left_2 <= 0;
      shift_right_2 <= 0; // Modified by signed
      set_less_than_2 <= 0; // Modified by signed
      add_2 <= 0;
      sub_2 <= 0;
      xor_2 <= 0;
      or_2 <= 0;
      and_2 <= 0;
      eq_2 <= 0;
      ne_2 <= 0;
      lt_2 <= 0; // Modified by signed
      ge_2 <= 0; // Modified by signed
      mul_2 <= 0; // Modified by signed when upper is set
      upper_2 <= 0; // Modified by signed
      mixed_2 <= 0;
      div_2 <= 0; // Modified by signed
      rem_2 <= 0; // Modified by signed
      jumpimm_2 <= 0;
      csr_set_2 <= 0;
      csr_clr_2 <= 0;
      csr_imm_2 <= 0;
      rs1_rd_addr_2 <= 0;
      rs2_rd_addr_2 <= 0;
      force_rs1_zero <= 0;
      uses_rs1_2 <= 0;
      uses_rs2_2 <= 0;
    end
  else
    begin
      if (!stall && !hazard)
        begin
          uses_rs1_2 <= ns_uses_rs1_2;
          uses_rs2_2 <= ns_uses_rs2_2;
          force_rs1_zero <= ns_force_rs1_zero;
          insn_2 <= insn_1;
          pc_2 <= pc_1;
          rs1_rd_addr_2 <= rs1_rd_addr;
          rs2_rd_addr_2 <= rs2_rd_addr;
          write_2 <= ns_write_2;
          load_2 <= ns_load_2;
          fake_2 <= ns_fake_2;
          store_2 <= ns_store_2;
          mret_2 <= ns_mret_2;
          branch_2 <= ns_branch_2;
          jump_2 <= ns_jump_2;
          csr_2 <= ns_csr_2;
          auipc_2 <= ns_auipc_2;
          arg2_imm_2 <= ns_arg2_imm_2;
          arg2_rs2_2 <= ns_arg2_rs2_2;
          arg2_upper_imm_2 <= ns_arg2_upper_imm_2;
          byte_2 <= ns_byte_2;
          half_2 <= ns_half_2;
          signed_2 <= ns_signed_2;
          shift_left_2 <= ns_shift_left_2;
          shift_right_2 <= ns_shift_right_2; // Modified by signed
          set_less_than_2 <= ns_set_less_than_2; // Modified by signed
          add_2 <= ns_add_2;
          sub_2 <= ns_sub_2;
          xor_2 <= ns_xor_2;
          or_2 <= ns_or_2;
          and_2 <= ns_and_2;
          eq_2 <= ns_eq_2;
          ne_2 <= ns_ne_2;
          lt_2 <= ns_lt_2; // Modified by signed
          ge_2 <= ns_ge_2; // Modified by signed
          mul_2 <= ns_mul_2; // Modified by signed when upper is set
          upper_2 <= ns_upper_2; // Modified by signed
          mixed_2 <= ns_mixed_2;
          div_2 <= ns_div_2; // Modified by signed
          rem_2 <= ns_rem_2; // Modified by signed
          jumpimm_2 <= ns_jumpimm_2;
          csr_set_2 <= ns_csr_set_2;
          csr_clr_2 <= ns_csr_clr_2;
          csr_imm_2 <= ns_csr_imm_2;
        end
    end

always @*
  begin
    // Defaults for control bits
    ns_uses_rs1_2 = 0;
    ns_uses_rs2_2 = 0;
    ns_force_rs1_zero = 0;
    ns_write_2 = 0;
    ns_load_2 = 0;
    ns_fake_2 = 0;
    ns_store_2 = 0;
    ns_mret_2 = 0;
    ns_branch_2 = 0;
    ns_jump_2 = 0;
    ns_csr_2 = 0;
    ns_auipc_2 = 0;
    ns_arg2_imm_2 = 0;
    ns_arg2_rs2_2 = 0;
    ns_arg2_upper_imm_2 = 0;
    ns_byte_2 = 0;
    ns_half_2 = 0;
    ns_signed_2 = 0;
    ns_shift_left_2 = 0;
    ns_shift_right_2 = 0; // Modified by signed
    ns_set_less_than_2 = 0; // Modified by signed
    ns_add_2 = 0;
    ns_sub_2 = 0;
    ns_xor_2 = 0;
    ns_or_2 = 0;
    ns_and_2 = 0;
    ns_eq_2 = 0;
    ns_ne_2 = 0;
    ns_lt_2 = 0; // Modified by signed
    ns_ge_2 = 0; // Modified by signed
    ns_mul_2 = 0; // Modified by signed when upper is set
    ns_upper_2 = 0; // Modified by signed
    ns_mixed_2 = 0;
    ns_div_2 = 0; // Modified by signed
    ns_rem_2 = 0; // Modified by signed
    ns_jumpimm_2 = 0;
    ns_csr_set_2 = 0;
    ns_csr_clr_2 = 0;
    ns_csr_imm_2 = 0;

    // Instruction decoder

    casex (insn_1)
      //  f7      rs2   rs1   f3  rd    opcode
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_0000011: // LB Load signed byte
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_load_2 = 1;
          ns_byte_2 = 1;
          ns_signed_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_0000011: // LH Load signed halfword
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_load_2 = 1;
          ns_half_2 = 1;
          ns_signed_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_010_xxxxx_0000011: // LW Load word
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_load_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_100_xxxxx_0000011: // LBU Load unsigned byte 
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_load_2 = 1;
          ns_byte_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_101_xxxxx_0000011: // LHU Load unsigned halfword
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_load_2 = 1;
          ns_half_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_0001111: // FENCE
        begin
        end
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_0001111: // FENCE.I
        begin
        end
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_0010011: // ADDI Add immediate
        begin
          ns_uses_rs1_2 = 1;
          ns_add_2 = 1;
          ns_write_2 = 1;
          ns_arg2_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_0010011: // SLLI Shift left immediate
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_shift_left_2 = 1;
          ns_arg2_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_010_xxxxx_0010011: // SLTI Set if less than immediate signed
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_set_less_than_2 = 1;
          ns_sub_2 = 1;
          ns_signed_2 = 1;
          ns_arg2_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_011_xxxxx_0010011: // SLTIU Set if less than immediate unsigned
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_set_less_than_2 = 1;
          ns_sub_2 = 1;
          ns_arg2_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_100_xxxxx_0010011: // XORI Xor immediate
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_xor_2 = 1;
          ns_arg2_imm_2 = 1;
        end
      32'b00xxxxx_xxxxx_xxxxx_101_xxxxx_0010011: // SRLI Unsigned shift right
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_shift_right_2 = 1;
          ns_arg2_imm_2 = 1;
        end
      32'b01xxxxx_xxxxx_xxxxx_101_xxxxx_0010011: // SRAI Signed shift right
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_shift_right_2 = 1;
          ns_signed_2 = 1;
          ns_arg2_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_110_xxxxx_0010011: // ORI Or immediate
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_or_2 = 1;
          ns_arg2_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_111_xxxxx_0010011: // ANDI And immediate
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_and_2 = 1;
          ns_arg2_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_xxx_xxxxx_0010111: // AUIPC Add upper immediate to PC
        begin
          ns_add_2 = 1;
          ns_write_2 = 1;
          ns_auipc_2 = 1; // Select PC for arg1
          ns_arg2_upper_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_0100011: // SB Store byte
        begin
          ns_uses_rs1_2 = 1;
          ns_store_2 = 1;
          ns_byte_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_0100011: // SH Store halfword
        begin
          ns_uses_rs1_2 = 1;
          ns_store_2 = 1;
          ns_half_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_010_xxxxx_0100011: // SW Store word
        begin
          ns_uses_rs1_2 = 1;
          ns_store_2 = 1;
        end
      32'b0000000_xxxxx_xxxxx_000_xxxxx_0110011: // ADD Add
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_add_2 = 1;
          ns_write_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0100000_xxxxx_xxxxx_000_xxxxx_0110011: // SUB Subtract
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_sub_2 = 1;
          ns_add_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000000_xxxxx_xxxxx_001_xxxxx_0110011: // SLL Shift left
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_shift_left_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000000_xxxxx_xxxxx_010_xxxxx_0110011: // SLT Set if left than signed
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_sub_2 = 1;
          ns_set_less_than_2 = 1;
          ns_signed_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000000_xxxxx_xxxxx_011_xxxxx_0110011: // SLTU Set if left than unsigned
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_sub_2 = 1;
          ns_set_less_than_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000000_xxxxx_xxxxx_100_xxxxx_0110011: // XOR Xor
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_xor_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000000_xxxxx_xxxxx_101_xxxxx_0110011: // SRL Shift right unsigned
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_shift_right_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0100000_xxxxx_xxxxx_101_xxxxx_0110011: // SRA Shift right signed
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_shift_right_2 = 1;
          ns_signed_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000000_xxxxx_xxxxx_110_xxxxx_0110011: // OR Or
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_or_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000000_xxxxx_xxxxx_111_xxxxx_0110011: // AND
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_and_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000001_xxxxx_xxxxx_000_xxxxx_0110011: // MUL
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_mul_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000001_xxxxx_xxxxx_001_xxxxx_0110011: // MULH
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_mul_2 = 1;
          ns_upper_2 = 1;
          ns_signed_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000001_xxxxx_xxxxx_010_xxxxx_0110011: // MULHSU
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_mul_2 = 1;
          ns_upper_2 = 1;
          ns_mixed_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000001_xxxxx_xxxxx_011_xxxxx_0110011: // MULHU
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_mul_2 = 1;
          ns_upper_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000001_xxxxx_xxxxx_100_xxxxx_0110011: // DIV
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_div_2 = 1;
          ns_signed_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000001_xxxxx_xxxxx_101_xxxxx_0110011: // DIVU
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_div_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000001_xxxxx_xxxxx_110_xxxxx_0110011: // REM
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_rem_2 = 1;
          ns_signed_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'b0000001_xxxxx_xxxxx_111_xxxxx_0110011: // REMU
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_write_2 = 1;
          ns_rem_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_xxx_xxxxx_0110111: // LUI
        begin
          ns_add_2 = 1;
          ns_write_2 = 1;
          ns_force_rs1_zero = 1;
          ns_arg2_upper_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_1100011: // BEQ
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_branch_2 = 1;
          ns_sub_2 = 1;
          ns_add_2 = 1;
          ns_eq_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_1100011: // BNE
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_branch_2 = 1;
          ns_sub_2 = 1;
          ns_add_2 = 1;
          ns_ne_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_100_xxxxx_1100011: // BLT
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_branch_2 = 1;
          ns_sub_2 = 1;
          ns_add_2 = 1;
          ns_lt_2 = 1;
          ns_signed_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_101_xxxxx_1100011: // BGE
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_branch_2 = 1;
          ns_sub_2 = 1;
          ns_add_2 = 1;
          ns_ge_2 = 1;
          ns_signed_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_110_xxxxx_1100011: // BLTU
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_branch_2 = 1;
          ns_sub_2 = 1;
          ns_add_2 = 1;
          ns_lt_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_111_xxxxx_1100011: // BGEU
        begin
          ns_uses_rs1_2 = 1;
          ns_uses_rs2_2 = 1;
          ns_branch_2 = 1;
          ns_sub_2 = 1;
          ns_add_2 = 1;
          ns_ge_2 = 1;
          ns_arg2_rs2_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_1100111: // JALR
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_jump_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_xxx_xxxxx_1101111: // JAL
        begin
          ns_write_2 = 1;
          ns_jump_2 = 1;
          ns_jumpimm_2 = 1;
        end
      32'b0000000_xxxxx_xxxxx_000_xxxxx_1110011: // ECALL
        begin
        end
      32'b0000001_xxxxx_xxxxx_000_xxxxx_1110011: // EBREAK
        begin
        end
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_1110011: // CSRRW
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_csr_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_010_xxxxx_1110011: // CSRRS
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_csr_2 = 1;
          ns_csr_set_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_011_xxxxx_1110011: // CSRRC
        begin
          ns_uses_rs1_2 = 1;
          ns_write_2 = 1;
          ns_csr_2 = 1;
          ns_csr_clr_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_101_xxxxx_1110011: // CSRRWI
        begin
          ns_write_2 = 1;
          ns_csr_2 = 1;
          ns_csr_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_110_xxxxx_1110011: // CSRRSI
        begin
          ns_write_2 = 1;
          ns_csr_2 = 1;
          ns_csr_set_2 = 1;
          ns_csr_imm_2 = 1;
        end
      32'bxxxxxxx_xxxxx_xxxxx_111_xxxxx_1110011: // CSRRCI
        begin
          ns_write_2 = 1;
          ns_csr_2 = 1;
          ns_csr_clr_2 = 1;
          ns_csr_imm_2 = 1;
        end
      32'b0011000_00010_00000_000_00000_1110011: // MRET
        begin
          ns_mret_2 = 1;
        end
      32'b0001000_00101_00000_000_00000_1110011: // WFI
        begin
        end
      32'b0001000_1xxxx_00000_000_00000_1110011: // Fake instruction for simulation testing
        begin
          ns_fake_2 = 1;
        end
    endcase

    // NOP this instruction if we jump
    if (jump)
      begin
        ns_write_2 = 0;
        ns_store_2 = 0;
        ns_jump_2 = 0;
        ns_branch_2 = 0;
        ns_load_2 = 0;
        ns_fake_2 = 0;
        ns_csr_2 = 0;
     end
  end

//
// Stage 3; Operate
//

// Stage 3 outputs:

reg load_3;
reg mret_3;
reg csr_3;
reg csr_imm_3;
reg csr_set_3;
reg csr_clr_3;
reg fake_3;
reg write_3;
reg store_3;
reg jump_3;
reg branch_3;
reg byte_3;
reg half_3;
reg signed_3;
reg [31:0] rs2_3;
reg [31:0] rs1_3;
reg [31:0] insn_3;
reg [31:0] pc_3;
reg not_equal_3, ne; // Not equal
reg less_than_3, lt; // Less than
reg eq_3;
reg ne_3;
reg lt_3;
reg ge_3;

reg [31:0] alu_3, ns_alu_3;
wire [31:0] dmem_rd_data_3 = dmem_rd_data;

reg [31:0] return_addr_3, ns_return_addr_3;

reg [31:0] target_addr_3, ns_target_addr_3;

reg [31:0] bypass_rs1;
reg [31:0] bypass_rs2;
reg [31:0] ea; // Computed load address

reg [31:0] dmem_rd_addr_2;
reg [31:0] dmem_rd_addr_3;

always @(posedge clk)
  if (!reset_l)
    begin
      mret_3 <= 0;
      rs2_3 <= 0;
      rs1_3 <= 0;
      alu_3 <= 0;
      return_addr_3 <= 0;
      target_addr_3 <= 0;
      load_3 <= 0;
      fake_3 <= 0;
      csr_3 <= 0;
      csr_imm_3 <= 0;
      csr_set_3 <= 0;
      csr_clr_3 <= 0; 
      write_3 <= 0;
      store_3 <= 0;
      jump_3 <= 0;
      branch_3 <= 0;
      byte_3 <= 0;
      half_3 <= 0;
      signed_3 <= 0;
      insn_3 <= 0;
      pc_3 <= 0;
      dmem_rd_addr_3 <= 0;
      not_equal_3 <= 0;
      less_than_3 <= 0;
      eq_3 <= 0;
      ne_3 <= 0;
      lt_3 <= 0;
      ge_3 <= 0;
    end
  else if (!stall)
    begin
      mret_3 <= mret_2;
      eq_3 <= eq_2;
      ne_3 <= ne_2;
      lt_3 <= lt_2;
      ge_3 <= ge_2;
      alu_3 <= ns_alu_3;
      dmem_rd_addr_3 <= dmem_rd_addr_2;
      return_addr_3 <= ns_return_addr_3;
      target_addr_3 <= ns_target_addr_3;
      // Pass on control bits to next stage
      rs2_3 <= bypass_rs2;
      rs1_3 <= bypass_rs1;
      byte_3 <= byte_2;
      half_3 <= half_2;
      signed_3 <= signed_2;
      insn_3 <= insn_2;
      pc_3 <= pc_2;
      csr_imm_3 <= csr_2;
      csr_set_3 <= csr_set_2;
      csr_clr_3 <= csr_clr_2;
      // NOP this instruction if we jump
      load_3 <= load_2 && !jump && !hazard;
      csr_3 <= csr_2 && !jump && !hazard;
      fake_3 <= fake_2 && !jump && !hazard;
      write_3 <= write_2 && !jump && !hazard;
      store_3 <= store_2 && !jump && !hazard;
      jump_3 <= jump_2 && !jump && !hazard;
      branch_3 <= branch_2 && !jump && !hazard;
      not_equal_3 <= ne;
      less_than_3 <= lt;
    end

reg [31:0] arg1;
reg [31:0] arg2;
reg [31:0] arg2a;
reg [32:0] sum;

// Feed dmem
assign dmem_rd_addr = { dmem_rd_addr_2[31:2], 2'd0 };
assign dmem_rd_req = load_2 && !jump;

// Various forms of immediate
wire [31:0] imm12 = { { 20 { insn_2[31] } }, insn_2[31:20] }; // I-type
wire [31:0] store_imm12 = { { 20 { insn_2[31] } }, insn_2[31:25], insn_2[11:7] }; // S-type
wire [31:0] branch_imm12 = { { 19 { insn_2[31] } }, insn_2[31], insn_2[7], insn_2[30:25], insn_2[11:8], 1'd0 }; // B-Type (WTF?)
wire [31:0] upper_imm20 = { insn_2[31:12], 12'd0 }; // U-type
wire [31:0] jump_imm20 = { { 19 { insn_2[31] } }, insn_2[31], insn_2[19:12], insn_2[20], insn_2[30:21], 1'd0 }; // J-type (WTF?)

wire [4:0] insn_2_rs1 = insn_2[19:15];
wire [4:0] insn_2_rs2 = insn_2[24:20];

reg [31:0] bypass_wr_data;

always @*
  begin
    // Bypass MUXes
    if (rs1_rd_addr_2 == rd_wr_addr && rs1_rd_addr_2 != 0 && rd_we) // Do not bypass x0!
      bypass_rs1 = bypass_wr_data;
    else
      bypass_rs1 = rs1_2;

    if (rs2_rd_addr_2 == rd_wr_addr && rs2_rd_addr_2 != 0 && rd_we) // Do not bypass x0!
      bypass_rs2 = bypass_wr_data;
    else
      bypass_rs2 = rs2_2;

    // Hazard check
    if (load_3 && ((uses_rs1_2 && rs1_rd_addr_2 == rd_wr_addr && rs1_rd_addr_2 != 0 && rd_we) ||
                   (uses_rs2_2 && rs2_rd_addr_2 == rd_wr_addr && rs2_rd_addr_2 != 0 && rd_we)))
      hazard = 1;
    else
      hazard = 0;

    // Compute load address
    ea = bypass_rs1 + imm12;

    // Compute address for dmem load
    dmem_rd_addr_2 = ea;

    // ALU A input
    if (auipc_2)
      arg1 = pc_2;
    else
      arg1 = bypass_rs1;

    // ALU B input
    casex({ arg2_upper_imm_2, arg2_imm_2, arg2_rs2_2 }) // synthesis parallel_case full_case
      3'bxx1: arg2 = bypass_rs2;
      3'bx1x: arg2 = imm12;
      3'b1xx: arg2 = upper_imm20;
    endcase

    // Complement B for subtract
    arg2a = sub_2 ? ~arg2 : arg2;

    // Here is the main adder / subtractor
    sum = { 1'd0, arg1 } + { 1'd0, arg2a } + sub_2;

    //ne = |sum[31:0]; // We are set up for subtraction, but..
    ne = (arg1 != arg2); // This is faster..
    if (signed_2)
      lt = (sum[31] ^ ((sum[31] ^ arg1[31]) & (sum[31] ^ arg2a[31])));
    else
      lt = ~sum[32];

    // ALU operation select
    casex({ shift_left_2, shift_right_2, xor_2, or_2, and_2, set_less_than_2, add_2 }) // synthesis parallel_case full_case
      7'bxxxxxx1: ns_alu_3 = sum[31:0];
      7'bxxxxx1x: ns_alu_3 = lt ? 32'd1 : 32'd0;
      7'bxxxx1xx: ns_alu_3 = arg1 & arg2;
      7'bxxx1xxx: ns_alu_3 = arg1 | arg2;
      7'bxx1xxxx: ns_alu_3 = arg1 ^ arg2;
      7'bx1xxxxx: // ns_alu_3 = { { 31 { arg1[31] & signed_2 } }, arg1 } >> arg2[4:0];

        if (signed_2)
          // ns_alu_3 = arg1 >>> arg2[4:0];
          ns_alu_3 = { { 31 { arg1[31] } }, arg1 } >> arg2[4:0];
        else
          ns_alu_3 = arg1 >> arg2[4:0];
      7'b1xxxxxx: ns_alu_3 = arg1 << arg2[4:0];
    endcase

    // Compute return address in case this is a JAL
    ns_return_addr_3 = pc_2 + 3'd4;

    // Compute branch and store address
    if (branch_2)
      ns_target_addr_3 = pc_2 + branch_imm12; // Use for conditional branch
    else if (jumpimm_2)
      ns_target_addr_3 = pc_2 + jump_imm20; // use for JAL
    else if (store_2)
      ns_target_addr_3 = bypass_rs1 + store_imm12; // Use for store
    else if (mret_2)
      ns_target_addr_3 = csr_mepc;
    else
      ns_target_addr_3 = ea; // ea is rs1 + imm12, use for JALR
  end

//
// Stage 4: write back
//

reg do_exception;

reg mie;
reg mpie;
reg [31:0] csr_mie;
reg [31:0] csr_mtvec;
reg [31:0] csr_mscratch;
reg [31:0] csr_mepc;
reg [31:0] csr_mcause;
reg [31:0] csr_mip;

reg [31:0] result_3;
reg [31:0] selected_load;
reg [31:0] extended_load;
reg [3:0] be_3;

// Write back to register file
assign rd_wr_data = result_3;
assign rd_wr_addr = insn_3[11:7];
assign rd_we = write_3 && !do_exception;

// Store
reg [31:0] store_data;
assign dmem_wr_data = store_data;
assign dmem_wr_addr = target_addr_3;
assign dmem_wr_req = store_3 && !do_exception;
assign dmem_wr_be = be_3;

reg condition_true_3;

reg [31:0] selected_csr;
reg [31:0] updated_csr;
reg [31:0] csr_modifier;

always @*
  begin
    do_exception = 0;
    jump = 0;
    jump_to = target_addr_3;

    // Evaluate branch condition
    casex ({ lt_3, ge_3, ne_3, eq_3}) // synthesis parallel_case full_case
      4'bxxx1: condition_true_3 = ~not_equal_3;
      4'bxx1x: condition_true_3 = not_equal_3;
      4'bx1xx: condition_true_3 = ~less_than_3;
      4'b1xxx: condition_true_3 = less_than_3;
    endcase

    // Jumps and exceptions
    if (mie && |(csr_mip & csr_mie))
      begin
        do_exception = 1;
        jump = 1;
        jump_to = csr_mtvec;
      end
`ifdef STATIC_PREDICT
    else if (branch_3 && !condition_true_3 && pc_2 != pc_3 + 3'd4)
      begin
        jump = 1;
        jump_to = pc_3 + 3'd4;
      end
    else if ((mret_3 || jump_3 || branch_3 && condition_true_3) && pc_2 != target_addr_3)
      begin
        jump = 1;
        jump_to = target_addr_3;
      end
`else
    else if (mret_3)
      begin
        jump = 1;
        jump_to = target_addr_3;
      end
    else if (branch_3 && condition_true_3 || mret_3 || jump_3)
      begin
        jump = 1;
        jump_to = target_addr_3;
      end
`endif

    // dmem write datapath: select byte, half or word
    if (byte_3)
      begin
        store_data = { rs2_3[7:0], rs2_3[7:0], rs2_3[7:0], rs2_3[7:0] };
        be_3 = 4'd1 << dmem_wr_addr[1:0];
      end
    else if (half_3)
      begin
        store_data = { rs2_3[15:0], rs2_3[15:0] };
        be_3 = dmem_wr_addr[1] ? 4'b1100 : 4'b0011;
      end
    else
      begin
        store_data = rs2_3;
        be_3 = 4'b1111;
      end

    // dmem read datapath: select byte, half or word
    if (byte_3)
      case (dmem_rd_addr_3[1:0])
        2'd0: selected_load = { 24'd0, dmem_rd_data[7:0] };
        2'd1: selected_load = { 24'd0, dmem_rd_data[15:8] };
        2'd2: selected_load = { 24'd0, dmem_rd_data[23:16] };
        2'd3: selected_load = { 24'd0, dmem_rd_data[31:24] };
      endcase
    else if (half_3)
      if (dmem_rd_addr_3[1])
        selected_load = { 16'd0, dmem_rd_data[31:16] };
      else
        selected_load = { 16'd0, dmem_rd_data[15:0] };
    else
      selected_load = dmem_rd_data;

    // Sign extend read data if necessary
    if (byte_3 && signed_3)
      extended_load = { { 24 { selected_load[7] } }, selected_load[7:0] };
    else if (half_3 && signed_3)
      extended_load = { { 16 { selected_load[15] } }, selected_load[15:0] };
    else
      extended_load = selected_load;

    // CSR read
    case (insn_3[31:20])
      12'h300: selected_csr = { 24'd0, mpie, 3'd0, mie, 3'd0 }; // mstatus
      12'h304: selected_csr = csr_mie; // mie
      12'h305: selected_csr = csr_mtvec; // mtvec
      12'h340: selected_csr = csr_mscratch;// mscratch
      12'h341: selected_csr = csr_mepc; // mepc
      12'h342: selected_csr = csr_mcause; // mcause
      12'h344: selected_csr = csr_mip; // mip
      default: selected_csr = 0;
    endcase

    if (csr_imm_3)
      csr_modifier = { 27'd0, insn_3[19:15] };
    else
      csr_modifier = rs1_3;

    if (csr_set_3)
      updated_csr = selected_csr | csr_modifier;
    else if (csr_clr_3)
      updated_csr = selected_csr & ~csr_modifier;
    else
      updated_csr = csr_modifier;

    // Select which data to write-back
    if (load_3)
      result_3 = extended_load;
    else if (jump_3)
      result_3 = return_addr_3;
    else if (csr_3)
      result_3 = selected_csr;
    else
      result_3 = alu_3;

    // Don't bypass loads
    if (jump_3)
      bypass_wr_data = return_addr_3;
    else if (csr_3)
      bypass_wr_data = selected_csr;
    else
      bypass_wr_data = alu_3;
  end

always @(posedge clk)
  if (!reset_l)
    begin
      mie <= 0;
      mpie <= 0;
      csr_mie <= 0;
      csr_mtvec <= 0;
      csr_mscratch <= 0;
      csr_mepc <= 0;
      csr_mcause <= 0;
      csr_mip <= 0;
    end
  else if (!stall)
    begin
      csr_mip <= irq; // Interrupt pending
      // Save address of interrupted instruction
      if (do_exception)
        begin
          csr_mepc <= pc_3;
          mie <= 0;
          mpie <= mie;
        end
      // Return from exception: restore interrupt flag
      else if (mret_3)
        begin
          mie <= mpie;
          mpie <= 1;
        end
      else if (csr_3)
        case (insn_3[31:20])
          12'h300: // mstatus
            begin
              mie <= updated_csr[3];
              mpie <= updated_csr[7];
            end
          12'h304: csr_mie <= updated_csr; // mie
          12'h305: csr_mtvec <= updated_csr; // mtvec
          12'h340: csr_mscratch <= updated_csr;// mscratch
          12'h341: csr_mepc <= updated_csr; // mepc
          12'h342: csr_mcause <= updated_csr; // mcause
        endcase
    end

// Generate instruction trace for debugging

wire [31:0] imm12_3 = { { 20 { insn_3[31] } }, insn_3[31:20] }; // I-type
wire [31:0] store_imm12_3 = { { 20 { insn_3[31] } }, insn_3[31:25], insn_3[11:7] }; // S-type
wire [31:0] branch_imm12_3 = { { 19 { insn_3[31] } }, insn_3[31], insn_3[7], insn_3[30:25], insn_3[11:8], 1'd0 }; // B-Type (WTF?)
wire [31:0] upper_imm20_3 = { insn_3[31:12], 12'd0 }; // U-type
wire [31:0] jump_imm20_3 = { { 19 { insn_3[31] } }, insn_3[31], insn_3[19:12], insn_3[20], insn_3[30:21], 1'd0 }; // J-type (WTF?)

always @(posedge clk)
  begin
    // Instruction decoder

    if (csr_3 || mret_3 || jump_3 || store_3 || write_3 || branch_3 || load_3 || fake_3) // Suppress if instruction was NOPd
    casex (insn_3)
      //  f7      rs2   rs1   f3  rd    opcode
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_0000011: // LB Load signed byte
          $display("%h: %h	lb x%0d, 0x%0h(x%0d)	result=%0h", pc_3, insn_3, insn_3[11:7], imm12_3, insn_3[19:15], result_3);
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_0000011: // LH Load signed halfword
          $display("%h: %h	lh R%0d, 0x%0h(R%0d)	result=%0h", pc_3, insn_3, insn_3[11:7], imm12_3, insn_3[19:15], result_3);
      32'bxxxxxxx_xxxxx_xxxxx_010_xxxxx_0000011: // LW Load word
          $display("%h: %h	lw x%0d, 0x%0h(x%0d)	result=%0h", pc_3, insn_3, insn_3[11:7], imm12_3, insn_3[19:15], result_3);
      32'bxxxxxxx_xxxxx_xxxxx_100_xxxxx_0000011: // LBU Load unsigned byte 
          $display("%h: %h	lbu x%0d, 0x%0h(x%0d)	result=%0h", pc_3, insn_3, insn_3[11:7], imm12_3, insn_3[19:15], result_3);
      32'bxxxxxxx_xxxxx_xxxxx_101_xxxxx_0000011: // LHU Load unsigned halfword
          $display("%h: %h	lhu x%0d, 0x%0h(x%0d)	result=%0h", pc_3, insn_3, insn_3[11:7], imm12_3, insn_3[19:15], result_3);
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_0001111: // FENCE
          $display("%h: %h	fence	result=%0h", pc_3, insn_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_0001111: // FENCE.I
          $display("%h: %h	fence	result=%0h", pc_3, insn_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_0010011: // ADDI Add immediate
          $display("%h: %h	addi x%0d, x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], imm12_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_0010011: // SLLI Shift left immediate
          $display("%h: %h	slli x%0d, x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], imm12_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_010_xxxxx_0010011: // SLTI Set if less than immediate signed
          $display("%h: %h	slti x%0d, x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], imm12_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_011_xxxxx_0010011: // SLTIU Set if less than immediate unsigned
          $display("%h: %h	sltiu x%0d, x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], imm12_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_100_xxxxx_0010011: // XORI Xor immediate
          $display("%h: %h	xori x%0d, x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], imm12_3, result_3);
      32'b00xxxxx_xxxxx_xxxxx_101_xxxxx_0010011: // SRLI Unsigned shift right
          $display("%h: %h	srli x%0d, x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], imm12_3, result_3);
      32'b01xxxxx_xxxxx_xxxxx_101_xxxxx_0010011: // SRAI Signed shift right
          $display("%h: %h	srai x%0d, x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], imm12_3[4:0], result_3);
      32'bxxxxxxx_xxxxx_xxxxx_110_xxxxx_0010011: // ORI Or immediate
          $display("%h: %h	ori x%0d, x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], imm12_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_111_xxxxx_0010011: // ANDI And immediate
          $display("%h: %h	andi x%0d, x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], imm12_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_xxx_xxxxx_0010111: // AUIPC Add upper immediate to PC
          $display("%h: %h	auipc x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], upper_imm20_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_0100011: // SB Store byte
          $display("%h: %h	sb x%0d, 0x%0h(x%0d)	result=%0h", pc_3, insn_3, insn_3[24:20], store_imm12_3, insn_3[19:15], result_3);
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_0100011: // SH Store halfword
          $display("%h: %h	sh x%0d, 0x%0h(x%0d)	result=%0h", pc_3, insn_3, insn_3[24:20], store_imm12_3, insn_3[19:15], result_3);
      32'bxxxxxxx_xxxxx_xxxxx_010_xxxxx_0100011: // SW Store word
          $display("%h: %h	sw x%0d, 0x%0h(x%0d)	result=%0h", pc_3, insn_3, insn_3[24:20], store_imm12_3, insn_3[19:15], result_3);
      32'b0000000_xxxxx_xxxxx_000_xxxxx_0110011: // ADD Add
          $display("%h: %h	add x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0100000_xxxxx_xxxxx_000_xxxxx_0110011: // SUB Subtract
          $display("%h: %h	sub x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000000_xxxxx_xxxxx_001_xxxxx_0110011: // SLL Shift left
          $display("%h: %h	sll x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000000_xxxxx_xxxxx_010_xxxxx_0110011: // SLT Set if left than signed
          $display("%h: %h	slt x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000000_xxxxx_xxxxx_011_xxxxx_0110011: // SLTU Set if left than unsigned
          $display("%h: %h	sltu x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000000_xxxxx_xxxxx_100_xxxxx_0110011: // XOR Xor
          $display("%h: %h	xor x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000000_xxxxx_xxxxx_101_xxxxx_0110011: // SRL Shift right unsigned
          $display("%h: %h	srl x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0100000_xxxxx_xxxxx_101_xxxxx_0110011: // SRA Shift right signed
          $display("%h: %h	sra x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000000_xxxxx_xxxxx_110_xxxxx_0110011: // OR Or
          $display("%h: %h	or x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000000_xxxxx_xxxxx_111_xxxxx_0110011: // AND
          $display("%h: %h	and x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000001_xxxxx_xxxxx_000_xxxxx_0110011: // MUL
          $display("%h: %h	mul x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000001_xxxxx_xxxxx_001_xxxxx_0110011: // MULH
          $display("%h: %h	mulh x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000001_xxxxx_xxxxx_010_xxxxx_0110011: // MULHSU
          $display("%h: %h	mulh x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000001_xxxxx_xxxxx_011_xxxxx_0110011: // MULHU
          $display("%h: %h	mulhu x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000001_xxxxx_xxxxx_100_xxxxx_0110011: // DIV
          $display("%h: %h	div x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000001_xxxxx_xxxxx_101_xxxxx_0110011: // DIVU
          $display("%h: %h	divu x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000001_xxxxx_xxxxx_110_xxxxx_0110011: // REM
          $display("%h: %h	rem x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'b0000001_xxxxx_xxxxx_111_xxxxx_0110011: // REMU
          $display("%h: %h	remu x%0d, x%0d, x%0d	result=%0h", pc_3, insn_3, insn_3[11:7], insn_3[19:15], insn_3[24:20], result_3);
      32'bxxxxxxx_xxxxx_xxxxx_xxx_xxxxx_0110111: // LUI
          $display("%h: %h	lui  x%0d, 0x%0h", pc_3, insn_3, insn_3[11:7], upper_imm20_3);
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_1100011: // BEQ
          $display("%h: %h	beq  x%0d, x%0d, 0x%0h", pc_3, insn_3, insn_3[19:15], insn_3[24:20], pc_3 + { { 19 { insn_3[31] } }, insn_3[31], insn_3[7], insn_3[30:25], insn_3[11:8], 1'd0 });
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_1100011: // BNE
          $display("%h: %h	bne  x%0d, x%0d, 0x%0h", pc_3, insn_3, insn_3[19:15], insn_3[24:20], pc_3 + { { 19 { insn_3[31] } }, insn_3[31], insn_3[7], insn_3[30:25], insn_3[11:8], 1'd0 });
      32'bxxxxxxx_xxxxx_xxxxx_100_xxxxx_1100011: // BLT
          $display("%h: %h	blt  x%0d, x%0d, 0x%0h", pc_3, insn_3, insn_3[19:15], insn_3[24:20], pc_3 + { { 19 { insn_3[31] } }, insn_3[31], insn_3[7], insn_3[30:25], insn_3[11:8], 1'd0 });
      32'bxxxxxxx_xxxxx_xxxxx_101_xxxxx_1100011: // BGE
          $display("%h: %h	bge  x%0d, x%0d, 0x%0h", pc_3, insn_3, insn_3[19:15], insn_3[24:20], pc_3 + { { 19 { insn_3[31] } }, insn_3[31], insn_3[7], insn_3[30:25], insn_3[11:8], 1'd0 });
      32'bxxxxxxx_xxxxx_xxxxx_110_xxxxx_1100011: // BLTU
          $display("%h: %h	bltu  x%0d, x%0d, 0x%0h", pc_3, insn_3, insn_3[19:15], insn_3[24:20], pc_3 + { { 19 { insn_3[31] } }, insn_3[31], insn_3[7], insn_3[30:25], insn_3[11:8], 1'd0 });
      32'bxxxxxxx_xxxxx_xxxxx_111_xxxxx_1100011: // BGEU
          $display("%h: %h	bgeu  x%0d, x%0d, 0x%0h", pc_3, insn_3, insn_3[19:15], insn_3[24:20], pc_3 + { { 19 { insn_3[31] } }, insn_3[31], insn_3[7], insn_3[30:25], insn_3[11:8], 1'd0 });
      32'bxxxxxxx_xxxxx_xxxxx_000_xxxxx_1100111: // JALR
          $display("%h: %h	jalr  x%0d, x%0d, %0d	result=%0h", pc_3, insn_3, insn_3[19:15], insn_3[24:20], pc_3 + { { 19 { insn_3[31] } }, insn_3[31], insn_3[7], insn_3[30:25], insn_3[11:8], 1'd0 }, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_xxx_xxxxx_1101111: // JAL
          $display("%h: %h	jal x%0d, 0x%0h	result=%0h", pc_3, insn_3, insn_3[11:7], pc_3 + jump_imm20_3, result_3);
      32'b0000000_xxxxx_xxxxx_000_xxxxx_1110011: // ECALL
          $display("%h: %h	ecall	result=%0h", pc_3, insn_3, result_3);
      32'b0000001_xxxxx_xxxxx_000_xxxxx_1110011: // EBREAK
          $display("%h: %h	ebreak	result=%0h", pc_3, insn_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_001_xxxxx_1110011: // CSRRW
          $display("%h: %h	csrrw	result=%0h", pc_3, insn_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_010_xxxxx_1110011: // CSRRS
          $display("%h: %h	csrrs	result=%0h", pc_3, insn_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_011_xxxxx_1110011: // CSRRC
          $display("%h: %h	csrrc	result=%0h", pc_3, insn_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_101_xxxxx_1110011: // CSRRWI
          $display("%h: %h	csrrwi	result=%0h", pc_3, insn_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_110_xxxxx_1110011: // CSRRSI
          $display("%h: %h	csrrsi	result=%0h", pc_3, insn_3, result_3);
      32'bxxxxxxx_xxxxx_xxxxx_111_xxxxx_1110011: // CSRRCI
          $display("%h: %h	csrrci	result=%0h", pc_3, insn_3, result_3);
      32'b0011000_00010_00000_000_00000_1110011: // MRET
          $display("%h: %h	mret	result=%0h", pc_3, insn_3, result_3);
      32'b0001000_00101_00000_000_00000_1110011: // WFI
          $display("%h: %h	wfi	result=%0h", pc_3, insn_3, result_3);
      32'b0001000_10000_00000_000_00000_1110011: // Fake instruction for testing
        begin
          $display("%h: %h	Test passed!", pc_3, insn_3);
          $finish;
        end
      32'b0001000_10001_00000_000_00000_1110011: // Fake instruction for testing
        begin
          $display("%h: %h	Test failed!", pc_3, insn_3);
          $finish;
        end
    endcase
  end

endmodule
