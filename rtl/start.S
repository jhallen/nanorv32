#define r_type_insn(_f7, _rs2, _rs1, _f3, _rd, _opc) \
	.word (((_f7) << 25) | ((_rs2) << 20) | ((_rs1) << 15) | ((_f3) << 12) | ((_rd) << 7) | ((_opc) << 0))

#define pass r_type_insn(0b0001000, 0b10000, 0b00000, 0b000, 0b00000, 0b1110011)
#define fail r_type_insn(0b0001000, 0b10001, 0b00000, 0b000, 0b00000, 0b1110011)

	.section	.text

reset_vec:
	# zero-initialize register file
	addi x1, zero, 0
	addi x2, zero, 0
	addi x3, zero, 0
	addi x4, zero, 0
	addi x5, zero, 0
	addi x6, zero, 0
	addi x7, zero, 0
	addi x8, zero, 0
	addi x9, zero, 0
	addi x10, zero, 0
	addi x11, zero, 0
	addi x12, zero, 0
	addi x13, zero, 0
	addi x14, zero, 0
	addi x15, zero, 0
	addi x16, zero, 0
	addi x17, zero, 0
	addi x18, zero, 0
	addi x19, zero, 0
	addi x20, zero, 0
	addi x21, zero, 0
	addi x22, zero, 0
	addi x23, zero, 0
	addi x24, zero, 0
	addi x25, zero, 0
	addi x26, zero, 0
	addi x27, zero, 0
	addi x28, zero, 0
	addi x29, zero, 0
	addi x30, zero, 0
	addi x31, zero, 0

loop:
	# Update LEDs
	li a0, 0x03
	li a1, 1
	sw a1, 0(a0)

	# Update LEDs
	li a0, 0x03
	li a1, 3
	sw a1, 0(a0)

	li a2, 10
	li a3, 5
inner:
	addi a2, a2, -1
	bge a2, a3, inner

	fail

	j loop
