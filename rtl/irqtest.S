#define r_type_insn(_f7, _rs2, _rs1, _f3, _rd, _opc) \
	.word (((_f7) << 25) | ((_rs2) << 20) | ((_rs1) << 15) | ((_f3) << 12) | ((_rd) << 7) | ((_opc) << 0))

#define pass r_type_insn(0b0001000, 0b10000, 0b00000, 0b000, 0b00000, 0b1110011)
#define fail r_type_insn(0b0001000, 0b10001, 0b00000, 0b000, 0b00000, 0b1110011)

	.section	.text

	la	x1, irq_handler
	li	x2, 0

	csrw	0x305, x1	// Set interrupt handler address
	csrsi	0x300, 0x8	// Enable interrupts
	csrsi	0x304, 0x1	// Enable interrupt no. 1
 
repeat:	addi	x1, zero, 200
loop:	addi	x1, x1, -1
	bne	x1, zero, loop
	li	x3, 2
	beq	x2, x3, passit
	fail
passit:	pass


irq_handler:
	addi	x2, x2, 1
	mret
