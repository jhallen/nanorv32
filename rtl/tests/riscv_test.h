#ifndef _ENV_PICORV32_TEST_H
#define _ENV_PICORV32_TEST_H

#define r_type_insn(_f7, _rs2, _rs1, _f3, _rd, _opc) \
	.word (((_f7) << 25) | ((_rs2) << 20) | ((_rs1) << 15) | ((_f3) << 12) | ((_rd) << 7) | ((_opc) << 0))

#define pass_insn r_type_insn(0b0001000, 0b10000, 0b00000, 0b000, 0b00000, 0b1110011)
#define fail_insn r_type_insn(0b0001000, 0b10001, 0b00000, 0b000, 0b00000, 0b1110011)


#ifndef TEST_FUNC_NAME
#  define TEST_FUNC_NAME mytest
#  define TEST_FUNC_TXT "mytest"
#  define TEST_FUNC_RET mytest_ret
#endif

#define RVTEST_RV32U
#define TESTNUM x28

#define RVTEST_CODE_BEGIN		\
	.text;				\

#define RVTEST_PASS			\
	pass_insn

#define RVTEST_FAIL			\
	fail_insn

#define RVTEST_CODE_END
#define RVTEST_DATA_BEGIN .balign 4;
#define RVTEST_DATA_END

#endif
