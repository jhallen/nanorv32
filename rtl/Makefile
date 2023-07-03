TESTS = \
tests/addi \
tests/add \
tests/andi \
tests/and \
tests/auipc \
tests/beq \
tests/bge \
tests/bgeu \
tests/blt \
tests/bltu \
tests/bne \
tests/jal \
tests/jalr \
tests/j \
tests/lb \
tests/lbu \
tests/lh \
tests/lhu \
tests/lui \
tests/lw \
tests/ori \
tests/or \
tests/sb \
tests/sh \
tests/slli \
tests/sll \
tests/slti \
tests/slt \
tests/srai \
tests/sra \
tests/srli \
tests/srl \
tests/sub \
tests/sw \
tests/xori \
tests/xor \

SRCS = nanorv32.v sys.v sys_tb.v ram_dist_dp.v ram_blk_dp_bypassed.v rom.v

all: $(TESTS)

%: %.S
	@echo
	@echo Runing test $*...
	@echo
	make -f Makefile.single TEST=$*.o
	iverilog -g2001 $(SRCS) && ./a.out | awk -e 'BEGIN { err = 1 }; /Test passed/ { err = 0 }; // { print }; END { exit err }'
	@echo
	@echo Test $* Passed!
	@echo

clean:
	rm -f tests/*.o
