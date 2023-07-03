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

all: $(TESTS)

%: %.S
	@echo
	@echo Runing test $*...
	@echo
	make -f Makefile.single TEST=$*.o
	iverilog -g2001 rv.v sys.v sys_tb.v ram_dist_dp.v ram_blk_dp_bypassed.v rom.v && ./a.out | awk -f check.awk
	@echo
	@echo Test $* Passed!
	@echo

clean:
	rm -f tests/*.o
