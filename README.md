# nanorv32

Nanorv32 is intended to be a more efficient but lower fMAX version of
Clifford Wolf's "picorv32." This means that it is intended to be used as a
microcontroller core, so no MMU is included and it can not run Linux. 
Nanorv32 will run at approximately one cycle per instruction instead of 3 or
4.

Nanorv32 has a four stage pipeline: fetch, decode / register read, execute /
load / store and write-back.  All instructions execute in one cycle except
for multply and divide, a mispredicted branch or when there is a stall due
to a pipeline hazard.

Nanorv32 is bypassed, so there are few pipeline stalls due to hazards. 
However there is one case: when a load is followed by an instruction that
uses the load result, there is a one cycle delay.  This hazard could be
eliminated with a bypass MUX, but doing so puts the data load in series with
the ALU, and the impact on fMAX is too much.  Instead we choose to stall
this case.

Nanorv32 uses a static branch predictor.  This means that the fetch stage
calculates JAL targets, so JAL takes one cycle.  It also calculates
conditional branch targets and assumes conditional branches are taken.  So
conditional branches take one cycle unless the condition fails, in which
case they take three cycles.  JALR always takes three cycles.

# Interface

# Tests

To run the tests, type "make".

