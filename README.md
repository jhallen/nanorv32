# nanorv32

This is intended to be a more efficient but lower fMAX version of Clifford
Wolf's "picorv32."  This means that it is intended to be used as a
microcontroller core, so no MMU or Linux support.  Compared with picorv32,
nanorv32 will run at approximately one cycle per instruction instead of 3 or
4.

Nanorv32 has a four stage pipeline: fetch, decode / register read, execute /
load / store and write-back.  All instructions execute in one cycle except
for multply and divide or when there is a stall due to a pipeline hazard.

Nanorv32 is bypassed, so there are very few pipeline stalls due to hazards. 
However there is one case: when a load is followed by an instruction that
uses the load result, there is a one cycle delay.  This hazard could be
eliminated with a bypass MUX, but doing so puts the data load in series with
the ALU, and the impact on fMAX is too much.  Instead we choose to stall
this case.

# Interface

# Tests

To run the tests, type "make".

