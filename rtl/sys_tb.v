module tb;

reg clk;
reg reset_l;
reg irq;

sys sys
  (
  .clk (clk),
  .reset_l (reset_l),
  .irq (irq)
  );

always
  begin
    #50 clk <= !clk;
  end

integer x;

initial
  begin
    $readmemh("rv0.mem", sys.dmem_0.ram);
    $readmemh("rv1.mem", sys.dmem_1.ram);
    $readmemh("rv2.mem", sys.dmem_2.ram);
    $readmemh("rv3.mem", sys.dmem_3.ram);
    $dumpvars(0);
    $dumpon;
    $display("Hi there!\n");
    clk <= 0;
    reset_l <= 1;
    irq <= 0;
    // Clear x0
    // FPGA does this in the background
    sys.nanorv32.rs1_ram.ram[0] = 0;
    sys.nanorv32.rs2_ram.ram[0] = 0;
    @(posedge clk);
    @(posedge clk);
    reset_l <= 0;
    @(posedge clk);
    @(posedge clk);
    reset_l <= 1;
    @(posedge clk);
    @(posedge clk);

    for (x = 0; x != 1000; x = x + 1)
      begin
        if (x == 200)
          irq <= 1;
        if (x == 203)
          irq <= 0;
        if (x == 400)
          irq <= 1;
        if (x == 403)
          irq <= 0;
        @(posedge clk);
      end
 
    $finish;
  end

endmodule
