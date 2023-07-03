module tb;

reg clk;
reg reset_l;

sys sys
  (
  .clk (clk),
  .reset_l (reset_l)
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
    // Clear x0
    // FPGA does this in the background
    sys.rv.rs1_ram.ram[0] = 0;
    sys.rv.rs2_ram.ram[0] = 0;
    @(posedge clk);
    @(posedge clk);
    reset_l <= 0;
    @(posedge clk);
    @(posedge clk);
    reset_l <= 1;
    @(posedge clk);
    @(posedge clk);

    for (x = 0; x != 1000; x = x + 1)
      @(posedge clk);

    $finish;
  end

endmodule
