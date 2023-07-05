module sys
  (
  reset_l,
  clk,
  irq,
  inport,
  outport,
  );

parameter ROMFILE="rv.mem";

parameter RAMWIDTH=12;
parameter ROMWIDTH=12;

input reset_l;
input clk;
input irq;

input [31:0] inport;
output [31:0] outport;

wire [31:0] imem_rd_addr;
wire [31:0] imem_rd_data;

wire [31:0] dmem_rd_addr;
wire dmem_rd_req;
wire [31:0] dmem_rd_data;

wire [31:0] dmem_wr_addr;
wire [31:0] dmem_wr_data;
wire [3:0] dmem_wr_be;
wire dmem_wr_req;

reg [31:0] inport_reg;
reg [31:0] outport;
reg inport_ack;

nanorv32 nanorv32
  (
  .clk (clk),
  .reset_l (reset_l),

  .stall (1'd0),
  .irq ({ 31'd0, irq }),

  .imem_rd_addr (imem_rd_addr),
  .imem_rd_data (imem_rd_data),

  .dmem_rd_addr (dmem_rd_addr),
  .dmem_rd_req (dmem_rd_req),
  .dmem_rd_data (inport_ack ? inport_reg : dmem_rd_data),

  .dmem_wr_addr (dmem_wr_addr),
  .dmem_wr_data (dmem_wr_data),
  .dmem_wr_be (dmem_wr_be),
  .dmem_wr_req (dmem_wr_req)
  );

always @(posedge clk)
  if (!reset_l)
    begin
      outport <= 0;
      inport_ack <= 0;
      inport_reg <= 0;
    end
  else
    begin
      inport_ack <= 0;
      inport_reg <= inport;
      if (dmem_wr_addr == 32'h1000_0000 && dmem_wr_req)
        outport <= dmem_wr_data;
      if (dmem_rd_addr == 32'h1000_0000 && dmem_rd_req)
        inport_ack <= 1;
    end

rom #(.ADDRWIDTH(ROMWIDTH-2), .INIT_FILE(ROMFILE)) rom
  (
  .clk (clk),
  .rd_addr (imem_rd_addr[ROMWIDTH-1:2]),
  .rd_data (imem_rd_data)
  );

ram_blk_dp_bypassed #(.ADDRWIDTH(RAMWIDTH-2), .DATAWIDTH(8)) dmem_0
  (
  .clk (clk),

  .wr_data (dmem_wr_data[7:0]),
  .wr_addr (dmem_wr_addr[RAMWIDTH-1:2]),
  .we (dmem_wr_req && dmem_wr_be[0]),

  .rd_data (dmem_rd_data[7:0]),
  .rd_addr (dmem_rd_addr[RAMWIDTH-1:2])
  );

ram_blk_dp_bypassed #(.ADDRWIDTH(RAMWIDTH-2), .DATAWIDTH(8)) dmem_1
  (
  .clk (clk),

  .wr_data (dmem_wr_data[15:8]),
  .wr_addr (dmem_wr_addr[RAMWIDTH-1:2]),
  .we (dmem_wr_req && dmem_wr_be[1]),

  .rd_data (dmem_rd_data[15:8]),
  .rd_addr (dmem_rd_addr[RAMWIDTH-1:2])
  );

ram_blk_dp_bypassed #(.ADDRWIDTH(RAMWIDTH-2), .DATAWIDTH(8)) dmem_2
  (
  .clk (clk),

  .wr_data (dmem_wr_data[23:16]),
  .wr_addr (dmem_wr_addr[RAMWIDTH-1:2]),
  .we (dmem_wr_req && dmem_wr_be[2]),

  .rd_data (dmem_rd_data[23:16]),
  .rd_addr (dmem_rd_addr[RAMWIDTH-1:2])
  );

ram_blk_dp_bypassed #(.ADDRWIDTH(RAMWIDTH-2), .DATAWIDTH(8)) dmem_3
  (
  .clk (clk),

  .wr_data (dmem_wr_data[31:24]),
  .wr_addr (dmem_wr_addr[RAMWIDTH-1:2]),
  .we (dmem_wr_req && dmem_wr_be[3]),

  .rd_data (dmem_rd_data[31:24]),
  .rd_addr (dmem_rd_addr[RAMWIDTH-1:2])
  );

endmodule
