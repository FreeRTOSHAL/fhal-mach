//------------------------------------------------------------------------------
// The confidential and proprietary information contained in this file may
// only be used by a person authorised under and to the extent permitted
// by a subsisting licensing agreement from ARM Limited.
//
//            (C) COPYRIGHT 2010 ARM Limited.
//                ALL RIGHTS RESERVED
//
// This entire notice must be reproduced on all copies of this file
// and copies of this file may only be made by a person if such person is
// permitted to do so under the terms of a subsisting license agreement
// from ARM Limited.
//
//      SVN Information
//
//      Checked In          : 2010-08-03 21:05:56 +0100 (Tue, 03 Aug 2010)
//
//      Revision            : 144987
//
//      Release Information : AT510-MN-80001-r0p0-00rel0
//------------------------------------------------------------------------------

//------------------------------------------------------------------------------
// Cortex-M0 DesignStart testbench example
//------------------------------------------------------------------------------

module cortexm0ds_tb ();

//------------------------------------------------------------------------------
// Define parameters for clock period and power-on reset delay
//------------------------------------------------------------------------------

localparam clk_period = 2;            // Simulation cycles per clock period
localparam por_delay  = 1001;           // Simulation cycles of power-on-reset
localparam ram_log2   = 18;             // Power of two of RAM words
localparam addr_tty   = 32'h40000000;   // Address of output console
localparam addr_tty2  = 32'h40001000;   // Address of output console

//------------------------------------------------------------------------------
// Define registers for clock, reset and memory
//------------------------------------------------------------------------------

reg sim_clock;                          // System clock
reg power_on_reset_n;                   // Power-on reset signal
reg [31:0] ram [0:(2**ram_log2)-1];     // Storage for AHB memory model

//------------------------------------------------------------------------------
// Cortex-M0 DesignStart signal list
//------------------------------------------------------------------------------

// See the AMBA(r)3 AHB-Lite Protocol Specification v1.0 (ARM IHI 0033),
// and the Cortex(tm)-M0 Technical Reference Manual (ARM DDI 0432), for
// further details on the following signals:

wire        HCLK;               // AHB-Lite interface and CPU master clock
wire        HRESETn;            // AHB-Lite active-low reset signal

wire [31:0] HADDR;              // AHB-Lite byte address
wire [ 2:0] HBURST;             // AHB-Lite burst type (not used by testbench)
wire        HMASTLOCK;          // AHB-Lite locked transaction (always zero)
wire [ 3:0] HPROT;              // AHB-Lite protection (not used by testbench)
wire [ 2:0] HSIZE;              // AHB-Lite size (# of bits: 0=8, 1=16, 2=32)
wire [ 1:0] HTRANS;             // AHB-Lite perform transaction
wire [31:0] HWDATA;             // AHB-Lite write-data
wire        HWRITE;             // AHB-Lite transaction is write not read
wire [31:0] HRDATA;             // AHB-Lite read-data
wire        HREADY;             // AHB-Lite bus ready signal
wire        HRESP;              // AHB-Lite bus error (not used by testbench)

// See the ARMv6-M Architecture Reference Manual (ARM DDI 0419), and the
// Cortex(tm)-M0 Technical Reference Manual (ARM DDI 0432), for further
// details on the following signals:

wire        NMI;                // Non-maskable interrupt input (not used by tb)
wire [15:0] IRQ;                // Interrupt inputs (not used by testbench)

wire        TXEV;               // Event output (CPU executed SEV instruction)
wire        RXEV;               // Event input (not used by testbench)

wire        LOCKUP;             // CPU stopped due to multiple software errors
wire        SYSRESETREQ;        // CPU request for system to be reset

wire        SLEEPING;           // CPU is sleeping (not used by testbench)

//------------------------------------------------------------------------------
// Generate system clock, power-on reset and synchronized AHB reset signals
//------------------------------------------------------------------------------

// Generate a clock of the appropriate period
initial
  #0 sim_clock = 1'b0;

always @(sim_clock)
  #(clk_period/2) sim_clock <= ~sim_clock;

// Release the active-low power-on reset signal after the given delay
initial begin
  #0 power_on_reset_n = 1'b0;
  #(por_delay) power_on_reset_n = 1'b1;
end

// Synchronize AHB reset, and factor in reset request from the CPU
reg [1:0] rst_sync;
always @(posedge sim_clock or negedge power_on_reset_n)
  if(!power_on_reset_n)
    rst_sync <= 2'b00;
  else
    rst_sync <= {rst_sync[0],~SYSRESETREQ};

//------------------------------------------------------------------------------
// Connect clock and reset to AHB signals and assign static signals
//------------------------------------------------------------------------------

assign HCLK    = sim_clock;    // Assign AHB clock from simulation clock
assign HRESETn = rst_sync[1];  // Assign AHB clock from synchronizer
assign HREADY  = 1'b1;         // All devices are zero-wait-state
assign HRESP   = 1'b0;         // No device in this system generates errors
assign NMI     = 1'b0;         // Do not generate any non-maskable interrupts
assign IRQ     = {16{1'b0}};   // Do not generate any interrupts
assign RXEV    = 1'b0;         // Do not generate any external events

//------------------------------------------------------------------------------
// Instantiate Cortex-M0 DesignStart processor macro cell
//------------------------------------------------------------------------------

CORTEXM0DS u_cortexm0ds (
  .HCLK        (HCLK),
  .HRESETn     (HRESETn),
  .HADDR       (HADDR[31:0]),
  .HBURST      (HBURST[2:0]),
  .HMASTLOCK   (HMASTLOCK),
  .HPROT       (HPROT[3:0]),
  .HSIZE       (HSIZE[2:0]),
  .HTRANS      (HTRANS[1:0]),
  .HWDATA      (HWDATA[31:0]),
  .HWRITE      (HWRITE),
  .HRDATA      (HRDATA[31:0]),
  .HREADY      (HREADY),
  .HRESP       (HRESP),
  .NMI         (NMI),
  .IRQ         (IRQ[15:0]),
  .TXEV        (TXEV),
  .RXEV        (RXEV),
  .LOCKUP      (LOCKUP),
  .SYSRESETREQ (SYSRESETREQ),
  .SLEEPING    (SLEEPING)
);

//------------------------------------------------------------------------------
// Simulation model of an AHB memory
//------------------------------------------------------------------------------

// Initialize memory content from "ram.bin"
integer fd, i;
reg [31:0] data;

initial begin
  $display("%t: ----------------------------------------------", $time);
  $display("%t: ARM(r) Cortex(tm)-M0 DesignStart(tm) Testbench", $time);
  $display("%t: (c) Copyright 2010 ARM Limited", $time);
  $display("%t: All Rights Reserved", $time);
  $display("%t: ----------------------------------------------\n", $time);
  $display("%t: Loading initial memory content...", $time);
  fd = $fopen("test.bin","rb");
  for (i = 0; (i < (2**ram_log2)) && ($fread(data,fd) != -1); i = i + 1)
    ram[i] = {data[7:0],data[15:8],data[23:16],data[31:24]};
  $display("%t: ...complete\n", $time);
  $dumpfile("a.out.vcd");
  $dumpvars(0, cortexm0ds_tb );
end

// Record transaction information from last accepted address phase
reg [ 1:0] htrans_last;
reg        hwrite_last;
reg [31:0] haddr_last;
reg [ 2:0] hsize_last;

always @(posedge HCLK)
  if (HREADY) begin
    htrans_last <= HTRANS;
    hwrite_last <= HWRITE;
    haddr_last  <= HADDR;
    hsize_last  <= HSIZE;
  end

// Select RAM only if between address zero and top of RAM
wire hsel_ram = ~|haddr_last[31:ram_log2];

assign HRDATA[31:0] = hsel_ram ? ram[haddr_last[ram_log2+1:2]] : 32'd0;

reg [31:0] ram_tmp;

always @(posedge HCLK)
  if(HREADY & hwrite_last & hsel_ram & htrans_last[1]) begin

    // Extract RAM entry into temporary buffer
    ram_tmp = ram[haddr_last[ram_log2+1:2]];

    // Insert appropriate bytes from AHB-Lite transaction
    case({hsize_last[1:0], haddr_last[1:0]})
      // Byte writes are valid to any address
      4'b00_00 : ram_tmp[ 7: 0] = HWDATA[ 7: 0];
      4'b00_01 : ram_tmp[15: 8] = HWDATA[15: 8];
      4'b00_10 : ram_tmp[23:16] = HWDATA[23:16];
      4'b00_11 : ram_tmp[31:24] = HWDATA[31:24];
      // Halfword writes are only valid to even addresses
      4'b01_00 : ram_tmp[15: 0] = HWDATA[15: 0];
      4'b01_10 : ram_tmp[31:16] = HWDATA[31:16];
      // Word writes are only valid to word aligned addresses
      4'b10_00 : ram_tmp[31: 0] = HWDATA[31: 0];
      default  : begin
        $display("%t: Illegal AHB transaction, stopping simulation\n", $time);
        $finish(2);
      end
    endcase
    // $display("%t: 0x%x = 0x%x\n", $time, haddr_last[ram_log2+1:2], ram_tmp);

    // Commit write to RAM model
    ram[haddr_last[ram_log2+1:2]] <= ram_tmp;

  end

//------------------------------------------------------------------------------
// Simulation model of a simple AHB output console
//------------------------------------------------------------------------------

wire hsel_tty = (haddr_last == addr_tty);

always @(posedge HCLK)
  if(HRESETn & HREADY & hwrite_last & hsel_tty & htrans_last[1]) begin
    if(HWDATA[7:0] != 8'hFF)
      $write("%c", HWDATA[7:0]);
    else begin
      $display("%t: Simulation stop requested by CPU\n", $time);
      $finish(2);
    end
  end

wire hsel_tty2 = (haddr_last == addr_tty2);

always @(posedge HCLK)
  if(HRESETn & HREADY & hwrite_last & hsel_tty2 & htrans_last[1]) begin
    if(HWDATA[7:0] != 8'hFF)
      $write("%c", HWDATA[7:0]);
    else begin
      $display("%t: Simulation stop requested by CPU\n", $time);
      $finish(2);
    end
  end

//------------------------------------------------------------------------------
// Simulation commentary
//------------------------------------------------------------------------------

always @(posedge HRESETn)
  $display("%t: Simulation leaving reset", $time);

always @(posedge HCLK)
  if (HRESETn & LOCKUP) begin
    $display("%t: CPU LOCKUP asserted, stopping simulation\n", $time);
    #(clk_period * 32)
    $finish(2);
  end

always @(posedge HCLK)
  if (HRESETn & TXEV) begin
    $display("%t: CPU executed SEV instruction and asserted TXEV\n", $time);
  end

always @(posedge HCLK)
  if (HRESETn & HREADY & htrans_last[1] & ~(hsel_ram | hsel_tty | hsel_tty2))
    $display("%t: Warning, address %x selects neither RAM or console",
      $time, haddr_last);

endmodule // cortexm0ds_tb
