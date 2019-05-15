//EE382M-Verification of Digital Systems
//Lab 4 - Formal Property Verification
//
//
//Module - arbiter_top
//Instantiates arbiter and apb slave interface

module arbiter_top (
  PCLK, 
  PRESETn, 
  PADDR, 
  PWRITE, 
  PSEL, 
  PENABLE, 
  PWDATA, 
  PRDATA, 
  PREADY,
  APB_BYPASS,
  APB_REQ,
  APB_ARB_TYPE,
  REQ,
  GNT
  );

// APB interface
input        PCLK;
input        PRESETn;
input        PWRITE;
input        PSEL;
input        PENABLE;
input  [7:0] PADDR;
input  [7:0] PWDATA;

output [7:0] PRDATA;
output       PREADY;

// APB registers
output       APB_BYPASS;
output [3:0] APB_REQ;
output [2:0] APB_ARB_TYPE;

// Arbiter ports
input  [3:0] REQ;
output [3:0] GNT;

// APB slave: APB registers
apb_slave u_apb_slave ( 
  .PCLK(PCLK), 
  .PRESETn(PRESETn), 
  .PADDR(PADDR), 
  .PWRITE(PWRITE), 
  .PSEL(PSEL), 
  .PENABLE(PENABLE), 
  .PWDATA(PWDATA), 
  .PRDATA(PRDATA), 
  .PREADY(PREADY),
  .APB_BYPASS(APB_BYPASS),
  .APB_REQ(APB_REQ),
  .APB_ARB_TYPE(APB_ARB_TYPE)
);

// Multi-mode arbiter
arbiter u_arbiter(
  .clk(PCLK),
  .rst_n(PRESETn),
  .req(APB_BYPASS ? APB_REQ : REQ),
  .arb_type(APB_ARB_TYPE),
  .gnt(GNT)
  );

endmodule

