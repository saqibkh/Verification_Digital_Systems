//EE382M-Verification of Digital Systems
//Lab 4 - Formal Property Verification
//
//
//Module - apb_slave
//APB interface slave module

module apb_slave ( 
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
  APB_ARB_TYPE
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

`include "apb_parameters.v"

// Internal variables
reg [1:0] current_state;
reg [1:0] next_state;

reg [7:0] r_prdata;
reg [7:0] r_bypass;
reg [7:0] r_req;
reg [7:0] r_arb_type;

// Assignments
assign PRDATA       = r_prdata;
assign APB_BYPASS   = r_bypass[0]; // Saqib changed this from ~r_bypass[0] to r_bypass[0]
assign APB_REQ      = r_req[3:0];
assign APB_ARB_TYPE = r_arb_type[2:0];

// APB protocol fsm with no wait states
always @(negedge PRESETn or posedge PCLK) begin
  if (PRESETn == 0)
    begin
      current_state <= IDLE;
    end
  else 
    begin
      current_state <= next_state;
    end
end

always @(*) begin
  case (current_state)
    IDLE : begin
      if(PSEL & ~PENABLE)
        next_state = SETUP;
      else
        next_state = IDLE;
    end
    SETUP : begin
      if(PSEL & PENABLE)
        next_state = ACCESS;
    end
    ACCESS : begin
      if(PSEL & ~PENABLE)
        next_state = SETUP;
      else
        next_state = IDLE;
    end
    default: begin
      next_state = current_state;
    end
  endcase
end

assign PREADY = (current_state == SETUP) && (next_state == ACCESS);

// Read operation
always @(*) begin
  if(PREADY & ~PWRITE)
    begin
      if(PADDR == ADDR_BYPASS_REG)
        r_prdata = r_bypass;
      else if(PADDR == ADDR_REQ_REG)
        r_prdata = r_req;
      else if(PADDR == ADDR_ARB_TYPE_REG)
        r_prdata = r_arb_type;
      else
        r_prdata = 8'd0;
    end
  else
    begin
      r_prdata = 8'd0;
    end
end

// Write operation
always @(posedge PCLK or negedge PRESETn) begin
  if(PRESETn == 0)
    begin
      r_bypass  <= RST_VAL_BYPASS_REG;
      r_req     <= RST_VAL_REQ_REG;
      r_arb_type <= RST_VAL_ARB_TYPE_REG;
    end
  else
    begin
      if(PREADY & PWRITE)
        begin
          if(PADDR == ADDR_BYPASS_REG)
            r_bypass <= PWDATA;
          else if(PADDR == ADDR_REQ_REG)
            r_req <= PWDATA;
          else if(PADDR == ADDR_ARB_TYPE_REG)
            r_arb_type <= PWDATA;
        end
    end
end

endmodule

