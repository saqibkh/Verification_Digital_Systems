//EE382M-Verification of Digital Systems
//Lab 4 - Formal Property Verification
//
//
//Modules - apb_props and Wrapper
//SystemVerilog Properties for the module - arbiter_top

module apb_props(
// APB interface
input        PCLK,
input        PRESETn,
input        PWRITE,
input        PSEL,
input        PENABLE,
input  [7:0] PADDR,
input  [7:0] PWDATA,

input  [7:0] PRDATA,
input        PREADY,
// APB registers
input        APB_BYPASS,
input  [3:0] APB_REQ,
input  [2:0] APB_ARB_TYPE,
// Arbiter ports
input  [3:0] REQ,
input  [3:0] GNT
);

//Write APB interface properties here - assertions, cover properties and assume properties

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// APB Assumptions:

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// 1) APB read/write are single transfers and are padded with IDLE phase, that is,
//    once initiated they are always completed with the following sequence only:
//    IDLE (PSEL =0 & PENABLE =0)
//    => PHASE1 (PSEL=1 & PENABLE =0)
//    => PHASE2 (PSEL=1 & PENABLE =1)
//    => IDLE (PSEL =0 & PENABLE =0)
sequence APB_PHASE1;
  PSEL && !PENABLE;
endsequence

sequence APB_PHASE2;
  PSEL && PENABLE;
endsequence

sequence APB_IDLE;
  !PSEL;
endsequence

// Complete Bus Cycle IDLE->PHASE1->PHASE2->IDLE
sequence APB_BUS_CYCLE;
  APB_IDLE ##1 APB_PHASE1 ##1 APB_PHASE2 ##1 APB_IDLE;
endsequence

// Once we enter the bus cycle through IDLE, it must complete APB_BUS_CYCLE
property APB_BUS_CYCLE_COMPLETE;
  @(posedge PCLK) (APB_IDLE |-> APB_BUS_CYCLE);
endproperty

assume_APB_BUS_CYCLE_COMPLETE : assume property(APB_BUS_CYCLE_COMPLETE);
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// 2) PADDR, PWDATA and PWRITE are stable and defined during the transfers.

// Check that PADDR and PWRITE are stable during the cycle
property APB_ADDR_WRITE_STABLE;
  @(posedge PCLK) (PSEL |-> $stable({PWRITE, PADDR}));
endproperty

// Check that PWDATA is stable during the cycle
property APB_WRITE_DATA_STABLE;
  @(posedge PCLK) ((PSEL && PWRITE) |-> $stable(PWDATA));
endproperty

// If PENABLE==TRUE, it must be in the second clock of a cycle, and then it must be turned off
property APB_NO_PENABLE_OUTSIDE_CYCLE_2;
  @(posedge PCLK) (PENABLE |-> $stable(PSEL) ##1 (!PENABLE));
endproperty

assume_APB_WRITE_DATA_STABLE : assume property(APB_WRITE_DATA_STABLE);
assume_APB_ADDR_WRITE_STABLE : assume property(APB_ADDR_WRITE_STABLE);
assume_APB_NO_PENABLE_OUTSIDE_CYCLE_2 : assume property(APB_NO_PENABLE_OUTSIDE_CYCLE_2);
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// 3) PADDR must take only the legal address values given in the APB register
//    description.
// PWRITE and PADDR must be valid throughout the cycle
property APB_WRITE_ADDR_VALID;
  @(posedge PCLK) (PSEL |-> ((^{PWRITE, PADDR}) !== 1'bx));
endproperty
assume_APB_WRITE_ADDR_VALID : assume property(APB_WRITE_ADDR_VALID);
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// 4) For a given PADDR, PWDATA can only take legal write values as given in the
//    APB register description. For instance, if PADDR = 8'h10, PWDATA can only
//    be 8'h00 or 8'h01.
// PADDR can only take on following values:
// ADDR_BYPASS_REG == 8'h10 or 
// ADDR_REQ_REG = 8'h14 or
// ADDR_ARB_TYPE_REG = 8'h1C;
property APB_PADDR_RESTRICTED;
  @(posedge PCLK) PSEL |-> (PADDR == 8'h10) || (PADDR == 8'h14) || (PADDR == 8'h1C);
endproperty

// PWDATA can be 8'h00 or 8'h01 when PADDR = ADDR_BYPASS_REG == 8'h10
property APB_PWDATA_BYPASS_RESTRICTED;
  @(posedge PCLK) PSEL && PWRITE && (PADDR == 8'h10) |-> (PWDATA == 8'h00) || (PWDATA == 8'h01);
endproperty

// PWDATA must be < 8'd16 when PADDR = ADDR_REQ_REG == 8'h14
property APB_PWDATA_REQ_RESTRICTED;
  @(posedge PCLK) PSEL && PWRITE && (PADDR == 8'h14) |-> (PWDATA <= 8'd15) && (PWDATA >= 8'd0);
endproperty

// PWDATA must be < 8'd6 when PADDR = ADDR_ARB_TYPE_REG == 8'h1C
property APB_PWDATA_ARB_TYPE_RESTRICTED;
  @(posedge PCLK) PSEL && PWRITE && (PADDR == 8'h1C) |-> (PWDATA <= 8'd05) && (PWDATA >= 8'd0);
endproperty

assume_APB_PADDR_RESTRICTED : assume property(APB_PADDR_RESTRICTED);
assume_APB_PWDATA_BYPASS_RESTRICTED : assume property(APB_PWDATA_BYPASS_RESTRICTED);
assume_APB_PWDATA_REQ_RESTRICTED : assume property(APB_PWDATA_REQ_RESTRICTED);
assume_APB_PWDATA_ARB_TYPE_RESTRICTED : assume property(APB_PWDATA_ARB_TYPE_RESTRICTED);
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// APB assertions

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// 1) Check if APB write operation is correct for all registers
// ARB_BYPASS register output can be 0 or 1 at any time
property APB_BYPASS_REG_VALID;
  @(posedge PCLK) (APB_BYPASS == 8'd0) || (APB_BYPASS == 8'd1);
endproperty

// APB_REQ register output must be < 8'd16 at any time
property APB_REQ_REG_VALID;
  @(posedge PCLK) (APB_REQ <= 8'd15) && (APB_REQ >= 8'd0);
endproperty

// ARB_TYPE register output must be < 8'd6 at any time
property APB_ARB_TYPE_REG_VALID;
  @(posedge PCLK) (APB_ARB_TYPE <= 8'd05) && (APB_ARB_TYPE >= 8'd0);
endproperty

assert_APB_BYPASS_REG_VALID : assert property(APB_BYPASS_REG_VALID);
assert_APB_REQ_REG_VALID : assert property(APB_REQ_REG_VALID);
assert_APB_ARB_TYPE_REG_VALID : assert property(APB_ARB_TYPE_REG_VALID);

// Check the APB write
reg [7:0] pwdata_del;
always @(posedge PCLK) begin
  pwdata_del <= PWDATA;
end

assert_APB_BYPASS_WR_check : assert property(@(posedge PCLK) (PREADY && PWRITE && (PADDR == 8'h10)) |=> (APB_BYPASS == pwdata_del[0]));
assert_APB_REQ_WR_check : assert property(@(posedge PCLK) (PREADY && PWRITE && (PADDR == 8'h14)) |=> (APB_REQ == pwdata_del[3:0]));
assert_APB_ARB_TYPE_WR_check : assert property(@(posedge PCLK) (PREADY && PWRITE && (PADDR == 8'h1C)) |=> (APB_ARB_TYPE == pwdata_del[2:0]));
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// 2) Check if APB read operation is correct for all registers
assert_APB_BYPASS_RD_check : assert property(@(posedge PCLK) (PREADY && ~PWRITE && (PADDR == 8'h10)) |-> ($past(APB_BYPASS) == PRDATA));
assert_APB_REQ_RD_check : assert property(@(posedge PCLK) (PREADY && ~PWRITE && (PADDR == 8'h14)) |-> ($past(APB_REQ) == PRDATA));
assert_APB_ARB_TYPE_RD_check : assert property(@(posedge PCLK) (PREADY && ~PWRITE && (PADDR == 8'h1C)) |-> ($past(APB_ARB_TYPE) == PRDATA));
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// 3) Check if reset values of the registers are correct
assert_BYPASS_reset_check: assert property (@(posedge PCLK) $rose(PRESETn) |-> (APB_BYPASS == 8'd0) );
assert_REQ_reset_check: assert property (@(posedge PCLK) $rose(PRESETn) |-> (APB_REQ == 8'd0));
assert_ARB_TYPE_reset_check: assert property (@(posedge PCLK) $rose(PRESETn) |-> (APB_ARB_TYPE == 8'd4));
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// APB Coverage:
// 1) APB read operation happens at least once
// 2) APB write operation happens at least once
cover_APB_BYPASS: cover property(@(posedge PCLK) $rose(APB_BYPASS));
cover_APB_WRITE: cover property(@(posedge PCLK) $rose(PREADY & PWRITE));
cover_APB_READ: cover property(@(posedge PCLK) $rose(PREADY & ~PWRITE));

/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////

endmodule

module arb_props (
  clk,
  rst_n,
  req,
  arb_type,
  gnt
  );

input        clk;
input        rst_n;
input  [3:0] req;
input  [2:0] arb_type;

input  [3:0] gnt;

//Write arbiter properties here - assertions, cover properties and assume properties

// Assume:
// 1. Input requests on any port should be held high until they are granted. The
//    arbiter does not keep a history of requests. For correct operation, a port should
//    make a request and then keep it high till it has been granted.

// Assert:
// 1. All grants are mutually exclusive and grant is not issued unless request is asserted. These are safety properties to ensure that no two grants are given in the same cycle.
// 2. Check for priority order for scheme P0, P1, P2 and P3.
// 3. For priority schemes Prr and Prand, check for liveness properties to ensure that no port is starved for a grant. That is, for either of these arbitration schemes, 
//    every request should be granted within certain number of cycles `N'. Figure out the value of `N' and write the assertions to check for liveness.

// Cover:
// 1. Write a cover property on each request to go high at least once.
// 2. Write a cover property on each grant to go high at least once.

a_gnt_onehot : assert property (@(posedge clk) disable iff (~rst_n) $onehot0(gnt));

// Priority scheme when APB_ARB_TYPE = 3'b000
assert_priority_0_gnt0 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[0] && $past(arb_type == 3'd0)) |-> $past(req[0]));
assert_priority_0_gnt1 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[1] && $past(arb_type == 3'd0)) |-> $past(req[1] & ~req[0]));
assert_priority_0_gnt2 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[2] && $past(arb_type == 3'd0)) |-> $past(req[2] & ~req[1] & ~req[0]));
assert_priority_0_gnt3 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[3] && $past(arb_type == 3'd0)) |-> $past(req[3] & ~req[2] & ~req[1] & ~req[0]));

// Priority scheme when APB_ARB_TYPE = 3'b001
assert_priority_1_gnt0 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[0] && $past(arb_type == 3'd1)) |-> $past(req[0] & ~req[1]));
assert_priority_1_gnt1 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[1] && $past(arb_type == 3'd1)) |-> $past(req[1]));
assert_priority_1_gnt2 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[2] && $past(arb_type == 3'd1)) |-> $past(req[2] & ~req[1] & ~req[0]));
assert_priority_1_gnt3 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[3] && $past(arb_type == 3'd1)) |-> $past(req[3] & ~req[2] & ~req[1] & ~req[0]));
// Priority scheme when APB_ARB_TYPE = 3'b010
assert_priority_2_gnt0 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[0] && $past(arb_type == 3'd2)) |-> $past(req[0] & ~req[2]));
assert_priority_2_gnt1 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[1] && $past(arb_type == 3'd2)) |-> $past(req[1] & ~req[2] & ~req[0]));
assert_priority_2_gnt2 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[2] && $past(arb_type == 3'd2)) |-> $past(req[2]));
assert_priority_2_gnt3 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[3] && $past(arb_type == 3'd2)) |-> $past(req[3] & ~req[2] & ~req[1] & ~req[0]));
// Priority scheme when APB_ARB_TYPE = 3'b010
assert_priority_3_gnt0 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[0] && $past(arb_type == 3'd3)) |-> $past(req[0] & ~req[3]));
assert_priority_3_gnt1 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[1] && $past(arb_type == 3'd3)) |-> $past(req[1] & ~req[3] & ~req[0]));
assert_priority_3_gnt2 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[2] && $past(arb_type == 3'd3)) |-> $past(req[2] & ~req[3] & ~req[0] & ~req[1]));
assert_priority_3_gnt3 : assert property (@(posedge clk) disable iff (~rst_n) (gnt[3] && $past(arb_type == 3'd3)) |-> $past(req[3]));


generate for (genvar i=0; i<=3; i++)
  begin: gen
    assert_gnt_within5_req_rr_ : assert property( @(posedge clk) disable iff(arb_type != 3'b100) $rose(req[i]) |-> ##[1:4] $rose(gnt[i]));
    assert_gnt_within5_req_rand_ : assert property( @(posedge clk) disable iff(arb_type != 3'b101) $rose(req[i]) |-> ##[1:7] $rose(gnt[i]));

  property p_req_until_gnt;
    @(posedge clk) req[i] |-> req[i][*1:$] ##0 gnt[i];
  endproperty : p_req_until_gnt

  assume_req_until_gnt: assume property (p_req_until_gnt);
  property p_no_req_no_gnt;
    @(posedge clk) $past(req[i]==1'b0) |-> (gnt[i]==1'b0);
  endproperty : p_no_req_no_gnt
  assert_no_req_no_gnt: assert property (p_no_req_no_gnt);

  cover_req: cover property(@(posedge clk) disable iff (~rst_n) $rose(req[i]));
  cover_gnt: cover property(@(posedge clk) disable iff (~rst_n) $rose(gnt[i]));
  end
endgenerate

endmodule

module Wrapper;

//Bind the 'apb_props' module with the 'arbiter_top' module to instantiate the properties
bind arbiter_top apb_props u_apb_props(
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
  .APB_ARB_TYPE(APB_ARB_TYPE),
  .REQ(REQ),
  .GNT(GNT)
);

//Bind the 'arb_props' module with the 'arbiter' module to instantiate the properties
bind arbiter arb_props u_arb_props(
  .clk(clk),
  .rst_n(rst_n),
  .req(req),
  .arb_type(arb_type),
  .gnt(gnt)
);

endmodule

