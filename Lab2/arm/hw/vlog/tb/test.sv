// Write you SystemVerilog Assertions here !

// This file is wriiten by Saqib Khan (UT EID: sak2454)
// Date: 02-16-2019


// Main test module
module test (
  input [31:0] t_o_wb_adr, t_i_wb_dat, t_o_wb_dat, // Wishbone interface signals
  input t_o_wb_we, t_o_wb_stb, t_o_wb_cyc, t_i_wb_ack, // Wishbone interface signals
  input t_i_reset,
  input t_i_wb_clock
);

// a) Check if wishbone strobe o_wb_stb is always a known value (1 or 0)
  sequence known_o_wb_stb;
    @(posedge t_i_wb_clock) ((t_o_wb_stb == 1'b0) | (t_o_wb_stb == 1'b1));
  endsequence

  assert property (known_o_wb_stb);

// b) Check if wishbone cycle o_wb_cyc is always a known value
  sequence known_o_wb_cyc;
    @(posedge t_i_wb_clock) ((t_o_wb_cyc == 1'b0) | (t_o_wb_cyc == 1'b1));
  endsequence

  assert property (known_o_wb_cyc);

// c) Write a parametrized sequence for validating
  sequence known_value(value);
    @(posedge t_i_wb_clock) ((value == 1'b0) | (value == 1'b1));
  endsequence

  assert property (known_value(t_o_wb_stb));
  assert property (known_value(t_o_wb_cyc));

// d) Identify the conditions for which the signals o_wb_adr, o_wb_dat,
//    and i_wb_dat must be valid.

// o_wb_adr is TRUE when (o_wb_cyc & o_wb_stb) is TRUE
// o_wb_dat is TRUE when (o_wb_cyc & o_wb_stb & o_wb_we) is TRUE
// i_wb_dat is TRUE when (o_wb_cyc & o_wb_stb & ~o_wb_we & i_wb_ack) is TRUE


// e) Write a parametrized property to check if a condition holds, 
//    then a bus has a valid value at the same time.

  property Validate_Current_Clock_Cycle(reset, DataTr, hold_condition);
    @(posedge t_i_wb_clock) disable iff (!(reset)) $rose(hold_condition) |-> not $isunknown(DataTr) throughout hold_condition;
  endproperty

  property Validate_Next_Clock_Cycle(reset, DataTr, hold_condition);
    @(posedge t_i_wb_clock) disable iff (!reset) $rose(hold_condition) |-> ##1 !$isunknown(DataTr) throughout hold_condition;
  endproperty

// f) Use your parametrized property to check that data and address
//    bits are valid during read and write cycles. You should write
//    three properties for o wb dat, i wb dat, and o wb adr.

  assert property (Validate_Current_Clock_Cycle(t_i_reset, t_o_wb_adr, t_o_wb_cyc & t_o_wb_stb));
  assert property (Validate_Current_Clock_Cycle(t_i_reset, t_o_wb_dat, t_o_wb_cyc & t_o_wb_stb & t_o_wb_we));
  assert property (Validate_Next_Clock_Cycle(t_i_reset, t_i_wb_dat, t_o_wb_cyc & t_o_wb_stb & ~t_o_wb_we & t_i_wb_ack));

// g) With reference to the timing diagrams, write two properties that
//    describe the request-acknowledge sequence for the write and read
//    cycles.

// Every read/write request should be acknowledged during the read/write window
  assert property ( @(posedge t_i_wb_clock) disable iff(!t_i_reset) not ( (t_i_wb_ack == 0) throughout ($rose(t_o_wb_stb & t_o_wb_cyc & t_o_wb_we) ##[1:$] $fell(t_o_wb_stb & t_o_wb_cyc & t_o_wb_we))));
  assert property ( @(posedge t_i_wb_clock) disable iff(!t_i_reset) not ( (t_i_wb_ack == 0) throughout ($rose(t_o_wb_stb & t_o_wb_cyc & !t_o_wb_we) ##[1:$] $fell(t_o_wb_stb & t_o_wb_cyc & !t_o_wb_we))));
// Once the read/write request window has been terminated, the acknowledgement signal(i_wb_ack) should be turned off.
  assert property ( @(posedge t_i_wb_clock) disable iff(!t_i_reset) $fell(t_o_wb_stb) && $fell(t_o_wb_cyc) |-> not t_i_wb_ack);

// 2h) Can you write assertions describing what happens to o_wb_stb
// and o_wb_cyc on the interface when reset is asserted? Hint:
// o_wb_stb and o_wb_cyc should be reset to zero when reset is as-
// serted as in the wishbone standard.
  assert property ( @(posedge t_i_wb_clock) !t_i_reset |-> (!t_o_wb_stb & !t_o_wb_cyc));

endmodule

module test_Wrapper;

  bind a25_wishbone test wrp(
    .t_o_wb_adr(o_wb_adr), 
    .t_i_wb_dat(i_wb_dat),
    .t_o_wb_dat(o_wb_dat),
    .t_o_wb_we(o_wb_we),
    .t_o_wb_stb(o_wb_stb),
    .t_o_wb_cyc(o_wb_cyc),
    .t_i_wb_ack(i_wb_ack),
    .t_i_reset(quick_n_reset),
    .t_i_wb_clock(i_clk)
  );

endmodule
