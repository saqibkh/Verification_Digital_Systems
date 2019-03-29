module module4SVA (
  input t_clk, t_i_wb_ack, t_extra_write_r,
  input [2:0] t_wishbone_st
);

import FSMProperties::*;

// states recreated
localparam [3:0] WB_IDLE            = 3'd0,
                 WB_BURST1          = 3'd1,
                 WB_BURST2          = 3'd2,
                 WB_BURST3          = 3'd3,
                 WB_WAIT_ACK        = 3'd4;


/*place your properties here*/
assert property (FSMValidTransition(t_clk, (t_wishbone_st == WB_IDLE), 1, (t_wishbone_st == WB_IDLE) | (t_wishbone_st == WB_BURST1) | (t_wishbone_st == WB_WAIT_ACK)));

assert property (FSMValidTransition(t_clk, (t_wishbone_st == WB_BURST1), t_i_wb_ack, t_wishbone_st == WB_BURST2));

assert property (FSMValidTransition(t_clk, (t_wishbone_st == WB_BURST2), t_i_wb_ack, t_wishbone_st == WB_BURST3));

assert property (FSMValidTransition(t_clk, (t_wishbone_st == WB_BURST3), t_i_wb_ack, t_wishbone_st == WB_WAIT_ACK));

assert property (FSMValidTransition(t_clk, (t_wishbone_st == WB_WAIT_ACK), (t_extra_write_r || !t_i_wb_ack), t_wishbone_st == WB_WAIT_ACK));

assert property (FSMValidTransition(t_clk, (t_wishbone_st == WB_WAIT_ACK), (!t_extra_write_r && t_i_wb_ack), t_wishbone_st == WB_IDLE));

assert property (disable iff (t_wishbone_st == WB_IDLE) FSMTimeOut(t_clk, t_wishbone_st, 1000));

endmodule

module Wrapper ;

bind a25_wishbone module4SVA wrp2 (
  .t_clk(i_clk),
  .t_i_wb_ack(i_wb_ack),
  .t_extra_write_r(extra_write_r),
  .t_wishbone_st(wishbone_st)
);

endmodule
