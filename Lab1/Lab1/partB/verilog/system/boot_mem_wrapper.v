module boot_mem_wrapper 
(
input                       i_wb_clk,     // WISHBONE clock

input       [31:0]          i_wb_adr,
input       [3:0]           i_wb_sel,
input                       i_wb_we,
output      [31:0]          o_wb_dat,
input       [31:0]          i_wb_dat,
input                       i_wb_cyc,
input                       i_wb_stb,
output                      o_wb_ack,
output                      o_wb_err

);




boot_mem u_boot_mem (
    .i_wb_clk               ( i_wb_clk    ),
    .i_wb_adr               ( i_wb_adr    ),
    .i_wb_sel               ( i_wb_sel    ),
    .i_wb_we                ( i_wb_we     ),
    .o_wb_dat               ( o_wb_dat    ),
    .i_wb_dat               ( i_wb_dat    ),
    .i_wb_cyc               ( i_wb_cyc    ),
    .i_wb_stb               ( i_wb_stb    ),
    .o_wb_ack               ( o_wb_ack    ),
    .o_wb_err               ( o_wb_err    )
);

endmodule
