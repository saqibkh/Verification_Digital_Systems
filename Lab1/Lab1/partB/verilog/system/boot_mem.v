//////////////////////////////////////////////////////////////////
//                                                              //
//  8KBytes SRAM configured with boot software                  //
//                                                              //
//  This file is part of the Amber project                      //
//  http://www.opencores.org/project,amber                      //
//                                                              //
//  Description                                                 //
//  Holds just enough software to get the system going.         //
//  The boot loader fits into this 8KB embedded SRAM on the     //
//  FPGA and enables it to load large applications via the      //
//  serial port (UART) into the DDR3 memory                     //
//                                                              //
//  Author(s):                                                  //
//      - Conor Santifort, csantifort.amber@gmail.com           //
//                                                              //
//////////////////////////////////////////////////////////////////
//                                                              //
// Copyright (C) 2010 Authors and OPENCORES.ORG                 //
//                                                              //
// This source file may be used and distributed without         //
// restriction provided that this copyright statement is not    //
// removed from the file and that any derivative work contains  //
// the original copyright notice and the associated disclaimer. //
//                                                              //
// This source file is free software; you can redistribute it   //
// and/or modify it under the terms of the GNU Lesser General   //
// Public License as published by the Free Software Foundation; //
// either version 2.1 of the License, or (at your option) any   //
// later version.                                               //
//                                                              //
// This source is distributed in the hope that it will be       //
// useful, but WITHOUT ANY WARRANTY; without even the implied   //
// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      //
// PURPOSE.  See the GNU Lesser General Public License for more //
// details.                                                     //
//                                                              //
// You should have received a copy of the GNU Lesser General    //
// Public License along with this source; if not, download it   //
// from http://www.opencores.org/lgpl.shtml                     //
//                                                              //
//////////////////////////////////////////////////////////////////


module boot_mem 
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

wire start_write, start_read;
reg  start_read_d1 = 'd0;
reg [31:0] o_wb_dat_r;
// Can't start a write while a read is completing. The ack for the read cycle
// needs to be sent first
assign start_write = i_wb_stb &&  i_wb_we && !start_read_d1;
assign start_read  = i_wb_stb && !i_wb_we && !start_read_d1;


always @( posedge i_wb_clk )
    start_read_d1 <= start_read;

assign o_wb_ack = i_wb_stb && ( start_write || start_read_d1 );
assign o_wb_err = 1'd0;
assign o_wb_dat = o_wb_dat_r ;
// ------------------------------------------------------
// Instantiate SRAMs
// ------------------------------------------------------
//         
`ifdef XILINX_FPGA

    `ifdef XILINX_SPARTAN6_FPGA
        xs6_sram_2048x32_byte_en
    `endif 
    `ifdef XILINX_VIRTEX6_FPGA
        xv6_sram_2048x32_byte_en
    `endif 

#(
// This file holds a software image used for FPGA simulations
// This pre-processor syntax works with both the simulator
// and ISE, which I couldn't get to work with giving it the
// file name as a define.

`ifdef BOOT_MEM_PARAMS_FILE
    `include `BOOT_MEM_PARAMS_FILE
`else
    // default file
    `include "boot-loader_memparams.v"
`endif

)
`endif 

`ifndef XILINX_FPGA


wire add11,add10,add9;

assign add11=i_wb_adr[12];
assign add10=i_wb_adr[11];
assign add9=i_wb_adr[10];

wire [7:0] ram_select; 
reg cs0,cs1,cs2,cs3,cs4,cs5,cs6,cs7;
wire [31:0] o_wb_dat_arr [7:0] ; 
always @ (*) begin
 cs0 <= add9&add10&add11;
 cs1 <= add9&add10&!add11;
 cs2 <= add9&!add10&add11;
 cs3 <= add9&!add10&!add11;
 cs4 <= !add9&add10&add11;
 cs5 <= !add9&add10&!add11;
 cs6 <= !add9&!add10&add11;
 cs7 <= !add9&!add10&!add11;
end
 
assign ram_select = {cs0,cs1,cs2,cs3,cs4,cs5,cs6,cs0};
always @ (*) begin
 case(ram_select) 
        1000_0000:o_wb_dat_r =  o_wb_dat_arr[0];
        0100_0000:o_wb_dat_r =  o_wb_dat_arr[1];
        0010_0000:o_wb_dat_r =  o_wb_dat_arr[2];
        0001_0000:o_wb_dat_r =  o_wb_dat_arr[3];
        
        0000_1000:o_wb_dat_r =  o_wb_dat_arr[4];
        0000_0100:o_wb_dat_r =  o_wb_dat_arr[5];
        0000_0010:o_wb_dat_r =  o_wb_dat_arr[6];
        0000_0001:o_wb_dat_r =  o_wb_dat_arr[7];
        default:  o_wb_dat_r =  o_wb_dat_arr[0];
 endcase
end



SRAM1RW256x32 myram0(.A(i_wb_adr[9:2]),.CE(cs0),.WEB(start_write),.OEB(1'b1),.CSB(i_wb_clk),.I(i_wb_dat),.O(o_wb_dat_arr[0]));
SRAM1RW256x32 myram1(.A(i_wb_adr[9:2]),.CE(cs1),.WEB(start_write),.OEB(1'b1),.CSB(i_wb_clk),.I(i_wb_dat),.O(o_wb_dat_arr[1]));
SRAM1RW256x32 myram2(.A(i_wb_adr[9:2]),.CE(cs2),.WEB(start_write),.OEB(1'b1),.CSB(i_wb_clk),.I(i_wb_dat),.O(o_wb_dat_arr[2]));
SRAM1RW256x32 myram3(.A(i_wb_adr[9:2]),.CE(cs3),.WEB(start_write),.OEB(1'b1),.CSB(i_wb_clk),.I(i_wb_dat),.O(o_wb_dat_arr[3]));
SRAM1RW256x32 myram4(.A(i_wb_adr[9:2]),.CE(cs4),.WEB(start_write),.OEB(1'b1),.CSB(i_wb_clk),.I(i_wb_dat),.O(o_wb_dat_arr[4]));
SRAM1RW256x32 myram5(.A(i_wb_adr[9:2]),.CE(cs5),.WEB(start_write),.OEB(1'b1),.CSB(i_wb_clk),.I(i_wb_dat),.O(o_wb_dat_arr[5]));
SRAM1RW256x32 myram6(.A(i_wb_adr[9:2]),.CE(cs6),.WEB(start_write),.OEB(1'b1),.CSB(i_wb_clk),.I(i_wb_dat),.O(o_wb_dat_arr[6]));
SRAM1RW256x32 myram7(.A(i_wb_adr[9:2]),.CE(cs7),.WEB(start_write),.OEB(1'b1),.CSB(i_wb_clk),.I(i_wb_dat),.O(o_wb_dat_arr[7]));
//
//
//generic_sram_byte_en
//#(
//    .DATA_WIDTH    ( 32   ) ,
//    .ADDRESS_WIDTH ( 11   )
//)
`endif 
//u_mem (
//    .i_clk          ( i_wb_clk             ),
//    .i_write_enable ( start_write          ),
//    .i_byte_enable  ( i_wb_sel             ),
//    .i_address      ( i_wb_adr[12:2]       ),  // 2048 words, 32 bits
//    .o_read_data    ( o_wb_dat             ),
//    .i_write_data   ( i_wb_dat             )
//);
//
//
// =======================================================================================
// =======================================================================================
// =======================================================================================
// Non-synthesizable debug code
// =======================================================================================


//synopsys translate_off
`ifdef XILINX_SPARTAN6_FPGA
    `ifdef BOOT_MEM_PARAMS_FILE
        initial
            $display("Boot mem file is %s", `BOOT_MEM_PARAMS_FILE );
    `endif
`endif
//synopsys translate_on
    
endmodule



