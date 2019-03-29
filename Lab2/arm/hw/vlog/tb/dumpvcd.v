//////////////////////////////////////////////////////////////////
//                                                              //
//  Waveform Dumping Control                                    //
//                                                              //
//  This file is part of the Amber project                      //
//  http://www.opencores.org/project,amber                      //
//                                                              //
//  Description                                                 //
//  Its useful in very long simulations to be able to record    //
//  a set of signals for a limited window of time, so           //
//  that the dump file does not get too large.                  //
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

`timescale  1 ns / 1 ps
`include "global_defines.v"

`define AMBER_DUMP_LENGTH 0 // If $dumpoff is commented out, this number has no meaning.

module dumpvcd();
    
// ======================================
// Dump Waves to VCD File
// ======================================
`ifdef AMBER_DUMP_VCD_N
initial
    begin
    $display ("VCD Dump enabled from %d to %d",
    ( `AMBER_DUMP_START                ),
    ( `AMBER_DUMP_START + `AMBER_DUMP_LENGTH ) );
    $dumpfile("/home/unga/jypark/supreme/jypark/netlist.vcd"); // vcd file location
    $dumpvars(0,tb.u_system.u_amber);
    $dumpon;
    $dumpoff;
    #`AMBER_DUMP_START;
    $dumpon;
    #`AMBER_DUMP_LENGTH; 
    //$dumpoff; // if this one is commented out, this means dumping all simulation periods
    end
`endif

`ifdef AMBER_DUMP_VCD_R
initial
    begin
    $display ("VCD Dump enabled from %d to %d",
    ( `AMBER_DUMP_START                ),
    ( `AMBER_DUMP_START + `AMBER_DUMP_LENGTH ) );
    $dumpfile("rtl.vcd");
    $dumpvars(0,tb);
    $dumpon;
    $dumpoff;
    #`AMBER_DUMP_START;
    $dumpon;
    #`AMBER_DUMP_LENGTH; 
    //$dumpoff; // if this one is commented out, this means dumping all simulation periods
    end
`endif

endmodule
