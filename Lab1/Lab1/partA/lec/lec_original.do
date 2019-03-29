// The dofile must be in 'tclmode'
tclmode

// Load the library
vpx read library -Both   -sensitive  -Statetable  -Liberty /home/ecelrc/students/skhan2/verif_labs/lab1/partA/lib/gscl45nm.lib -nooptimize

// Load the golden design: RTL
vpx read design /home/ecelrc/students/skhan2/verif_labs/lab1/partA/rtl/a25_write_back.v -Verilog -Golden   -sensitive         -continuousassignment Bidirectional   -nokeep_unreach   -nosupply

// Load the revised design: Netlist
vpx read design /home/ecelrc/students/skhan2/verif_labs/lab1/partA/gate/a25_write_back_corrected_netlist.v -Verilog -Revised -Replace  -sensitive         -continuousassignment Bidirectional   -nokeep_unreach   -nosupply

// Change the mode to LEC
vpx set system mode lec

// Add compare points and compare
vpx add compared points -all
vpx compare
