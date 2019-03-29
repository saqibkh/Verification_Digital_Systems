// STEP 0: (completed) The dofile must be in 'tclmode'
tclmode

// STEP 1: Set the log file. This is helpful to debug the setup.
set_log_file lec_cg_scan.log -replace 

// STEP 2: Set the undefined cells as black boxes for both golden and revised designs.
set_undefined_cell black_box -noascend -both 

// STEP 3: Load the libraries
read_library -Both -Replace -sensitive -Statetable -Liberty \
    /usr/local/packages/synopsys_2015/SAED32_EDK/lib/stdcell_hvt/db_nldm/saed32hvt_ss0p95vn40c.lib \
    /usr/local/packages/synopsys_2015/SAED32_EDK/lib/stdcell_rvt/db_nldm/saed32rvt_ss0p95vn40c.lib \
    /usr/local/packages/synopsys_2015/SAED32_EDK/lib/stdcell_lvt/db_nldm/saed32lvt_ss0p95vn40c.lib

// STEP 4: Load the golden design.
// Before loading, add the search path to include all the sub-folders in '../../verilog',
// so that, the files called-in an RTL file with `inlcude directive can be located.
set WDIR [pwd]
set TOP ${WDIR}/.. 

set verilog_path [string trim $WDIR "scripts/lec"]
append verilog_path "/verilog"
set rtl_search_path [list /${verilog_path} /${verilog_path}/system /${verilog_path}/tb /${verilog_path}/lib /${verilog_path}/ethmac /${verilog_path}/amber25]

add_search_path $rtl_search_path -design -golden


source ${TOP}/common/rtl.list
set my_verilog_files $RTL_LIST 

read_design $my_verilog_files -Verilog -Golden -sensitive -root system -continuousassignment Bidirectional -nokeep_unreach -nosupply


// STEP 5: Load the revised design: The netlist '../rc/system_cg_scan_netlist.v'
read_design ../rc/system_cg_scan_netlist.v -Verilog -Revised -sensitive -root system -continuousassignment Bidirectional -nokeep_unreach -nosupply

// STEP 6: Add the pin constraints
add_pin_constraint 0 scan_cg_en -Revised
add_pin_constraint 0 scan_en -Revised
add_pin_constraint 0 scan_mode -both

// STEP 7: (completed) Setting the options for analysis
set_flatten_model -seq_constant -seq_constant_x_to 0
set_flatten_model -gated_clock
set_analyze_option -auto

// STEP 8: Set the system mode to lec
vpx set system mode lec

// STEP 9: The unmapped memory macros in golden and revised designs must be mapped.
// Use the add_mapped_points command to map the RAMs.
add_mapped_points u_boot_mem_wrapper/u_boot_mem/myram1 u_boot_mem_wrapper_u_boot_mem/myram1 -noinvert
add_mapped_points u_boot_mem_wrapper/u_boot_mem/myram2 u_boot_mem_wrapper_u_boot_mem/myram2 -noinvert
add_mapped_points u_boot_mem_wrapper/u_boot_mem/myram3 u_boot_mem_wrapper_u_boot_mem/myram3 -noinvert
add_mapped_points u_boot_mem_wrapper/u_boot_mem/myram4 u_boot_mem_wrapper_u_boot_mem/myram4 -noinvert
add_mapped_points u_boot_mem_wrapper/u_boot_mem/myram5 u_boot_mem_wrapper_u_boot_mem/myram5 -noinvert
add_mapped_points u_boot_mem_wrapper/u_boot_mem/myram6 u_boot_mem_wrapper_u_boot_mem/myram6 -noinvert
add_mapped_points u_boot_mem_wrapper/u_boot_mem/myram7 u_boot_mem_wrapper_u_boot_mem/myram7 -noinvert 


// STEP 10: Add the compared points and compare
vpx add compared points -all
vpx compare

// If the script is correctly written, the code below will display 
// zero diff, abort and unknown points.
puts "Num of compare points = [get_compare_points -count]"
puts "Num of diff points    = [get_compare_points -NONequivalent -count]"
puts "Num of abort points   = [get_compare_points -abort -count]"
puts "Num of unknown points = [get_compare_points -unknown -count]"

