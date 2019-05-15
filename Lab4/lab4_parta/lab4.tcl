#Tcl script which can be used with JasperGold

clear -all

#Use "source lab4.tcl" in the console to source this script

#Reading the files (.v and .sv) 
analyze -v2k arbiter_top.v arbiter.v PNSeqGen.v apb_slave.v apb_parameters.v
analyze -sv bind_wrapper.sv
#Elaborating the design, specify the top module
elaborate -top arbiter_top
#You may  need to add commands below

#Set the clock
clock PCLK
#Set Reset
reset ~(PRESETn)
#Prove all
prove -bg -all
