#Tcl script which can be used with JasperGold
#Use "source lab4_pb.tcl" in the console to source this script
clear -all

#Reading the files 
#analyze -v2k topsim.v alloc_issue_ino.v constants_new.v exunit_alu.v imem.v oldest_finder.v reorderbuf.v rs_mul.v srcopr_manager.v top.v alu_ops.vh constants.vh exunit_branch.v imm_gen.v pipeline_if.v rrf_freelistmanager.v rs_reqgen.v srcsel.v uart.v alu.v decoder.v exunit_ldst.v pipeline.v rrf.v rv32_opcodes_new.v storebuf.v arf.v define.v exunit_mul.v prioenc.v rs_alu.v rv32_opcodes.vh system.v brimm_gen.v dmem.v gshare.v mpft.v ram_sync_nolatch.v rs_branch.v search_be.v tag_generator.v btb.v dualport_ram.v imem_outa.v multiplier.v ram_sync.v rs_ldst.v src_manager.v

analyze -v2k constants.vh alu_ops.vh decoder.v


analyze -sv v_decoder.sv
#Elaborating the design
elaborate -top decoder

#Set the clock
clock clk
#Set Reset
reset ~(reset)
#Prove all
prove -bg -all



