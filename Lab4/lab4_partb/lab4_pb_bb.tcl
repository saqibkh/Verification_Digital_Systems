## Retaining the environment same as after lab4_pb.tcl add the command for the black boxing step
clear -all

analyze -v2k alloc_issue_ino.v constants_new.v exunit_alu.v imem.v oldest_finder.v reorderbuf.v rs_mul.v srcopr_manager.v top.v alu_ops.vh constants.vh exunit_branch.v imm_gen.v pipeline_if.v rrf_freelistmanager.v rs_reqgen.v srcsel.v uart.v alu.v decoder.v exunit_ldst.v pipeline.v rrf.v rv32_opcodes_new.v storebuf.v arf.v define.v exunit_mul.v prioenc.v rs_alu.v rv32_opcodes.vh system.v brimm_gen.v dmem.v gshare.v mpft.v ram_sync_nolatch.v rs_branch.v search_be.v tag_generator.v btb.v dualport_ram.v imem_outa.v multiplier.v ram_sync.v rs_ldst.v src_manager.v topsim.v

analyze -sv v_decoder.sv
#Elaborating the design
elaborate -top pipeline

#Set the clock
clock clk -both_edges
#Set Reset
reset (reset)
#Prove all
prove -bg -all
