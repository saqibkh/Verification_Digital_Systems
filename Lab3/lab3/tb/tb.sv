`timescale 1ns / 100ps
`include "uvm_macros.svh"
import uvm_pkg::*;
import modules_pkg::*;
import sequences::*;
import coverage::*;
import scoreboard::*;
import tests::*;

module dut(dut_in _in, dut_out _out);
ALU alu0(
    .CLK(_in.clk),
    .RST(_in.rst),
    .A(_in.A),
    .B(_in.B),
    .CIN(_in.CIN),
    .OPCODE(_in.opcode),
    .OUT(_out.OUT),
    .COUT(_out.COUT),
    .VOUT(_out.VOUT)
);
endmodule: dut

module top;    
dut_in dut_in1();
dut_out dut_out1();

initial begin
    dut_in1.clk<=0;
    forever #50 dut_in1.clk<=~dut_in1.clk;
end

initial begin
    dut_out1.clk<=0;
    forever #50 dut_out1.clk<=~dut_out1.clk;
end

// TODO: Instantiate the dut module as dut1 and use the input as dut_in1 and output as dut_out1
dut dut1(
    ._in(dut_in1),
    ._out(dut_out1)
);

initial begin
    uvm_config_db #(virtual dut_in)::set(null,"uvm_test_top","dut_vi_in",dut_in1);
    uvm_config_db #(virtual dut_out)::set(null,"uvm_test_top","dut_vi_out",dut_out1);
    uvm_top.finish_on_completion=1;

    //TODO:Modify the test name here
    run_test("test1");
end

endmodule: top
