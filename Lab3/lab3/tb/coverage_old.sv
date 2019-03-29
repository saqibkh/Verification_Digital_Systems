`include "uvm_macros.svh"
package coverage;
import sequences::*;
import uvm_pkg::*;

class alu_subscriber_in extends uvm_subscriber #(alu_transaction_in);
    `uvm_component_utils(alu_subscriber_in)

    //Declare Variables
    logic [31:0] A;
    logic [31:0] B;
    logic [4:0] opcode;
    logic cin;

    //TODO: Add covergroups for the inputs
    covergroup inputs;
 
      //covlabel_1: coverpoint A {
      //bins low = {[0:150000000]};
      //}

      //covlabel_2: coverpoint B {
      //bins low = {[0:150000000]};
      //}

      //covlabel_3: coverpoint cin {
      //bins up = {0};
      //bins dn = {1};
      //}

      //covlabel_4: coverpoint opcode {
      //bins op1 = {0};
      //}
    //covlabel_3_x_covlabel_4: cross covlabel_3, covlabel_4;
    endgroup: inputs

    function new(string name, uvm_component parent);
        super.new(name,parent);
        /* TODO: Uncomment
        inputs=new;
        */
    endfunction: new

    function void write(alu_transaction_in t);
        A={t.A};
        B={t.B};
        opcode={t.opcode};
        cin={t.CIN};
        /* TODO: Uncomment */
        inputs.sample();
    endfunction: write

endclass: alu_subscriber_in

class alu_subscriber_out extends uvm_subscriber #(alu_transaction_out);
    `uvm_component_utils(alu_subscriber_out)

    logic [31:0] out;
    logic cout;
    logic vout;

    //TODO: Add covergroups for the outputs
    covergroup outputs;
    covlabel_1: coverpoint out {
    bins low = {[0:2000]};
    bins high = {[2001:10000]};
    } 

    covlabel_2: coverpoint cout {
    bins up = {0};
    bins dn = {1};
    }

    covlabel_3: coverpoint vout {
    bins up = {0};
    bins dn = {1};
    }

    endgroup: outputs

function new(string name, uvm_component parent);
    super.new(name,parent);
    /* TODO: Uncomment */
    outputs=new;

endfunction: new

function void write(alu_transaction_out t);
    out={t.OUT};
    cout={t.COUT};
    vout={t.VOUT};
    /*TODO: Uncomment */
    outputs.sample();

endfunction: write
endclass: alu_subscriber_out

endpackage: coverage
