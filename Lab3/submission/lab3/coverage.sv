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
    covlabel_1: coverpoint A {
      bins low = {[0:2147483647]};
    }

    covlabel_2: coverpoint B {
      bins low = {[0:2147483647]};
    }

    covlabel_3: coverpoint cin {
      bins up = {0};
      bins dn = {1};
    }

    covlabel_4: coverpoint opcode {
      bins op0 = {0};
      bins op1 = {1};
      bins op2 = {2};
      bins op3 = {3};
      bins op4 = {4};
      bins op5 = {5};
      bins op6 = {6};
      bins op7 = {7};
      bins op8 = {8};
      bins op9 = {9};
      bins op10 = {10};
      bins op11 = {11};
      bins op12 = {12};
      bins op13 = {13};
      bins op14 = {14};
      bins op15 = {15};
      bins op16 = {16};
      bins op17 = {17};
      bins op18 = {18};
      bins op19 = {19};
      bins op20 = {20};
      bins op21 = {21};
      bins op22 = {22};
      bins op23 = {23};
      bins op24 = {24};
      bins op25 = {25};
      bins op26 = {26};
      bins op27 = {27};
      bins op28 = {28};
      bins op29 = {29};
      bins op30 = {30};
      bins op31 = {31};
      bins op32 = {32};
    }
    endgroup: inputs

    function new(string name, uvm_component parent);
        super.new(name,parent);
        /* TODO: Uncomment
        */ inputs=new;
        
    endfunction: new

    function void write(alu_transaction_in t);
        A={t.A};
        B={t.B};
        opcode={t.opcode};
        cin={t.CIN};
        /* TODO: Uncomment
        */ inputs.sample();
        
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
    /* TODO: Uncomment
    */ outputs=new;
    
endfunction: new

function void write(alu_transaction_out t);
    out={t.OUT};
    cout={t.COUT};
    vout={t.VOUT};
    /*TODO: Uncomment
    */ outputs.sample();
    
endfunction: write
endclass: alu_subscriber_out

endpackage: coverage
