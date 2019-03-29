`include "uvm_macros.svh"
package modules_pkg;

import uvm_pkg::*;
import sequences::*;
import coverage::*;
import scoreboard::*;

typedef uvm_sequencer #(alu_transaction_in) alu_sequencer_in;

class alu_dut_config extends uvm_object;
    `uvm_object_utils(alu_dut_config)

    virtual dut_in dut_vi_in;
    virtual dut_out dut_vi_out;

endclass: alu_dut_config

class alu_driver_in extends uvm_driver#(alu_transaction_in);
    `uvm_component_utils(alu_driver_in)

    alu_dut_config dut_config_0;
    virtual dut_in dut_vi_in;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
       assert( uvm_config_db #(alu_dut_config)::get(this, "", "dut_config", dut_config_0));
       dut_vi_in = dut_config_0.dut_vi_in;
    endfunction : build_phase
   
    task run_phase(uvm_phase phase);
      forever
      begin
        alu_transaction_in tx;
        
        @(posedge dut_vi_in.clk);
        seq_item_port.get(tx);
        
        // TODO: Drive values from alu_transaction_in onto the virtual
        // interface of dut_vi_in
        //dut_vi_in.clk <= tx.clk; Saqib commented this out
        dut_vi_in.rst <= tx.rst;
        dut_vi_in.A <= tx.A;
        dut_vi_in.B <= tx.B;
        dut_vi_in.CIN <= tx.CIN;
        dut_vi_in.opcode <= tx.opcode;
      end
    endtask: run_phase

endclass: alu_driver_in

class alu_monitor_in extends uvm_monitor;
    `uvm_component_utils(alu_monitor_in)

    uvm_analysis_port #(alu_transaction_in) aport;

    alu_dut_config dut_config_0;

    virtual dut_in dut_vi_in;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        dut_config_0=alu_dut_config::type_id::create("config");
        aport=new("aport",this);
        assert( uvm_config_db #(alu_dut_config)::get(this, "", "dut_config", dut_config_0) );
        dut_vi_in=dut_config_0.dut_vi_in;

    endfunction: build_phase

    task run_phase(uvm_phase phase);
    @(posedge dut_vi_in.clk);
      forever
      begin
        alu_transaction_in tx;
        @(posedge dut_vi_in.clk);
        tx = alu_transaction_in::type_id::create("tx");
        // TODO: Read the values from the virtual interface of dut_vi_in and
        // assign them to the transaction "tx"
        //tx.clk = dut_vi_in.clk; Saqib commented this out
        tx.rst = dut_vi_in.rst;
        tx.A = dut_vi_in.A;
        tx.B = dut_vi_in.B;
        tx.CIN = dut_vi_in.CIN;
        tx.opcode = dut_vi_in.opcode;
        aport.write(tx);
      end
    endtask: run_phase

endclass: alu_monitor_in


class alu_monitor_out extends uvm_monitor;
    `uvm_component_utils(alu_monitor_out)

    uvm_analysis_port #(alu_transaction_out) aport;

    alu_dut_config dut_config_0;

    virtual dut_out dut_vi_out;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        dut_config_0=alu_dut_config::type_id::create("config");
        aport=new("aport",this);
        assert( uvm_config_db #(alu_dut_config)::get(this, "", "dut_config", dut_config_0) );
        dut_vi_out=dut_config_0.dut_vi_out;

    endfunction: build_phase

    task run_phase(uvm_phase phase);
    @(posedge dut_vi_out.clk);
    @(posedge dut_vi_out.clk);
      forever
      begin
        alu_transaction_out tx;
        
        @(posedge dut_vi_out.clk);
        tx = alu_transaction_out::type_id::create("tx");
        // TODO: Read the values from the virtual interface of dut_vi_out and
        // assign them to the transaction "tx"
        tx.OUT = dut_vi_out.OUT;
        tx.COUT = dut_vi_out.COUT;
        tx.VOUT = dut_vi_out.VOUT;
        aport.write(tx);
      end
    endtask: run_phase
endclass: alu_monitor_out

class alu_agent_in extends uvm_agent;
    `uvm_component_utils(alu_agent_in)

    uvm_analysis_port #(alu_transaction_in) aport;

    alu_sequencer_in alu_sequencer_in_h;
    alu_driver_in alu_driver_in_h;
    alu_monitor_in alu_monitor_in_h;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new


    function void build_phase(uvm_phase phase);
        aport=new("aport",this);
        alu_sequencer_in_h=alu_sequencer_in::type_id::create("alu_sequencer_in_h",this);
        alu_driver_in_h=alu_driver_in::type_id::create("alu_driver_in_h",this);
        alu_monitor_in_h=alu_monitor_in::type_id::create("alu_monitor_in_h",this);
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        alu_driver_in_h.seq_item_port.connect(alu_sequencer_in_h.seq_item_export);
        alu_monitor_in_h.aport.connect(aport);
    endfunction: connect_phase

endclass: alu_agent_in

class alu_agent_out extends uvm_agent;
    `uvm_component_utils(alu_agent_out)

    uvm_analysis_port #(alu_transaction_out) aport;

    alu_monitor_out alu_monitor_out_h;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        aport=new("aport",this);
        alu_monitor_out_h=alu_monitor_out::type_id::create("alu_monitor_out_h",this);
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        alu_monitor_out_h.aport.connect(aport);
    endfunction: connect_phase

endclass: alu_agent_out


class alu_env extends uvm_env;
    `uvm_component_utils(alu_env)

    alu_agent_in alu_agent_in_h;
    alu_agent_out alu_agent_out_h;
    alu_subscriber_in alu_subscriber_in_h;
    alu_subscriber_out alu_subscriber_out_h;
    alu_scoreboard alu_scoreboard_h;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        alu_agent_in_h = alu_agent_in::type_id::create("alu_agent_in_h",this);
        alu_agent_out_h = alu_agent_out::type_id::create("alu_agent_out_h",this);
        alu_subscriber_in_h = alu_subscriber_in::type_id::create("alu_subscriber_in_h",this);
        alu_subscriber_out_h = alu_subscriber_out::type_id::create("alu_subscriber_out_h",this);
        alu_scoreboard_h = alu_scoreboard::type_id::create("alu_scoreboard_h",this);
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        alu_agent_in_h.aport.connect(alu_subscriber_in_h.analysis_export);
        alu_agent_out_h.aport.connect(alu_subscriber_out_h.analysis_export);
        alu_agent_in_h.aport.connect(alu_scoreboard_h.sb_in);
        alu_agent_out_h.aport.connect(alu_scoreboard_h.sb_out);
    endfunction: connect_phase

    function void start_of_simulation_phase(uvm_phase phase);
        //TODO: Use this command to set the verbosity of the testbench. By
        //default, it is UVM_MEDIUM
        uvm_top.set_report_verbosity_level_hier(UVM_HIGH);
    endfunction: start_of_simulation_phase

endclass: alu_env

class alu_test extends uvm_test;
    `uvm_component_utils(alu_test)

    alu_dut_config dut_config_0;
    alu_env alu_env_h;

    function new(string name, uvm_component parent);
        super.new(name,parent);
    endfunction: new

    function void build_phase(uvm_phase phase);
        dut_config_0 = new();
        if(!uvm_config_db #(virtual dut_in)::get( this, "", "dut_vi_in", dut_config_0.dut_vi_in))
          `uvm_fatal("NOVIF", "No virtual interface set for dut_in")
        
        if(!uvm_config_db #(virtual dut_out)::get( this, "", "dut_vi_out", dut_config_0.dut_vi_out))
          `uvm_fatal("NOVIF", "No virtual interface set for dut_out")
            
        uvm_config_db #(alu_dut_config)::set(this, "*", "dut_config", dut_config_0);
        alu_env_h = alu_env::type_id::create("alu_env_h", this);
    endfunction: build_phase

endclass:alu_test

endpackage: modules_pkg
