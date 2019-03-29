`include "uvm_macros.svh"
package scoreboard; 
import uvm_pkg::*;
import sequences::*;

class alu_scoreboard extends uvm_scoreboard;
    `uvm_component_utils(alu_scoreboard)

    logic [33:0] result;

    uvm_analysis_export #(alu_transaction_in) sb_in;
    uvm_analysis_export #(alu_transaction_out) sb_out;

    uvm_tlm_analysis_fifo #(alu_transaction_in) fifo_in;
    uvm_tlm_analysis_fifo #(alu_transaction_out) fifo_out;

    alu_transaction_in tx_in;
    alu_transaction_out tx_out;

    function new(string name, uvm_component parent);
        super.new(name,parent);
        tx_in=new("tx_in");
        tx_out=new("tx_out");
    endfunction: new

    function void build_phase(uvm_phase phase);
        sb_in=new("sb_in",this);
        sb_out=new("sb_out",this);
        fifo_in=new("fifo_in",this);
        fifo_out=new("fifo_out",this);
    endfunction: build_phase

    function void connect_phase(uvm_phase phase);
        sb_in.connect(fifo_in.analysis_export);
        sb_out.connect(fifo_out.analysis_export);
    endfunction: connect_phase

    task run();
        forever begin
            fifo_in.get(tx_in);
            fifo_out.get(tx_out);
            compare();
        end
    endtask: run

    extern virtual function [33:0] getresult; 
    extern virtual function void compare; 
        
endclass: alu_scoreboard

function void alu_scoreboard::compare;
    //TODO: Write this function to check whether the output of the DUT matches
    //the spec.
    //Use the getresult() function to get the spec output.
    //Consider using `uvm_info(ID,MSG,VERBOSITY) in this function to print the
    //results of the comparison.
    //You can use tx_in.convert2string() and tx_out.convert2string() for
    //debugging purposes

    logic [33:0] result;
    result = getresult();

    //if(tx_out.VOUT==result[33] && tx_out.OUT==result[31:0]&& tx_out.COUT==result[32])
    //begin
    //`uvm_info("0",$sformatf("\nActual Input Values  \n RST =%b A =%b B =%b CIN =%b Opcode =%b\nActual Outputs \n COUT =%b VOUT =%b OUT =%b\nExpected Output \n COUT =%b VOUT =%b OUT =%b \n",tx_in.rst,tx_in.A,tx_in.B,tx_in.CIN,tx_in.opcode,tx_out.COUT, tx_out.VOUT, tx_out.OUT,result[32],result[33],result[31:0]) ,UVM_HIGH);
    //end

    if(tx_out.VOUT!=result[33] || $isunknown(tx_out.VOUT))
    begin
    `uvm_info("1",$sformatf("\nActual Input Values  \n RST =%b A =%b B =%b CIN =%b Opcode =%b\nActual Outputs \n COUT =%b VOUT =%b OUT =%b\nExpected Output \n COUT =%b VOUT =%b OUT =%b \n",tx_in.rst,tx_in.A,tx_in.B,tx_in.CIN,tx_in.opcode,tx_out.COUT, tx_out.VOUT, tx_out.OUT,result[32],result[33],result[31:0]) ,UVM_HIGH);
    end

    if(tx_out.COUT!=result[32] || $isunknown(tx_out.COUT))
    begin
    `uvm_info("2",$sformatf("\nActual Input Values  \n RST =%b A =%b B =%b CIN =%b Opcode =%b\nActual Outputs \n COUT =%b VOUT =%b OUT =%b\nExpected Output \n COUT =%b VOUT =%b OUT =%b \n",tx_in.rst,tx_in.A,tx_in.B,tx_in.CIN,tx_in.opcode,tx_out.COUT, tx_out.VOUT, tx_out.OUT,result[32],result[33],result[31:0]) ,UVM_HIGH);
    end

    if(tx_out.OUT!=result[31:0] || $isunknown(result[31:0]))
    begin
    `uvm_info("3",$sformatf("\nActual Input Values  \n RST =%b A =%b B =%b CIN =%b Opcode =%b\nActual Outputs \n COUT =%b VOUT =%b OUT =%b\nExpected Output \n COUT =%b VOUT =%b OUT =%b \n",tx_in.rst,tx_in.A,tx_in.B,tx_in.CIN,tx_in.opcode,tx_out.COUT, tx_out.VOUT, tx_out.OUT,result[32],result[33],result[31:0]) ,UVM_HIGH);
    end

endfunction

function [33:0] alu_scoreboard::getresult;
    //TODO: Remove the statement below
    //Modify this function to return a 34-bit result {VOUT, COUT,OUT[31:0]} which is
    //consistent with the given spec.

    logic [31:0] out;
    logic cout;
    logic vout;

    // Use of scratch register
    logic [32:0] cout_out;
    logic signed [31:0] signed_out;
    logic signed [31:0] signed_A;
    logic signed [31:0] signed_B;

    signed_A = tx_in.A;
    signed_B = tx_in.B;

    // If reset is enabled then return all zeros
    if(tx_in.rst)
      begin
      return 34'd0;
      //cout=0;
      //vout=0;
    end

    /////////////////////////////////////////////////////////////////////////
    //       Start Logic Operations (00---)
    /////////////////////////////////////////////////////////////////////////
    // 00111 A OR B
    if(tx_in.opcode==5'b00111)
      begin
      out = tx_in.A|tx_in.B;
      cout=0;
      vout=0;
    end

    // 00011 A XOR B
    if(tx_in.opcode==5'b00011)
      begin
      return 34'd0;
      //cout=0;
      //vout=0;
    end

    // 00000 NOT A
    if(tx_in.opcode==5'b00000)
      begin
      out = ~tx_in.A;
      cout = 0;
      vout = 0;
    end

    // 00101 A AND B
    if(tx_in.opcode==5'b00101)
      begin
      out = tx_in.A&tx_in.B;
      cout = 0;
      vout = 0;
    end
   
    // Following are undefined opcodes for logical operations 
    if(tx_in.opcode==5'b00001)
      begin
      return 34'd0;
    end
    if(tx_in.opcode==5'b00010)
      begin
      return 34'd0;
    end
    if(tx_in.opcode==5'b00100)
      begin
      return 34'd0;
    end
    if(tx_in.opcode==5'b00110)
      begin
      return 34'd0;
    end
    /////////////////////////////////////////////////////////////////////////
    //       End Logic Operations (00---)
    //////////////////////////////////////////////////////////////////////////


    /////////////////////////////////////////////////////////////////////////
    //       Start Compare Operations (01---)
    //////////////////////////////////////////////////////////////////////////

    // 01100 A <= B
    if((tx_in.opcode==5'b01100))
      begin
      if(signed_A <= signed_B)
      begin
        out = 32'b00000000000000000000000000000001;
        cout = 0;
        vout = 0;
      end
      else
      begin
        out = 32'b00000000000000000000000000000000;
        cout = 0;
        vout = 0;
      end
    end

    // 01001 A < B
    if((tx_in.opcode==5'b01001))
      begin
      if(signed_A < signed_B)
      begin
        out = 32'b00000000000000000000000000000001;
        cout = 0;
        vout = 0;
      end
      else
      begin
        out = 32'b00000000000000000000000000000000;
        cout = 0;
        vout = 0;
      end
    end

    // 01110 A >= B
    if((tx_in.opcode==5'b01110))
      begin
      if(signed_A >= signed_B)
      begin
        out = 32'b00000000000000000000000000000001;
        cout = 0;
        vout = 0;
      end
      else
      begin
        out = 32'b00000000000000000000000000000000;
        cout = 0;
        vout = 0;
      end
    end

    // 01011 A > B
    if((tx_in.opcode==5'b01011))
      begin
      if(signed_A > signed_B)
      begin
        out = 32'b00000000000000000000000000000001;
        cout = 0;
        vout = 0;
      end
      else
      begin
        out = 32'b00000000000000000000000000000000;
        cout = 0;
        vout = 0;
      end
    end

    // 01111 A = B
    if((tx_in.opcode==5'b01111))
      begin
      if(signed_A == signed_B)
      begin
        out = 32'b00000000000000000000000000000001;
        cout = 0;
        vout = 0;
      end
      else
      begin
        out = 32'b00000000000000000000000000000000;
        cout = 0;
        vout = 0;
      end
    end

    // 01010 A != B
    if((tx_in.opcode==5'b01010))
      begin
      if(signed_A != signed_B)
      begin
        out = 32'b00000000000000000000000000000001;
        cout = 0;
        vout = 0;
      end
      else
      begin
        out = 32'b00000000000000000000000000000000;
        cout = 0;
        vout = 0;
      end
    end

    // Following are undefined opcodes for compare operations
    if(tx_in.opcode==5'b01000)
      begin
      return 34'd0;
    end
    if(tx_in.opcode==5'b01101)
      begin
      return 34'd0;
    end

    /////////////////////////////////////////////////////////////////////////
    //       End Compare Operations (01---)
    //////////////////////////////////////////////////////////////////////////


    /////////////////////////////////////////////////////////////////////////
    //       End Arithmetic Operations (10---)
    //////////////////////////////////////////////////////////////////////////
   
    // 10101 add signed addition (A + B)
    if(tx_in.opcode==5'b10101)
      begin
      out = signed_A+signed_B+tx_in.CIN;

      //For add, if the inputs have the same sign (say 0) and the output has the opposite sign (say 1), then VOUT is 1.
      if((tx_in.A[31]==tx_in.B[31]) && (out[31]==~tx_in.A[31]))
        begin
        vout = 1;
      end

      // Check for carry out
      cout_out = signed_A+signed_B+tx_in.CIN; 
      if (cout_out[32] == 1'b1)
        begin
        cout = 1;
      end
    end

    // 10001 addu unsigned addtion A + B
    if(tx_in.opcode==5'b10001)
      begin
      out = tx_in.A+tx_in.B+tx_in.CIN;

   
      // Check for carry out and vout
      cout_out = tx_in.A+tx_in.B+tx_in.CIN;
      if (cout_out[32] == 1'b1)
        begin
        cout = 1;
        vout = 1;
      end
      else
      begin
        cout = 0;
        vout = 0;
      end
    end

    // 10100 sub signed subtraction (A-B)
    if(tx_in.opcode==5'b10100)
      begin
      out = signed_A-signed_B;

      //For sub, if the inputs have different signs for A (say 0) and B (say 1) and the output has a different sign than A (say 1), then VOUT is 1.
      if((tx_in.A[31]!=tx_in.B[31]) && (out[31]!=tx_in.A[31]))
        begin
        vout = 1;
      end

      cout_out = signed_A+signed_B+tx_in.CIN;
      if (cout_out[32] == 1'b1)
        begin
        cout = 1;
      end
    end

    // 10000 subu unsigned subtraction A - B
    if(tx_in.opcode==5'b10000)
      begin
      out = tx_in.A-tx_in.B;
      cout = 1;
      vout = 0;
    end

    // 10111 inc signed increment (A+1)
    if(tx_in.opcode==5'b10111)
      begin
      out = signed_A + 1'b1;

      //For add, if the inputs have the same sign (say 0) and the output has the opposite sign (say 1), then VOUT is 1.
      if(out[31]==~tx_in.A[31])
        begin
        vout = 1;
      end

      // Check for carry out
      cout_out = signed_A+1;
      if (cout_out[32] == 1'b1)
        begin
        cout = 1;
      end

    end

    // 10110 dec signed decrement (A-1))
    if(tx_in.opcode==5'b10110)
      begin
      out = signed_A - 1'b1;

      //For sub, if the inputs have different signs for A (say 0) and B (say 1) and the output has a different sign than A (say 1), then VOUT is 1.
      if(out[31]!=tx_in.A[31])
        begin
        vout = 1;
      end

      cout_out = signed_A-1;
      if (cout_out[32] == 1'b1)
        begin
        cout = 1;
      end
    end
 
    // Following are undefined opcodes for compare operations
    if(tx_in.opcode==5'b10010)
      begin
      return 34'd0;
    end
    if(tx_in.opcode==5'b10011)
      begin
      return 34'd0;
    end
    /////////////////////////////////////////////////////////////////////////
    //       End Arithmetic Operations (10---)
    //////////////////////////////////////////////////////////////////////////

    /////////////////////////////////////////////////////////////////////////
    //       Start Shift Operations (11---)
    /////////////////////////////////////////////////////////////////////////

    // 11010 sll logic left shift A by amout of B[4:0]
    if(tx_in.opcode==5'b11010)
    begin
      out = tx_in.A << tx_in.B[4:0];
      cout = 0;
      vout = 0;
    end
    
    // 11011: srl => logic right shift A by the amount of B[4:0]
    if(tx_in.opcode==5'b11011)
    begin
      out = tx_in.A >> tx_in.B[4:0];
      cout = 0;
      vout = 0;
    end

    // 11100: sla => arithmetic left shift A by the amount of B[4:0]
    if(tx_in.opcode==5'b11100)
    begin
      out = tx_in.A <<< tx_in.B[4:0];
      cout = 0;

      // In shift left arithmetic, VOUT will be asserted in the case of "Overflow".
      // That is the case when you shift out significant bits.
      // For example, shifting 1100 left by 2 would result in an overflow.
      if(tx_in.A[31]!=out[31])
      begin
        vout = 1;
      end
      else
      begin
        vout = 0;
      end
    end

    // 11101: sra => arithmetic right shift A by the amount of B[4:0]
    signed_out = tx_in.A;
    if(tx_in.opcode==5'b11101)
    begin
      out = signed_out >>> tx_in.B[4:0];
      cout = 0;
      if(tx_in.A[tx_in.B[4:0]] == 1)
      begin
        vout = 1;
      end
      else
      begin
        vout = 0;
      end
    end

    // 11000: slr => rotate left shift A by the amount of B[4:0]
    if(tx_in.opcode==5'b11000)
    begin
      out = (tx_in.A << tx_in.B[4:0]) | (tx_in.A >> (32 - tx_in.B[4:0]));
      cout = 0;
      vout = 0;
    end

    // 11001: srr => rotate right shift A by the amount of B[4:0]
    if(tx_in.opcode==5'b11001)
    begin
      out = (tx_in.A >> tx_in.B[4:0]) | (tx_in.A << ~tx_in.B[4:0]);
      cout = 0;
      vout = 0;
    end

    // Following are undefined opcodes for compare operations
    if(tx_in.opcode==5'b11110)
      begin
      return 34'd0;
    end
    if(tx_in.opcode==5'b11111)
      begin
      return 34'd0;
    end

    /////////////////////////////////////////////////////////////////////////
    //       End Shift Operations (11---)
    /////////////////////////////////////////////////////////////////////////


    result = {vout, cout, out};
    return result;

endfunction

endpackage: scoreboard
