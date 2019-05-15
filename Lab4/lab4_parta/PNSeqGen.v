//EE382M-Verification of Digital Systems
//Lab 4 - Formal Property Verification
//
//
//Module - PNSeqGen
//Pseudo-random pattern generator

module PNSeqGen(
  input        clk,
  input        rst_n,
  output [1:0] rand
  );

reg s1, s2, s3;
wire s0;

assign s0 = s1 ^ s3;

always @ (posedge clk or negedge rst_n) begin
  if(!rst_n) begin
   s1 <= 1;
   s2 <= 0;
   s3 <= 0;
  end else begin   
   s1 <= s0;
   s2 <= s1;
   s3 <= s2;
  end
end

assign rand = {s3,s2};

endmodule
