//EE382M-Verification of Digital Systems
//Lab 4 - Formal Property Verification
//
//
//Module - arbiter
//4-way arbiter with multiple arbitration schemes

module arbiter(
  clk,
  rst_n,
  req,
  arb_type,
  gnt
  );

// Input and Output ports
input        clk;
input        rst_n;
input  [3:0] req;
input  [2:0] arb_type;

output [3:0] gnt;

// Internal variables
wire [3:0] req;

reg  [3:0] r_gnt_p0; // P0 priority scheme output
reg  [3:0] r_gnt_p1; // P1 priority scheme output
reg  [3:0] r_gnt_p2; // P2 priority scheme output
reg  [3:0] r_gnt_p3; // P3 priority scheme output
reg  [3:0] r_gnt_rr; // Prr: Round robin arbitration scheme output
reg  [3:0] r_gnt_px; // Prand: Random arbitration scheme output
reg  [3:0] r_gnt;

wire [1:0] rand;
wire [1:0] r_gnt_rr_encoded;

assign gnt   = r_gnt;

// P0 Fixed Priority req[0]
always @(*) begin
  if(req[0])
    r_gnt_p0 = 4'b0001;
  else if(req[1])
    r_gnt_p0 = 4'b0010;
  else if(req[2])
    r_gnt_p0 = 4'b0100;
  else if(req[3])
    r_gnt_p0 = 4'b1000; // Saqib changed this from r_gnt_p0 = 4'b0000;
  else
    r_gnt_p0 = 4'b0000;
end

// P1 Fixed Priority req[1]
always @(*) begin
  if(req[1])
    r_gnt_p1 = 4'b0010;
  else if(req[0])
    r_gnt_p1 = 4'b0001;
  else if(req[2])
    r_gnt_p1 = 4'b0100;
  else if(req[3])
    r_gnt_p1 = 4'b1000;
  else
    r_gnt_p1 = 4'b0000;
end

// P2 Fixed Priority req[2]
always @(*) begin
  if(req[2])
    r_gnt_p2 = 4'b0100;
  else if(req[0])
    r_gnt_p2 = 4'b0001;
  else if(req[1])
    r_gnt_p2 = 4'b0010;
  else if(req[3])
    r_gnt_p2 = 4'b1000;
  else
    r_gnt_p2 = 4'b0000;
end

// P3 Fixed Priority req[3]
always @(*) begin
  if(req[3])
    r_gnt_p3 = 4'b1000;
  else if(req[0])
    r_gnt_p3 = 4'b0001;
  else if(req[1])
    r_gnt_p3 = 4'b0010;
  else if(req[2])
    r_gnt_p3 = 4'b0100;
  else
    r_gnt_p3 = 4'b0000;
end

// Prr: Round robin arbiter
always @ (*) begin
  r_gnt_rr[0] = 
    (r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & req[0]) |
    (r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[3] & req[0]) |
    (~r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[3] & ~req[2] & req[0]) |
    (~r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[3] & ~req[2] & ~req[1] & req[0]) ;

  r_gnt_rr[1] = 
    (r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[0] & req[1]) |
    (r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[3] & ~req[0] & req[1]) |
    (~r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[3] & ~req[2] & ~req[0] & req[1]) |
    (~r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & req[1]) ;
  
  r_gnt_rr[2] = 
    (r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[0] & ~req[1] & req[2]) |
    (r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[3] & ~req[0] & ~req[1] & req[2]) |  // Saqib changed req[1] to ~req[1]
    (~r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & req[2]) |
    (~r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[1] & req[2]) ;
 
  r_gnt_rr[3] = 
    (r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[0] & ~req[1] & ~req[2] & req[3]) |
    (r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & req[3]) |
    (~r_gnt_rr_encoded[1] & r_gnt_rr_encoded[0] & ~req[2] & req[3]) |
    (~r_gnt_rr_encoded[1] & ~r_gnt_rr_encoded[0] & ~req[1] & ~req[2] & req[3]) ;
end

// encode the 4b r_gnt_rrs to 2b
assign r_gnt_rr_encoded = {r_gnt[3] | r_gnt[2], r_gnt[3] | r_gnt[1]};

// Prand: Random arbitration
PNSeqGen u_PNSeqGen ( .clk(clk), .rst_n(rst_n), .rand(rand) );

always @(*) begin
  case(rand)

  2'b00: begin
    if(req[0])
      r_gnt_px = 4'b0001;
    else if(req[1])
      r_gnt_px = 4'b0010;
    else if(req[2])
      r_gnt_px = 4'b0100;
    else if(req[3])
      r_gnt_px = 4'b1000;
    else
      r_gnt_px = 4'b0000;
  end
  
  2'b01: begin
    if(req[1])
      r_gnt_px = 4'b0010;  // Saqib change 4'b0001 to 4'b0010
    else if(req[0])
      r_gnt_px = 4'b0001;  // Saqib change 4'b0010 to 4'b0001
    else if(req[2])
      r_gnt_px = 4'b0100;
    else if(req[3])
      r_gnt_px = 4'b1000;
    else
      r_gnt_px = 4'b0000;
  end

  2'b10: begin
    if(req[2])
      r_gnt_px = 4'b0100;
    else if(req[0])
      r_gnt_px = 4'b0001;
    else if(req[1])
      r_gnt_px = 4'b0010;
    else if(req[3])
      r_gnt_px = 4'b1000;
    else
      r_gnt_px = 4'b0000;
  end

  2'b11: begin
    if(req[3])
      r_gnt_px = 4'b1000;
    else if(req[0])
      r_gnt_px = 4'b0001;
    else if(req[1])
      r_gnt_px = 4'b0010;
    else if(req[2])
      r_gnt_px = 4'b0100;
    else
      r_gnt_px = 4'b0000;
  end

  endcase
end

// Priority selection
always @(posedge clk or negedge rst_n)
begin
  if(!rst_n)
    r_gnt <= 4'b0000;
  else
    case(arb_type)
      4'b0000: r_gnt <= r_gnt_p0;
      4'b0001: r_gnt <= r_gnt_p1;
      4'b0010: r_gnt <= r_gnt_p2;
      4'b0011: r_gnt <= r_gnt_p3;
      4'b0100: r_gnt <= r_gnt_rr;
      4'b0101: r_gnt <= r_gnt_px;
      default: r_gnt <= 4'b0000;
    endcase
end

endmodule

