module fifo_verif 
#(	parameter FIFO_DEPTH = 2, 
	parameter DATA_WIDTH = 8
)
(
    input clock,
    input reset,
    input wr,
    input rd,
    input [DATA_WIDTH-1:0] din,
    input empty,
    input full,
    input [DATA_WIDTH-1:0] dout
);
 
wire db_wr, db_rd;
reg dffw1, dffw2, dffr1, dffr2;

always @ (posedge clock) dffw1 <= wr; 
always @ (posedge clock) dffw2 <= dffw1;
assign db_wr = ~dffw1 & dffw2; 

always @ (posedge clock) dffr1 <= rd;
always @ (posedge clock) dffr2 <= dffr1;
assign db_rd = ~dffr1 & dffr2; 

wire wr_en = db_wr; 
wire rd_en = db_rd; 


reg [FIFO_DEPTH-1:0] wr_ptr, rd_ptr;
reg [2**FIFO_DEPTH-1: 0] used_tag;

ck_empty_correctness: assert property ();
cl_full_correctness: assert property ();

 
ck_empty_to_full: cover property ( );
ck_full_to_empty: cover property ();


genvar i;
for (i=0; i<2**FIFO_DEPTH; i++) begin
	ck_all_used: cover property ( );
end


genvar j;
for (j=0; j< (2**FIFO_DEPTH + 3); j++) begin
	ck_wr_num: cover property ( );
	ck_rd_num: cover property ( );
end

endmodule

module wrapper;
bind sync_fifo fifo_verif
#(
	.FIFO_DEPTH(abits), 
	.DATA_WIDTH(dbits)
)
fifo_verif_inst(
    //bind your signals here
);


endmodule

