// EBMC property check: FIFO pointer empty/full conditions
// Paired with: Pythia/Hardware/BitVec.lean :: fifo_empty_iff, fifo_full_iff

module fifo_pointer;
  parameter N = 4;
  localparam DEPTH = 1 << N;

  reg [N-1:0] rd_ptr, wr_ptr;

  // Empty: rd == wr (mod 2^N)
  wire empty = (rd_ptr == wr_ptr);
  wire empty_alt = ((wr_ptr - rd_ptr) % DEPTH == 0);
  p_empty_iff: assert property (empty == empty_alt);

  // Full: (wr + 1) == rd (mod 2^N)
  wire full = ((wr_ptr + 1'b1) == rd_ptr);
  wire [N-1:0] occupancy = wr_ptr - rd_ptr;
  wire full_alt = (occupancy == DEPTH - 1);
  p_full_iff: assert property (full == full_alt);

endmodule
