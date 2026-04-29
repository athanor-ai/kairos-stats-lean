// EBMC property check: adjacent Gray code values differ in exactly 1 bit
// Paired with: Pythia/Hardware/BitVec.lean :: gray_adjacent_hamming_one

module bitvec_gray;
  parameter N = 8;

  reg [N-1:0] v;

  wire [N-1:0] gray_v     = v ^ (v >> 1);
  wire [N-1:0] gray_v1    = (v + 1) ^ ((v + 1) >> 1);
  wire [N-1:0] diff       = gray_v ^ gray_v1;

  // Popcount == 1 means exactly one bit differs.
  // For EBMC: diff is a power of 2 iff diff != 0 and diff & (diff-1) == 0
  wire is_power_of_two = (diff != 0) && ((diff & (diff - 1)) == 0);

  // Only check for v < 2^N - 1 (v+1 doesn't overflow)
  wire in_range = (v < {N{1'b1}});

  p_gray_adjacent: assert property (!in_range || is_power_of_two);

endmodule
