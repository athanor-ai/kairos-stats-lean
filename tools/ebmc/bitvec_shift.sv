// EBMC property check: arithmetic right shift == floor division by 2^m
// Paired with: Pythia/Hardware/BitVec.lean :: arith_shift_right_eq_div

module bitvec_shift;
  parameter N = 16;

  reg [N-1:0] v;
  reg [3:0] m;  // shift amount 0..15

  wire [N-1:0] shifted = v >> m;
  wire [N-1:0] divided = v / (1 << m);

  p_shift_eq_div: assert property (shifted == divided);

endmodule
