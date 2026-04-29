// EBMC property check: unsigned overflow detection
// a + b >= 2^N iff (a + b) % 2^N < a (when a,b < 2^N)
// Paired with: Pythia/Hardware/BitVec.lean :: unsigned_add_overflow_iff

module bitvec_overflow;
  parameter N = 8;
  localparam MOD = 1 << N;

  reg [N-1:0] a, b;
  wire [N:0] sum_ext = {1'b0, a} + {1'b0, b};

  wire overflow = sum_ext[N];  // carry out = overflow
  wire [N-1:0] wrapped = sum_ext[N-1:0];
  wire wrapped_lt_a = (wrapped < a);

  // overflow iff wrapped result < a
  p_overflow_iff: assert property (overflow == wrapped_lt_a);

endmodule
