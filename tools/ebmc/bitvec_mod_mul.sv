// EBMC property check: (a * b) % 2^N == ((a % 2^N) * (b % 2^N)) % 2^N
// Paired with: Pythia/Hardware/BitVec.lean :: mul_mod_eq

module bitvec_mod_mul;
  parameter N = 8;
  localparam MOD = 1 << N;

  reg [2*N-1:0] a, b;

  wire [4*N-1:0] lhs = (a * b) % MOD;
  wire [4*N-1:0] rhs = ((a % MOD) * (b % MOD)) % MOD;

  p_mul_mod: assert property (lhs == rhs);

endmodule
