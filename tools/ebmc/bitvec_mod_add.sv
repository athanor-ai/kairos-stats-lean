// EBMC property check: (a + b) % 2^N == ((a % 2^N) + (b % 2^N)) % 2^N
// Paired with: Pythia/Hardware/BitVec.lean :: add_mod_eq
// Verification: kairos sv-prove --spec bitvec_mod_add.sv --top bitvec_mod_add --mode k_induction

module bitvec_mod_add;
  parameter N = 8;
  localparam MOD = 1 << N;

  reg [2*N-1:0] a, b;

  // Property: modular addition distributes
  wire [2*N-1:0] lhs = (a + b) % MOD;
  wire [2*N-1:0] rhs = ((a % MOD) + (b % MOD)) % MOD;

  p_add_mod: assert property (lhs == rhs);

endmodule
