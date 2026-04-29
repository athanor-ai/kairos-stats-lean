// EBMC property check: k-induction on a simple counter FSM
// Tests that EBMC's --mode k_induction correctly verifies an
// inductive invariant. This is the empirical counterpart to
// Pythia/Hardware/KInduction.lean :: k_induction_soundness
//
// The property: a 4-bit counter never reaches 15 if reset holds
// it below 14. k=1 induction suffices.

module k_induction_fsm;
  reg clk;
  reg rst;
  reg [3:0] count;

  initial begin
    clk = 0;
    rst = 1;
    count = 0;
  end

  always @(posedge clk) begin
    if (rst)
      count <= 0;
    else if (count < 14)
      count <= count + 1;
    else
      count <= count;  // saturate at 14
  end

  // Property: count never reaches 15
  p_count_bounded: assert property (@(posedge clk) count < 15);

endmodule
