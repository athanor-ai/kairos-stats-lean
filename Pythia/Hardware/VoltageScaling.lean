import Mathlib

-- Dynamic voltage-frequency scaling (DVFS) safety.
-- Frequency must be reduced before voltage drops,
-- voltage must be raised before frequency increases.
-- Violating this order causes timing violations.

structure DVFSState where
  voltage : ℕ  -- in mV
  frequency : ℕ  -- in MHz

-- Safe DVFS transition: scale down = freq first, scale up = voltage first
def safeScaleDown (s : DVFSState) (new_freq new_volt : ℕ)
    (h_freq : new_freq ≤ s.frequency) (h_volt : new_volt ≤ s.voltage) :
    List DVFSState :=
  [{ voltage := s.voltage, frequency := new_freq },
   { voltage := new_volt, frequency := new_freq }]

def safeScaleUp (s : DVFSState) (new_freq new_volt : ℕ)
    (h_freq : s.frequency ≤ new_freq) (h_volt : s.voltage ≤ new_volt) :
    List DVFSState :=
  [{ voltage := new_volt, frequency := s.frequency },
   { voltage := new_volt, frequency := new_freq }]

-- Scale-down intermediate state has safe voltage (not yet reduced)
theorem scale_down_voltage_safe (s : DVFSState) (nf nv : ℕ)
    (hf : nf ≤ s.frequency) (hv : nv ≤ s.voltage) :
    (safeScaleDown s nf nv hf hv).head? = some { voltage := s.voltage, frequency := nf } := by
  simp [safeScaleDown]

-- Scale-up intermediate state has safe frequency (not yet increased)
theorem scale_up_freq_safe (s : DVFSState) (nf nv : ℕ)
    (hf : s.frequency ≤ nf) (hv : s.voltage ≤ nv) :
    (safeScaleUp s nf nv hf hv).head? = some { voltage := nv, frequency := s.frequency } := by
  simp [safeScaleUp]
