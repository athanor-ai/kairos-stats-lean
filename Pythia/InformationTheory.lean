/-
Pythia.InformationTheory — discrete information theory.

Pythia's information-theory lane: Shannon entropy, channel capacity,
mutual information, AEP, Fano's inequality, rate-distortion,
data-processing inequality.

Mathlib provides `Real.negMulLog`, `Real.binEntropy`,
`InformationTheory.klDiv`, and `InformationTheory.hammingDist` as
primitives; this module surfaces the named channel-capacity theorems
applied mathematicians and information theorists quote.

## Modules

- `Pythia.InformationTheory.Basic`: Shannon entropy non-negativity.
- `Pythia.InformationTheory.ChannelCapacity`: mutual information
  functional, channel capacity as sup over input distributions, and
  the definitional equality `channelCapacity W = iSup (I(p, W))`.
- `Pythia.InformationTheory.MutualInfo`: non-negativity of mutual
  information I(X;Y) ≥ 0 (parametrized / Gibbs form).
- `Pythia.InformationTheory.SourceCoding`: source-coding lower bound
  — expected code length ≥ Shannon entropy (parametrized form).
- `Pythia.InformationTheory.DPI`: data-processing inequality
  I(X;Z) ≤ I(X;Y) for Markov chains X → Y → Z (parametrized form).

## Status

`ChannelCapacity`: sorry-free (channel_capacity_eq_sup_mutual_info
closes by rfl).
`Basic` (shannonEntropy_nonneg): sorry-free.
`MutualInfo` (mutual_info_nonneg_via_gibbs): sorry-free; parametrized
  over Gibbs hypothesis pending discrete KL nonneg API in Mathlib.
`SourceCoding` (optimal_code_length_lower_bound): sorry-free;
  parametrized over Gibbs / Kraft hypothesis.
`DPI` (data_processing_inequality): sorry-free; parametrized over
  chain-rule hypothesis pending conditional-entropy infrastructure.
-/

import Pythia.InformationTheory.Basic
import Pythia.InformationTheory.ChannelCapacity
import Pythia.InformationTheory.MutualInfo
import Pythia.InformationTheory.SourceCoding
import Pythia.InformationTheory.DPI
import Pythia.InformationTheory.AEPBernoulli
import Pythia.InformationTheory.BSCCapacity
import Pythia.InformationTheory.KraftInequality
