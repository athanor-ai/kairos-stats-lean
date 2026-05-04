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
- `Pythia.InformationTheory.GibbsInequality`: discrete KL divergence
  non-negativity (Gibbs’ inequality / information inequality).
- `Pythia.InformationTheory.KLChainRule`: KL divergence chain rule
  for product distributions.
- `Pythia.InformationTheory.FanoInequality`: Fano’s inequality
  converse and capacity bound.
- `Pythia.InformationTheory.ConditionalEntropy`: conditional entropy
  definition and conditioning-reduces-entropy theorem.
- `Pythia.InformationTheory.SanovFinite`: Sanov-style large deviation
  bounds and exponential consistency.

## Status

All modules are sorry-free and axiom-clean (propext, Classical.choice,
Quot.sound only).
-/

import Pythia.InformationTheory.Basic
import Pythia.InformationTheory.ChannelCapacity
import Pythia.InformationTheory.MutualInfo
import Pythia.InformationTheory.SourceCoding
import Pythia.InformationTheory.DPI
import Pythia.InformationTheory.AEPBernoulli
import Pythia.InformationTheory.BSCCapacity
import Pythia.InformationTheory.KraftInequality
import Pythia.InformationTheory.GibbsInequality
import Pythia.InformationTheory.KLChainRule
import Pythia.InformationTheory.FanoInequality
import Pythia.InformationTheory.ConditionalEntropy
import Pythia.InformationTheory.SanovFinite
