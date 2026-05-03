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

- `Pythia.InformationTheory.ChannelCapacity`: mutual information
  functional, channel capacity as sup over input distributions, and
  the definitional equality `channelCapacity W = iSup (I(p, W))`.

## Status

`ChannelCapacity`: sorry-free (channel_capacity_eq_sup_mutual_info
closes by rfl).
`Basic` (shannonEntropy_nonneg + helpers): in-flight via Aristotle
project ec7f9f8e-02e5-44b5-8eb7-93c3cbbdbe7b — do NOT import here
until that file lands.
-/

import Pythia.InformationTheory.ChannelCapacity
