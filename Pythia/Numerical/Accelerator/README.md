# Pythia.Numerical.Accelerator

Formally verified error bounds for hardware accelerator compute patterns.
Built for AWS Trainium / Inferentia NKI kernel developers.

## What's here

| Module | Theorem | Customer question it answers |
|--------|---------|------------------------------|
| `ReductionTree` | tree_reduce_error | "How much error does my tree reduction add vs naive sequential?" |
| `TiledMatMul` | tiled_matmul_error | "What's the error bound for my 512×512 tiled matmul with T=128?" |
| `QuantizedReduction` | mixed_precision_fp16_fp32 | "What's the total error when I quantize inputs to FP16 and accumulate in FP32?" |

## Concrete numbers

A 512-element NKI tile reduction:
- **Tree reduction**: γ₉ · Σ|aᵢ| (depth 9, proved via `native_decide`)
- **Naive sequential**: γ₅₁₂ · Σ|aᵢ|
- **Improvement**: 57× tighter error bound

A 512×512 tiled matmul (T=128, 4 tiles):
- **Error factor**: γ₁₃₀ (tile inner product + tree accumulation)
- **vs naive**: γ₅₁₂
- **Improvement**: 4× tighter

FP16 inputs with FP32 accumulator:
- **Total error**: 2⁻¹⁰ · input_sum + γ_depth · product_sum
- **Quantization term**: ≈0.001 per element (10-bit mantissa)

## How to use

```lean
import Pythia.Numerical.Accelerator.ReductionTree
import Pythia.Numerical.Accelerator.TiledMatMul
import Pythia.Numerical.Accelerator.QuantizedReduction

open Pythia.Numerical

-- Your NKI kernel has 512-element reductions with tree depth 9:
#check ReductionTree.tree_depth_512  -- : tree_depth 512 = 9

-- Your tiled matmul uses T=128 tiles:
#check TiledMatMul.nki_matmul_512_error_factor  -- : 128 + tree_depth 4 = 130
```

## Toolchain

Lean 4.28.0 · Mathlib v4.28.0 · Apache-2.0
