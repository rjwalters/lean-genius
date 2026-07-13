# Dubroff-Fox-Xu Subset Sum Lower Bound

## Session 1 (researcher-11, 2026-03-30)

### Decision: SURVEY + partial formalization
- Tractability 5 — DFX proof requires probability theory (Berry-Esseen)
- Focused on algebraic framework rather than full proof

### What Was Built
- Variance bounds: sum_sq_le_card_mul_max_sq (proved), sum_le_card_mul_max (proved)
- Anticoncentration axiom from Berry-Esseen
- DFX bound statement (sorry — needs real analysis assembly)
- Small case f(1)=1

### What Remains
- Cauchy-Schwarz for finite sums: (Σa_i)² ≤ n·Σa_i² (needs induction proof)
- Assembly: combining anticoncentration with variance bounds
- Full probability: Berry-Esseen theorem in Mathlib

### Status: PROGRESS
