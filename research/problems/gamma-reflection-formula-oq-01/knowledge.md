# Euler's reflection formula: Γ(s)·Γ(1−s) = π / sin(πs)

## Summary

Reflection formula as a gallery entry. The core identity is Mathlib's
`Real.Gamma_mul_Gamma_one_sub` / `Complex.Gamma_mul_Gamma_one_sub`. Mathlib already
has the identity, the non-vanishing lemma `Real.Gamma_ne_zero` (for arguments avoiding
non-positive integers), and `Real.Gamma_one_half_eq : Γ(1/2) = √π`. The genuine new
content is the set of **concrete special-value products** that reflection evaluates
exactly even though the individual values are non-elementary, plus a clean sin-based
non-vanishing derivation.

## Session 2026-06-20 (Session 1) — FRESH

**Mode**: FRESH
**Outcome**: completed (build pending at time of writing)

### What I Did
- Claimed the problem; verified all vehicle/support lemmas against Mathlib v4.x source
  before building (expensive cold-cache full-Mathlib build).
- Wrote `proofs/Proofs/GammaReflectionFormulaOQ01.lean` (108 lines, 8 theorems, 0 sorry,
  0 axiom declarations).

### Key Findings
- Mathlib already provides reflection (real + complex), the non-vanishing lemma
  `Real.Gamma_ne_zero {s} (∀ m:ℕ, s ≠ -m)`, and `Real.Gamma_one_half_eq`. So a bare
  re-export would be a thin wrapper. The honest novel content is the concrete product
  evaluations, absent from Mathlib:
  - `Γ(1/2)² = π`  (sin(π/2)=1)
  - `Γ(1/4)·Γ(3/4) = π√2`  (sin(π/4)=√2/2)
  - `Γ(1/3)·Γ(2/3) = 2π/√3`  (sin(π/3)=√3/2)
  - `Γ(1/6)·Γ(5/6) = 2π`  (sin(π/6)=1/2)
- The deterministic proof pattern for each: specialize `Real.Gamma_mul_Gamma_one_sub`,
  `rw` the `1 - s` and `π * s` numerals, rewrite the special sin value, then close with
  `div_div_eq_mul_div` + (`ring` | `div_eq_iff` + `mul_assoc` + `Real.mul_self_sqrt`).
- Non-vanishing read straight off reflection: if `sin(π s) ≠ 0` the product equals the
  nonzero `π/sin(π s)`, so `Γ s ≠ 0` (`gamma_ne_zero_of_sin_ne_zero`); specialized to
  non-integer `s` via `Real.sin_eq_zero_iff` (`gamma_ne_zero_of_not_int`).

### Files Modified
- proofs/Proofs/GammaReflectionFormulaOQ01.lean (new)
- src/data/proofs/gamma-reflection-formula-oq-01/meta.json (new)

### Next Steps
- If build green: `#print axioms`, finalize meta, open PR.
- Follow-ups: Beta-function value B(1/2,1/2)=π via reflection; the `1/Γ` entire-function
  picture; Γ(1/4) individual value via the lemniscate constant (much harder, likely not
  in Mathlib).
