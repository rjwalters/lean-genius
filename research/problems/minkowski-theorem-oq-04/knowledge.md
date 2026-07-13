# Knowledge Base: minkowski-theorem-oq-04

Insights accumulated during research on Blichfeldt's theorem (k+1 congruent
points when vol > k) and its corollary recovery of Minkowski.

---

## Problem Understanding

**Blichfeldt's theorem (1914)**: For measurable S ⊆ ℝⁿ with vol(S) > k, there
exist k+1 distinct points x₁,...,x_{k+1} ∈ S whose pairwise differences lie in
ℤⁿ. Generalizes Minkowski (no convexity or symmetry needed). Minkowski is
recovered via T = (1/2)·S: vol(T) = vol(S)/2ⁿ > 1 ⇒ a, b ∈ T with a − b ∈ ℤⁿ;
central symmetry + convexity then give a − b ∈ S ∩ ℤⁿ \ {0}.

---

## Insights

### Sessions 1–3 (initial formalization, 2026-05-06/07)
- Proof uses fundamental-domain pigeonhole: if projections {Sᵥ}_{v∈ℤⁿ} are
  pairwise disjoint, ∑ vol(Sᵥ) ≤ vol(F) = 1 < vol(S).
- Three measure-theoretic axioms captured the pigeonhole engine; one general-k
  axiom captured the covering-count averaging step.
- Mathlib 4.26.0 API drift fixes: `Pairwise (Disjoint on f)` → lambda rewrite;
  ENNReal Nat-coerce via `exact_mod_cast`; `Submodule.mem_toAddSubgroup`
  removal compensation.

### Session 4 (this session, 2026-05-07T20:08Z)

**Axiom reduction 4 → 2 confirmed**: read of source revealed that the JSON
nextSteps list claiming "4 axioms" was stale — earlier sessions had already
converted `blichfeldt_proj_measurable` and `blichfeldt_disj_bound` from
`axiom` to `theorem` (lines 66 and 83 of MinkowskiTheoremOQ04.lean). Only
`blichfeldt_volume_partition` and `blichfeldt_general` remain as axioms.

**Both `minkowski_from_blichfeldt` sorries closed.**

1. **Sorry 1 — measurability of T = (1/2)·s**:
   - Pattern: rewrite the image `(2:ℝ)⁻¹ • s = ((2:ℝ)·) ⁻¹' s` via the
     `inv_smul = preimage` identity (`smul_smul` + `mul_inv_cancel₀`).
   - Then use `MeasurableSet.preimage` with `measurable_const_smul (2:ℝ)`.
   - Reused the bridge from `Erdos353Problem.lean:272-279` (Koizumi 2025
     formalization) which establishes `c⁻¹ • A = (c • ·) ⁻¹' A`.

2. **Sorry 2 — vol(T) > 1 from vol(s) > 2ⁿ**:
   - Apply `MeasureTheory.Measure.addHaar_smul volume (2:ℝ)⁻¹ s` →
     `vol(T) = ENNReal.ofReal |1/2|^n · vol(s)`.
   - Rewrite `Module.finrank ℝ (Fin n → ℝ) = n` (via `Module.finrank_pi`
     + `Fintype.card_fin`).
   - `ENNReal.ofReal (1/2) = (2:ENNReal)⁻¹` via `ofReal_div_of_pos`.
   - Multiplicative cancellation: `(2⁻¹)ⁿ · 2ⁿ = 1` via
     `mul_pow + ENNReal.inv_mul_cancel`, then `ENNReal.mul_lt_mul_left`
     applied to `h_vol : 2ⁿ < vol s` gives `1 < (2⁻¹)ⁿ · vol s = vol(T)`.

**Required setup change**: added `Pointwise` to `open` declaration
(line 42) so that `(2:ℝ)⁻¹ • s` parses as the `Set.SMul` pointwise instance,
needed for `addHaar_smul` to typecheck on the half-scaled set.

### Lean 4.26.0 / Mathlib 4.26.0 API notes for half-scaling proofs

- `Measure.addHaar_smul` lives in `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`
  (transitively imported through `Mathlib.Tactic`); signature:
  `volume (r • s) = ENNReal.ofReal |r| ^ Module.finrank ℝ E * volume s`.
- The `Pointwise` namespace is **scoped** — sets need `open Pointwise` to use
  the SMul instance. Without it, `c • s` doesn't parse for `s : Set α`.
- `Module.finrank_pi : Module.finrank R (ι → R) = Fintype.card ι` is the right
  lemma for `Fin n → ℝ` (combined with `Fintype.card_fin`).
- `ENNReal.mul_lt_mul_left (h : a ≠ 0) (h' : a ≠ ⊤) : a * b < a * c ↔ b < c`
  is the strict-monotonicity lemma; works on (1/2 : ENNReal)ⁿ since this
  value is both nonzero and finite (`pow_ne_zero` + `pow_ne_top`).

---

## Dead Ends

- Tried thinking about a `MeasurableEquiv.smul₀` direct route for sorry 1
  but the preimage-rewrite path is cleaner and reuses existing Erdős-353
  infrastructure.
- Direct `linarith` on ENNReal goals fails (no linarith for ENNReal); had to
  do explicit `ENNReal.mul_lt_mul_left` + rewriting `(2⁻¹)ⁿ · 2ⁿ = 1`.
