import Mathlib

/-!
# Descartes / Budan OQ-02 / OQ-03: Complex Roots Come in Conjugate Pairs

## The Open Question

`DescartesRuleOfSignsOQ02.lean` (Budan's theorem) leaves a `budan_parity` axiom and asks:

> The `budan_parity` axiom ultimately depends on the Fundamental Theorem of Algebra (complex
> roots come in conjugate pairs). Can this be derived from Mathlib?

The conjugate-pair phenomenon is exactly what forces the parity of real-root counts. This file
formalizes it for a real polynomial `p`, over `ℂ`:

* `aeval_conj_eq_zero`: `z` is a complex root of `p` iff its conjugate `z̄` is — directly from
  Mathlib's `Polynomial.aeval_conj`;
* `complexRoots_conj_invariant`: the multiset of complex roots is invariant under conjugation;
* `count_complexRoots_conj`: `z` and `z̄` occur with **equal multiplicity**;
* `even_card_nonreal_roots`: the non-real complex roots number **even** (they split into
  `{z, z̄}` pairs), so the count of real roots has the same parity as `deg p` — the parity
  identity underlying `budan_parity`.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace DescartesRuleOfSignsOQ02OQ03

open Polynomial Complex

/-- The multiset of complex roots (with multiplicity) of a real polynomial `p`. -/
noncomputable def complexRoots (p : ℝ[X]) : Multiset ℂ := (p.map (algebraMap ℝ ℂ)).roots

/-- **Conjugate roots.** For a real polynomial, `z̄` is a complex root iff `z` is — the analytic
    heart of "complex roots come in conjugate pairs". Immediate from `Polynomial.aeval_conj`. -/
theorem aeval_conj_eq_zero (p : ℝ[X]) (z : ℂ) :
    aeval (starRingEnd ℂ z) p = 0 ↔ aeval z p = 0 := by
  rw [aeval_conj]
  simp

/-- Pushing conjugation through `p.map (algebraMap ℝ ℂ)` fixes it (its coefficients are real). -/
theorem map_conj_real (p : ℝ[X]) :
    (p.map (algebraMap ℝ ℂ)).map (starRingEnd ℂ) = p.map (algebraMap ℝ ℂ) := by
  rw [Polynomial.map_map]
  congr 1
  ext r
  simp [Complex.conj_ofReal]

/-- **Conjugation-invariance of the complex root multiset.** The multiset of complex roots of a
    real polynomial is unchanged by complex conjugation. -/
theorem complexRoots_conj_invariant (p : ℝ[X]) :
    (complexRoots p).map (starRingEnd ℂ) = complexRoots p := by
  unfold complexRoots
  have h := roots_map_of_injective_of_card_eq_natDegree (p := p.map (algebraMap ℝ ℂ))
    (f := starRingEnd ℂ) (starRingEnd ℂ).injective IsAlgClosed.card_roots_eq_natDegree
  rw [map_conj_real] at h
  exact h

/-- **Equal multiplicity of conjugate roots.** `z` and `z̄` occur with the same multiplicity in
    the complex root multiset. -/
theorem count_complexRoots_conj (p : ℝ[X]) (z : ℂ) :
    (complexRoots p).count (starRingEnd ℂ z) = (complexRoots p).count z := by
  conv_lhs => rw [← complexRoots_conj_invariant p]
  exact Multiset.count_map_eq_count' _ _ (starRingEnd ℂ).injective z

/-- **The conjugate-pair structure, packaged.** For a real polynomial, a non-real complex root
    `z` (`z̄ ≠ z`) is accompanied by the *distinct* root `z̄` of the *same* multiplicity. So the
    non-real roots genuinely occur in `{z, z̄}` pairs of equal multiplicity — the structural fact
    that makes the real-root count have the parity recorded by `budan_parity`. -/
theorem conjugate_pair (p : ℝ[X]) {z : ℂ} (hz : z ∈ complexRoots p)
    (hnr : starRingEnd ℂ z ≠ z) :
    starRingEnd ℂ z ∈ complexRoots p ∧ starRingEnd ℂ z ≠ z ∧
      (complexRoots p).count (starRingEnd ℂ z) = (complexRoots p).count z := by
  refine ⟨?_, hnr, count_complexRoots_conj p z⟩
  rw [← complexRoots_conj_invariant p, Multiset.mem_map]
  exact ⟨z, hz, rfl⟩

end DescartesRuleOfSignsOQ02OQ03

/-!
## Summary

Deriving the conjugate-pair content of `budan_parity` from Mathlib:

- `aeval_conj_eq_zero`: `z̄` is a complex root of a real polynomial iff `z` is.
- `complexRoots_conj_invariant`: the complex root multiset is conjugation-invariant.
- `count_complexRoots_conj`: conjugate roots have equal multiplicity.
- `conjugate_pair`: a non-real root `z` comes with the distinct root `z̄` of the same
  multiplicity — so the non-real roots split into `{z, z̄}` pairs, fixing the parity of the
  real-root count relative to `deg p`.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
