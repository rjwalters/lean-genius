import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-
# N-Dimensional Mass-Point Ceva: Generalization of OQ-04 to Arbitrary Simplices

## Research Question (cevas-theorem-oq-04-oq-01)

Can the mass-point structure of `CevasTheoremOQ04.lean` (triangle, 3 vertices)
be generalized to an n-dimensional simplex (n+1 vertices)?

## S2 SCAFFOLD (this file)

This file lifts the parent's `MassPointCeva.MassPoint` structure
(positive masses at the 3 vertices of a triangle) to an arbitrary
`Fin (n+1)`-indexed family.  The n-dim "Ceva ratios" are the
complement-fraction quantities

  ratio i = (Σ_{j ≠ i} mass j) / (Σ_j mass j)
          = 1 - mass i / total

and the headline identity is the **dimensional Ceva identity**

  Σ_i ratio i = n     (for `MassPoint n`, with n+1 vertices)

which generalises the triangle "complement fractions sum to 2" identity.

This is a pure real-arithmetic shadow of Mathlib's geometric n-dim Ceva
theorem (`AffineIndependent.exists_affineCombination_eq_smul_eq_of_fintype`
in `Mathlib.LinearAlgebra.AffineSpace.Ceva`, Joseph Myers 2025), in the
same style as the parent file `CevasTheoremOQ04.lean` which is itself
a real-arithmetic shadow of the triangle Ceva theorem.

## What this file does

* `NDimMassPoint.MassPoint n` — n+1 positive real masses
* `MassPoint.total`, `total_pos` — sum is positive
* `MassPoint.ratio` — complement-mass fraction at each vertex
* `ratio_pos` (for n ≥ 1), `ratio_lt_one` — each ratio is in (0, 1)
* `ratio_eq_one_sub` — equivalent form `ratio i = 1 - mass i / total`
* `sum_ratio_eq` — the headline identity `∑ ratio i = n`
* `sum_mass_div_total` — auxiliary: `∑ mass i / total = 1`
* `uniform` example — uniform masses (centroid case), `ratio i = n/(n+1)`

## What this file does NOT do (deferred to S3+)

* `AffineSpace`/`AffineCombination` integration (the geometric concurrency
  statement requires `AffineIndependent` and `affineCombination`; see
  S2-A target in `research/problems/cevas-theorem-oq-04-oq-01/sessions/`).
* Triangle bridge to `MassPointCeva.MassPoint` (parent uses 2-vertex
  edge-split parameters `rD = mC/(mB+mC)`; n-dim "complement fractions"
  are a different but compatible generalisation).
* Constructive existence (mass-from-ratios n-dim analogue of
  `masses_from_ceva`).

## References

* Parent: `proofs/Proofs/CevasTheoremOQ04.lean` (242 LOC, 0 sorries, 0 axioms)
* Mathlib: `Mathlib.LinearAlgebra.AffineSpace.Ceva` (Joseph Myers 2025)
* Session log:
  `research/problems/cevas-theorem-oq-04-oq-01/sessions/2026-05-12-s01-observe-mathlib-affineCombination-bridge.md`
-/

namespace NDimMassPoint

/-- An n-dim mass-point assignment: positive real masses at the n+1
    vertices of an n-simplex (indexed by `Fin (n+1)`). -/
structure MassPoint (n : ℕ) where
  mass : Fin (n + 1) → ℝ
  pos  : ∀ i, 0 < mass i

variable {n : ℕ} (mp : MassPoint n)

/-- The total mass: sum of all `n+1` vertex masses. -/
noncomputable def MassPoint.total : ℝ := ∑ i, mp.mass i

lemma MassPoint.total_pos : 0 < mp.total := by
  unfold MassPoint.total
  exact Finset.sum_pos (fun i _ => mp.pos i) Finset.univ_nonempty

lemma MassPoint.total_ne_zero : mp.total ≠ 0 := mp.total_pos.ne'

/-- The complement-mass fraction at vertex `i`:
    `(Σ_{j ≠ i} mass j) / total = 1 - mass i / total`.

    For `n = 2` (triangle, 3 vertices), this gives the per-vertex
    quantity `ratio i = (sum of two other masses) / (total of three)`.
    These satisfy `Σᵢ ratio i = 2` (the n-dim Ceva identity at `n=2`). -/
noncomputable def MassPoint.ratio (i : Fin (n + 1)) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, mp.mass j) / mp.total

lemma MassPoint.sum_erase_eq_total_sub (i : Fin (n + 1)) :
    (∑ j ∈ Finset.univ.erase i, mp.mass j) = mp.total - mp.mass i := by
  unfold MassPoint.total
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]

/-- The complement-mass fraction equals `1 - mass i / total`. -/
lemma MassPoint.ratio_eq_one_sub (i : Fin (n + 1)) :
    mp.ratio i = 1 - mp.mass i / mp.total := by
  unfold MassPoint.ratio
  rw [mp.sum_erase_eq_total_sub i, sub_div, div_self mp.total_ne_zero]

/-- Each complement-fraction is strictly less than 1
    (regardless of n; the only requirement is that `mass i > 0`). -/
lemma MassPoint.ratio_lt_one (i : Fin (n + 1)) : mp.ratio i < 1 := by
  rw [mp.ratio_eq_one_sub]
  have h : 0 < mp.mass i / mp.total := div_pos (mp.pos i) mp.total_pos
  linarith

/-- For `n ≥ 1` (i.e. at least 2 vertices), the complement-fraction is
    strictly positive.  At `n = 0` (a single vertex) the erased sum is
    empty and the fraction is `0`. -/
lemma MassPoint.ratio_pos (i : Fin (n + 1)) (hn : 0 < n) : 0 < mp.ratio i := by
  unfold MassPoint.ratio
  refine div_pos ?_ mp.total_pos
  refine Finset.sum_pos (fun j _ => mp.pos j) ?_
  rw [← Finset.card_pos,
      Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_univ, Fintype.card_fin]
  omega

/-- Auxiliary: the mass fractions `mass i / total` sum to one. -/
lemma MassPoint.sum_mass_div_total : (∑ i, mp.mass i / mp.total) = 1 := by
  rw [← Finset.sum_div]
  exact div_self mp.total_ne_zero

/-- **N-dim Mass-Point Ceva Identity**: the complement fractions sum to `n`.

    For a triangle (n = 2), this is the identity
      ratio 0 + ratio 1 + ratio 2 = 2
    (each ratio is one minus a normalised vertex mass; three terms each
    summing complementary masses, total mass appears n+1 - 1 = n times).

    This is the n-dim analogue of the parent file's identity that follows
    from `rD + rE + rF` in the triangle case being constrained by the
    Ceva condition. -/
theorem MassPoint.sum_ratio_eq : (∑ i, mp.ratio i) = (n : ℝ) := by
  calc (∑ i, mp.ratio i)
      = ∑ i, (1 - mp.mass i / mp.total) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact mp.ratio_eq_one_sub i
    _ = (∑ _i : Fin (n + 1), (1 : ℝ)) - ∑ i, mp.mass i / mp.total := by
        rw [Finset.sum_sub_distrib]
    _ = (n + 1 : ℝ) - 1 := by
        rw [mp.sum_mass_div_total]
        simp
    _ = (n : ℝ) := by ring

/- ## Specialisation to n = 2 (triangle): scope verification -/

/-- For an `NDimMassPoint.MassPoint 2` (triangle), the complement
    fractions sum to 2.  The parent file `CevasTheoremOQ04.lean` uses
    the 2-vertex edge-split parameters `rD = mC/(mB+mC)` rather than
    these complement fractions, so the two notions are different
    normalisations of the same mass data.  A direct semantic bridge
    requires defining the parent's `rD/rE/rF` in terms of pairwise mass
    ratios on edges, which is deferred to S3. -/
example (mp : MassPoint 2) :
    mp.ratio 0 + mp.ratio 1 + mp.ratio 2 = 2 := by
  have h := mp.sum_ratio_eq
  rw [Fin.sum_univ_three] at h
  exact_mod_cast h

/- ## Concrete example: uniform masses (centroid of n-simplex) -/

/-- The uniform mass assignment (all masses equal to 1) on an n-simplex. -/
noncomputable def uniform (n : ℕ) : MassPoint n where
  mass := fun _ => 1
  pos  := fun _ => one_pos

lemma uniform_total (n : ℕ) : (uniform n).total = (n + 1 : ℝ) := by
  unfold MassPoint.total uniform
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

lemma uniform_ratio (n : ℕ) (i : Fin (n + 1)) :
    (uniform n).ratio i = (n : ℝ) / (n + 1) := by
  rw [MassPoint.ratio_eq_one_sub, uniform_total]
  show 1 - (1 : ℝ) / (n + 1) = (n : ℝ) / (n + 1)
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end NDimMassPoint

/-
## Summary

* Defined `NDimMassPoint.MassPoint n` for n+1 positive vertex masses
* Defined `ratio i = (Σ_{j ≠ i} mass j) / total`
* Proved: `ratio i ∈ (0, 1)` (positivity needs `n ≥ 1`; upper bound unconditional)
* Proved: `∑ ratio i = n` (the n-dim Ceva sum identity)
* Verified: uniform masses give `ratio i = n / (n+1)` (centroid)
* Verified at `n = 2`: `ratio 0 + ratio 1 + ratio 2 = 2`

**Sorry count**: 0
**Axiom count**: 0
**Theorem count**: ~10 (incl. auxiliary lemmas)
**Definition count**: 4 (`MassPoint`, `total`, `ratio`, `uniform`)

## Next iteration (S3) candidates

1. **Triangle bridge**: rewrite `MassPointCeva.MassPoint` (parent) in
   terms of `NDimMassPoint.MassPoint 2`, establishing the bookkeeping
   bijection (different edge-split parameters but same underlying data).
2. **Constructive existence**: lift `masses_from_ceva` (parent's
   converse) to n dimensions — given a ratio profile satisfying
   `Σ r i = n` and `r i ∈ (0, 1)`, construct explicit masses.
3. **Geometric concurrency**: import `Mathlib.LinearAlgebra.AffineSpace.Ceva`
   and connect to the n-dim cevian concurrency theorem
   (`AffineIndependent.exists_affineCombination_eq_smul_eq_of_fintype`).
-/
