/-
Descartes' Rule of Signs — multiplicity-aware conjugate root pairing
(Erdős/algebra research leaf: descartes-rule-oq-01-oq-01, "Extension to Complex Roots")

Source problem: https://erdosproblems.com (Descartes' rule of signs family)
Status: original supporting theory; fully machine-checked.

Context:
The gallery entry `descartes-rule-of-signs-oq-01-oq-01` formalizes the conjugate
root theorem and the *set-level* pairing of non-real roots of a real polynomial,
and proves the abstract parity fact n = r + c with c even. It explicitly lists as
OPEN the question of connecting this to Mathlib's `Polynomial.roots` multiset so
that roots are counted *with multiplicity*. This file answers exactly that.

For p : ℝ[X], write q = p.map (algebraMap ℝ ℂ) for its image in ℂ[X].

Main results:
  * `rootMultiplicity_conj` — z and its conjugate z̄ have the SAME multiplicity
        as roots of q (multiplicity-aware conjugate root theorem). The proof
        applies Mathlib's `eq_rootMultiplicity_map` to the conjugation
        automorphism of ℂ, which fixes q because p has real coefficients.
  * `count_roots_conj` — the same statement phrased via the root multiset:
        q.roots.count z = q.roots.count z̄.
  * `roots_map_conj` — the multiset q.roots is invariant under conjugation.
  * `nonreal_roots_card_even` — the number of non-real roots of q, COUNTED WITH
        MULTIPLICITY, is even (conjugation is a fixed-point-free involution
        swapping the upper and lower half-planes).
  * `realRoots_card_parity` — therefore the number of real roots of p counted
        with multiplicity is congruent to deg p modulo 2. This is the
        multiplicity-aware refinement of the gallery's parity fact, obtained by
        combining the even non-real count with `IsAlgClosed.card_roots_eq_natDegree`.

This refines the earlier set-level pairing to the level of the actual root
multiset, with multiplicities, using only standard Mathlib (no axioms, no sorries).

Tags: descartes-rule, complex-roots, conjugate-pairing, multiplicity, parity, polynomials
-/

import Mathlib

namespace DescartesRuleComplexMult

open Polynomial

/-- The image of a real polynomial inside `ℂ[X]`. -/
noncomputable def toC (p : ℝ[X]) : ℂ[X] := p.map (algebraMap ℝ ℂ)

/-- Complex conjugation is injective (it is its own inverse). -/
theorem conj_injective : Function.Injective (starRingEnd ℂ) :=
  Function.LeftInverse.injective (starRingEnd_self_apply (R := ℂ))

/-- A real polynomial, mapped into `ℂ[X]`, is fixed by conjugating its
coefficients: conjugation fixes the image of every real number. -/
theorem toC_map_conj (p : ℝ[X]) : (toC p).map (starRingEnd ℂ) = toC p := by
  have h : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = algebraMap ℝ ℂ := by
    ext r
    simp [Complex.conj_ofReal]
  simp only [toC, Polynomial.map_map, h]

/-- **Multiplicity-aware conjugate root theorem.**
For a real polynomial viewed over `ℂ`, a complex number `z` and its conjugate
`z̄` are roots of exactly the same multiplicity. -/
theorem rootMultiplicity_conj (p : ℝ[X]) (z : ℂ) :
    (toC p).rootMultiplicity (starRingEnd ℂ z) = (toC p).rootMultiplicity z := by
  have h := Polynomial.eq_rootMultiplicity_map (p := toC p) conj_injective z
  rw [toC_map_conj] at h
  exact h.symm

/-- Conjugate roots occur with equal multiplicity in the root multiset. -/
theorem count_roots_conj (p : ℝ[X]) (z : ℂ) :
    (toC p).roots.count (starRingEnd ℂ z) = (toC p).roots.count z := by
  classical
  rw [count_roots, count_roots, rootMultiplicity_conj]

/-- The root multiset of a real polynomial (over `ℂ`) is invariant under
conjugation. -/
theorem roots_map_conj (p : ℝ[X]) :
    (toC p).roots.map (starRingEnd ℂ) = (toC p).roots := by
  classical
  refine Multiset.ext.mpr (fun w => ?_)
  have h1 : ((toC p).roots.map (starRingEnd ℂ)).count w
      = (toC p).roots.count (starRingEnd ℂ w) := by
    have h := Multiset.count_map_eq_count' (starRingEnd ℂ) (toC p).roots
      conj_injective (starRingEnd ℂ w)
    rwa [starRingEnd_self_apply] at h
  rw [h1]
  exact count_roots_conj p w

/-- Conjugation maps the upper-half-plane roots bijectively onto the
lower-half-plane roots (counted with multiplicity). -/
theorem roots_filter_neg_im (p : ℝ[X]) :
    (toC p).roots.filter (fun z => z.im < 0)
      = ((toC p).roots.filter (fun z => 0 < z.im)).map (starRingEnd ℂ) := by
  classical
  conv_lhs => rw [← roots_map_conj p]
  rw [Multiset.filter_map]
  congr 1
  apply Multiset.filter_congr
  intro z _
  simp [Complex.conj_im]

/-- **The non-real roots come in conjugate pairs**: the number of non-real roots
of a real polynomial, counted with multiplicity, is even. -/
theorem nonreal_roots_card_even (p : ℝ[X]) :
    Even (Multiset.card ((toC p).roots.filter (fun z => z.im ≠ 0))) := by
  classical
  -- count the non-real roots as the sum over the two open half-planes
  have hsplit : Multiset.card ((toC p).roots.filter (fun z => z.im ≠ 0))
      = Multiset.card ((toC p).roots.filter (fun z => 0 < z.im))
        + Multiset.card ((toC p).roots.filter (fun z => z.im < 0)) := by
    rw [← Multiset.card_add]
    congr 1
    refine Multiset.ext.mpr (fun w => ?_)
    rw [Multiset.count_add, Multiset.count_filter, Multiset.count_filter,
      Multiset.count_filter]
    rcases lt_trichotomy w.im 0 with h | h | h
    · rw [if_pos (ne_of_lt h), if_neg (not_lt.mpr h.le), if_pos h, zero_add]
    · simp [h]
    · rw [if_pos (ne_of_gt h), if_pos h, if_neg (not_lt.mpr h.le), add_zero]
  rw [hsplit, roots_filter_neg_im p, Multiset.card_map]
  exact ⟨_, rfl⟩

/-- **Multiplicity-aware Descartes parity.**
The number of real roots of a real polynomial, counted with multiplicity, is
congruent modulo 2 to the degree of the polynomial. This is the refinement, at
the level of the root multiset, of the gallery's set-level parity fact. -/
theorem realRoots_card_parity (p : ℝ[X]) :
    Multiset.card ((toC p).roots.filter (fun z => z.im = 0)) ≡ p.natDegree [MOD 2] := by
  classical
  -- total roots with multiplicity = degree (ℂ is algebraically closed)
  have hcard : Multiset.card (toC p).roots = p.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree]
    exact natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective p
  -- real part + non-real part = all roots
  have hpart : (toC p).roots.filter (fun z => z.im = 0)
      + (toC p).roots.filter (fun z => z.im ≠ 0) = (toC p).roots := by
    simpa using Multiset.filter_add_not (fun z : ℂ => z.im = 0) (toC p).roots
  have hcard2 : Multiset.card ((toC p).roots.filter (fun z => z.im = 0))
      + Multiset.card ((toC p).roots.filter (fun z => z.im ≠ 0)) = p.natDegree := by
    rw [← Multiset.card_add, hpart, hcard]
  obtain ⟨m, hm⟩ := nonreal_roots_card_even p
  -- p.natDegree = realCount + 2*m, so realCount ≡ natDegree mod 2
  refine (Nat.modEq_iff_dvd' ?_).mpr ⟨m, ?_⟩
  · omega
  · omega

end DescartesRuleComplexMult
