import Mathlib
import Proofs.GeneralQuartic

/-!
# Axiom discharge for `GeneralQuartic.lean`

`GeneralQuartic.lean` (Wiedijk #46, Ferrari's quartic method) carries exactly
three remaining `axiom` declarations, all of which are *routine, classical*
facts (FTA for a degree-4 polynomial; the quadratic formula for a biquadratic).
This file proves each of them as a `theorem`, so that — once verified under the
Docker build — the `axiom` lines in `GeneralQuartic.lean` can be replaced by
these proofs verbatim, dropping its `axiomCount` from 3 to 0.

This file is intentionally **not** imported by `Proofs.lean`: it is a staging
/ companion file. Keeping it out of the registered build means an in-progress
or mistaken proof here cannot break the gallery build of `Proofs`.

## Targets (mirror the `axiom` statements exactly)

* `quartic_has_four_roots'`  ↔ `GeneralQuartic.quartic_has_four_roots`
* `biquadratic_forward'`     ↔ `GeneralQuartic.biquadratic_forward`
* `biquadratic_backward'`    ↔ `GeneralQuartic.biquadratic_backward`

The math behind all three is independently checked by
`research/problems/solution-of-cubic-oq-03-oq-03-oq-01/verify_quartic_axioms.py`.
-/

open Polynomial Complex

namespace GeneralQuartic

/-- The principal-branch square of the biquadratic discriminant radical:
`s = (p² − 4r)^{1/2}` satisfies `s² = p² − 4r`.

This is the single non-`ring` fact underlying both biquadratic axioms.  It is
**not** provable by `field_simp; ring`; it needs `Complex.cpow_nat_inv_pow`
(`(x ^ (n⁻¹ : ℂ))^n = x` for `n ≠ 0`) after rewriting `1/2` as `(2 : ℕ)⁻¹`. -/
theorem cpow_half_sq (p r : ℂ) :
    (Complex.cpow (p ^ 2 - 4 * r) (1 / 2 : ℂ)) ^ 2 = p ^ 2 - 4 * r := by
  rw [show (1 / 2 : ℂ) = ((2 : ℕ) : ℂ)⁻¹ by norm_num]
  exact_mod_cast Complex.cpow_nat_inv_pow (p ^ 2 - 4 * r) (n := 2) (by norm_num)

/-- **A3 (biquadratic backward), proved.**
If `y²` equals one of the two quadratic-formula solutions of `z² + p z + r = 0`,
then `y` is a root of the biquadratic `y⁴ + p y² + r = 0`.

Substituting `y² = (-p ± s)/2` and using `s² = p² − 4r` reduces the quartic to
`(s² − (p² − 4r))/4 = 0`. -/
theorem biquadratic_backward' (p r y : ℂ)
    (h : (y ^ 2 = (-p + Complex.cpow (p ^ 2 - 4 * r) (1 / 2 : ℂ)) / 2) ∨
         (y ^ 2 = (-p - Complex.cpow (p ^ 2 - 4 * r) (1 / 2 : ℂ)) / 2)) :
    y ^ 4 + p * y ^ 2 + 0 * y + r = 0 := by
  set s := Complex.cpow (p ^ 2 - 4 * r) (1 / 2 : ℂ) with hs_def
  have hs : s ^ 2 = p ^ 2 - 4 * r := cpow_half_sq p r
  rcases h with hz | hz
  · rw [show y ^ 4 = (y ^ 2) ^ 2 from by ring, hz]
    linear_combination (1 / 4 : ℂ) * hs
  · rw [show y ^ 4 = (y ^ 2) ^ 2 from by ring, hz]
    linear_combination (1 / 4 : ℂ) * hs

/-- **A2 (biquadratic forward), proved.**
If `y` is a root of `y⁴ + p y² + r = 0`, then `y²` equals one of the two
quadratic-formula solutions.

Writing `w = y²`, the resolvent `w² + p w + r` factors as `(w − z₁)(w − z₂)`
with `z₁,₂ = (-p ± s)/2` and `s² = p² − 4r`; `ℂ` has no zero divisors. -/
theorem biquadratic_forward' (p r y : ℂ)
    (h : y ^ 4 + p * y ^ 2 + 0 * y + r = 0) :
    (y ^ 2 = (-p + Complex.cpow (p ^ 2 - 4 * r) (1 / 2 : ℂ)) / 2) ∨
    (y ^ 2 = (-p - Complex.cpow (p ^ 2 - 4 * r) (1 / 2 : ℂ)) / 2) := by
  set s := Complex.cpow (p ^ 2 - 4 * r) (1 / 2 : ℂ) with hs_def
  have hs : s ^ 2 = p ^ 2 - 4 * r := cpow_half_sq p r
  have hfac : (y ^ 2 - (-p + s) / 2) * (y ^ 2 - (-p - s) / 2) = 0 := by
    linear_combination h - (1 / 4 : ℂ) * hs
  rcases mul_eq_zero.mp hfac with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (sub_eq_zero.mp h2)

/-- **A1 (quartic has four roots), proved.**
A degree-4 polynomial over `ℂ` has, by the Fundamental Theorem of Algebra, a
root multiset of cardinality 4; naming its four entries `r₁,r₂,r₃,r₄`
(with multiplicity) gives the root characterization.

Route: `compute_degree!` for `natDegree = 4`; `IsAlgClosed.splits` +
`Splits.natDegree_eq_card_roots` for `card roots = 4`; enumerate the length-4
`roots.toList`; convert `eval x = 0 ↔ x ∈ roots` via `Polynomial.mem_roots`. -/
theorem quartic_has_four_roots' (a b c d : ℂ) :
    ∃ (r₁ r₂ r₃ r₄ : ℂ),
      ∀ x : ℂ, (quarticPoly a b c d).eval x = 0 ↔ (x = r₁ ∨ x = r₂ ∨ x = r₃ ∨ x = r₄) := by
  have hdeg : (quarticPoly a b c d).natDegree = 4 := by
    unfold quarticPoly; compute_degree!
  have hp0 : quarticPoly a b c d ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hdeg; exact absurd hdeg (by norm_num)
  have hsplit : (quarticPoly a b c d).Splits := IsAlgClosed.splits _
  have hcard : Multiset.card (quarticPoly a b c d).roots = 4 := by
    have h := hsplit.natDegree_eq_card_roots
    rw [hdeg] at h; exact h.symm
  have hlen : (quarticPoly a b c d).roots.toList.length = 4 := by
    rw [Multiset.length_toList]; exact hcard
  obtain ⟨r₁, r₂, r₃, r₄, hlist⟩ :
      ∃ r₁ r₂ r₃ r₄, (quarticPoly a b c d).roots.toList = [r₁, r₂, r₃, r₄] := by
    rcases ht : (quarticPoly a b c d).roots.toList with
        _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, tl⟩⟩⟩⟩
    · rw [ht] at hlen; simp at hlen
    · rw [ht] at hlen; simp at hlen
    · rw [ht] at hlen; simp at hlen
    · rw [ht] at hlen; simp at hlen
    · cases tl with
      | nil => exact ⟨a1, a2, a3, a4, ht⟩
      | cons a5 tl2 =>
          rw [ht] at hlen
          simp only [List.length_cons, List.length_nil] at hlen
          omega
  refine ⟨r₁, r₂, r₃, r₄, fun x => ?_⟩
  have hmem : x ∈ (quarticPoly a b c d).roots ↔ (x = r₁ ∨ x = r₂ ∨ x = r₃ ∨ x = r₄) := by
    rw [← Multiset.mem_toList, hlist]; simp
  rw [← hmem, Polynomial.mem_roots hp0, Polynomial.IsRoot.def]

end GeneralQuartic
