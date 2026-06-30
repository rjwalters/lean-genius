/-
  The complex-conjugation route for `f = X⁵ − X − 1`  (abel-ruffini OQ-07)

  ## Context
  The gallery entry `AbelRuffiniOQ07.lean` documents — but only in prose, via
  `prod_two_swaps_mem_alternating` — that the curated route (iii) "f has exactly
  three real roots ⟹ complex conjugation is a transposition" is **inapplicable** to
  `X⁵ − X − 1`, because this polynomial has exactly ONE real root (its four non-real
  roots form two conjugate pairs), so complex conjugation acts as a *double*
  transposition, an even permutation in `A₅`.

  This file makes that correction **quantitative and machine-checked**, by exposing
  the exact arithmetic that controls it.  Mathlib's
  `card_complex_roots_eq_card_real_add_card_not_gal_inv` states, for any `p : ℚ[X]`,

      #{complex roots} = #{real roots} + #support(complex conjugation),

  and for an irreducible *quintic* the complex root set has exactly `5` elements
  (separability over a perfect field + algebraic closure of `ℂ`).  Since a
  transposition is precisely a permutation whose support has cardinality `2`
  (`Equiv.Perm.card_support_eq_two`), complex conjugation is a transposition **iff**
  the support has size `2` **iff** the polynomial has exactly `5 − 2 = 3` real roots.

  ## Main results (0 sorry, 0 axiom)
  * `conj_isSwap_iff_three_real` — for ANY irreducible quintic `p` over `ℚ`, the
    complex-conjugation automorphism acts on the roots as a transposition **iff** `p`
    has exactly three real roots.  This is the reusable mechanism behind Mathlib's
    real-root assembler `galActionHom_bijective_of_prime_degree`; it is not stated in
    pinned Mathlib in this iff form.
  * `f_conj_isSwap_iff_three_real` — the specialization to `f = X⁵ − X − 1`
    (irreducible by Selmer's theorem, degree 5).
  * `f_not_three_real_of_conj_not_isSwap` / `f_conj_not_isSwap_of_not_three_real` —
    the two contrapositive corollaries: the transposition the curated route (iii)
    assumed exists for `f` **if and only if** `f` has three real roots, so the
    documented "exactly one real root" fact is exactly what rules it out.

  All results are fully machine-checked with `0` sorries and `0` axioms
  (`propext`, `Classical.choice`, `Quot.sound` only); no `native_decide`.
-/

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Selmer
import Mathlib.GroupTheory.Perm.Cycle.Type

open Equiv Equiv.Perm Polynomial Polynomial.Gal

-- The `ℚ → ℂ` splitting fact is only a *local* instance in Mathlib's source file, so we
-- re-enable it here to let `restrict p ℂ` / `galActionHom p ℂ` elaborate.
attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

namespace AbelRuffiniOQ07ComplexConj

/-- The complex-conjugation automorphism of a rational polynomial `p`, as a
    permutation of its complex root set (`Polynomial.galActionHom` applied to the
    restriction of `Complex.conjAe`).  This is the element whose support Mathlib's
    `card_complex_roots_eq_card_real_add_card_not_gal_inv` counts. -/
noncomputable def conjPerm (p : ℚ[X]) : Equiv.Perm (p.rootSet ℂ) :=
  galActionHom p ℂ (restrict p ℂ (AlgEquiv.restrictScalars ℚ Complex.conjAe))

/-- **For any irreducible quintic over `ℚ`, complex conjugation acts on the roots as a
    transposition iff the polynomial has exactly three real roots.**

This is the iff form of the mechanism that powers Mathlib's clean real-root assembler
`galActionHom_bijective_of_prime_degree` (which assumes exactly one conjugate pair, i.e.
`#ℂ-roots = #ℝ-roots + 2`).  It is the rigorous, quantitative version of the
"three real roots ⟹ transposition" half of the classical quintic route. -/
theorem conj_isSwap_iff_three_real {p : ℚ[X]} (hirr : Irreducible p)
    (hdeg : p.natDegree = 5) :
    (conjPerm p).IsSwap ↔ (p.rootSet ℝ).toFinset.card = 3 := by
  -- The complex root set of an irreducible (hence separable) quintic has 5 elements.
  have hC : (p.rootSet ℂ).toFinset.card = 5 := by
    rw [Set.toFinset_card,
      card_rootSet_eq_natDegree hirr.separable (IsAlgClosed.splits (p.map (algebraMap ℚ ℂ))),
      hdeg]
  -- Mathlib's real/complex root count split.
  have hsplit := card_complex_roots_eq_card_real_add_card_not_gal_inv p
  rw [hC] at hsplit
  -- A transposition is exactly a permutation with support of size 2.
  rw [conjPerm, ← Equiv.Perm.card_support_eq_two]
  omega

/-! ## Specialization to `f = X⁵ − X − 1` -/

/-- The Selmer quintic `f = X⁵ − X − 1` over `ℚ`. -/
noncomputable def f : ℚ[X] := X ^ 5 - X - 1

/-- `f` has degree 5. -/
@[simp] theorem f_natDegree : f.natDegree = 5 := by
  unfold f; compute_degree!

/-- `f` is irreducible over `ℚ` — Selmer's theorem
    (`Polynomial.X_pow_sub_X_sub_one_irreducible_rat` at `n = 5`). -/
theorem f_irreducible : Irreducible f := by
  unfold f; exact X_pow_sub_X_sub_one_irreducible_rat (n := 5) (by norm_num)

/-- **Specialization to `f = X⁵ − X − 1`.**  Complex conjugation is a transposition of
    the roots of `f` iff `f` has exactly three real roots. -/
theorem f_conj_isSwap_iff_three_real :
    (conjPerm f).IsSwap ↔ (f.rootSet ℝ).toFinset.card = 3 :=
  conj_isSwap_iff_three_real f_irreducible f_natDegree

/-- Contrapositive: if complex conjugation is **not** a transposition of the roots of
    `f`, then `f` does **not** have exactly three real roots.  (For `X⁵ − X − 1` the
    real-root count is in fact `1`, so conjugation is the even double-transposition the
    entry's `prod_two_swaps_mem_alternating` describes.) -/
theorem f_not_three_real_of_conj_not_isSwap (h : ¬ (conjPerm f).IsSwap) :
    (f.rootSet ℝ).toFinset.card ≠ 3 :=
  fun hc => h (f_conj_isSwap_iff_three_real.mpr hc)

/-- Contrapositive, other direction: if `f` does **not** have exactly three real roots,
    then complex conjugation is **not** a transposition — so it cannot be the swap the
    curated route (iii) assumed, and the `S₅` proof must obtain its transposition
    elsewhere (the `p = 2` Frobenius `frob2 ^ 3`). -/
theorem f_conj_not_isSwap_of_not_three_real (h : (f.rootSet ℝ).toFinset.card ≠ 3) :
    ¬ (conjPerm f).IsSwap :=
  fun hs => h (f_conj_isSwap_iff_three_real.mp hs)

end AbelRuffiniOQ07ComplexConj
