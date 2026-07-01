/-
Proof: **ℚ(∛3)/ℚ is not a normal (Galois) extension** — the minimal polynomial
`X³ − 3` of ∛3 does not split inside ℚ(∛3), because ℚ(∛3) sits inside ℝ and
`X³ − 3` has only one real root.
Research: cube-root-3-irrational-oq-03-oq-03
Date: 2026-07-01

Open question (child of `cube-root-3-irrational-oq-03`): the parent established
that ∛3 has degree 3 over ℚ with minimal polynomial `X³ − 3`
(`minpoly_cbrt3`, `finrank_adjoin_cbrt3`). A sibling (`…-oq-03-oq-02`) drew the
constructibility corollary. Here we settle the **Galois-theoretic** status of the
extension: it is *not* normal.

## Why this is the natural next question

The degree `[ℚ(∛3) : ℚ] = 3` is *odd*, so ℚ(∛3) cannot be built from ℚ by
quadratic steps (that was the non-constructibility corollary). But degree alone
does not decide normality. The classical fact is that ℚ(∛3)/ℚ is the standard
first example of a **non-normal** finite extension: `X³ − 3` has the one real
root ∛3 in ℚ(∛3) but its two complex conjugate roots `ω∛3, ω²∛3` are missing.
Consequently the splitting field ℚ(∛3, ω) is strictly larger (degree 6), and the
Galois group of the splitting field is `S₃`, not a group acting on ℚ(∛3) alone.

## The proof

`Normal ℚ ℚ⟮cbrt3⟯` would force the minimal polynomial of ∛3, namely `X³ − 3`,
to split *inside* ℚ(∛3) (`Normal.splits`).  Since ℚ(∛3) is an intermediate field
of ℝ, the algebra embedding `ℚ(∛3) ↪ ℝ` (`IntermediateField.val`) transports that
splitting to ℝ (`Polynomial.splits_of_algHom`).  But `X³ − 3` does **not** split
over ℝ:

* if it did, `splits_iff_card_roots` would give it three roots (with
  multiplicity) in ℝ;
* `X³ − 3` is separable over ℝ (`separable_X_pow_sub_C`), so its roots are
  distinct (`nodup_roots`);
* yet every real root `r` satisfies `r³ = 3 = (∛3)³`, and `x ↦ x³` is injective
  on ℝ (`Odd.strictMono_pow`), so `r = ∛3` — there is only **one** real root.

Three distinct roots collapsing to one is the contradiction.
-/

import Mathlib
import Proofs.CubeRoot3IrrationalOQ03

open CubeRoot3Irrational CubeRoot3IrrationalOQ03 Polynomial IntermediateField

namespace CubeRoot3IrrationalOQ03OQ03

/-! ### The real polynomial `X³ − 3` -/

/-- `(X³ − 3 : ℚ[X])` maps to `X³ − 3 : ℝ[X]` under `algebraMap ℚ ℝ`. -/
theorem map_X_cubed_sub_three :
    (X ^ 3 - C 3 : ℚ[X]).map (algebraMap ℚ ℝ) = (X ^ 3 - C 3 : ℝ[X]) := by
  simp

/-- **Uniqueness of the real cube root of 3.** Any real `r` with `r³ = 3`
equals `∛3`, since `x ↦ x³` is injective on ℝ. -/
theorem real_root_eq_cbrt3 {r : ℝ} (hr : r ^ 3 = 3) : r = cbrt3 := by
  have h : r ^ 3 = cbrt3 ^ 3 := by rw [hr, cbrt3_pow_three]
  exact (Odd.strictMono_pow (by norm_num : Odd 3)).injective h

/-- **`X³ − 3` does not split over ℝ.** A splitting would supply three real roots
(counted without multiplicity, by separability), but `X³ − 3` has the single
real root `∛3`. -/
theorem not_splits_real : ¬ (X ^ 3 - C 3 : ℝ[X]).Splits := by
  intro hsplit
  have hdeg : (X ^ 3 - C 3 : ℝ[X]).natDegree = 3 := natDegree_X_pow_sub_C
  -- three roots with multiplicity
  have hcard : (X ^ 3 - C 3 : ℝ[X]).roots.card = 3 := by
    rw [splits_iff_card_roots.mp hsplit, hdeg]
  -- separable ⇒ roots are distinct
  have hsep : (X ^ 3 - C 3 : ℝ[X]).Separable :=
    separable_X_pow_sub_C (3 : ℝ) (by norm_num) (by norm_num)
  have hnodup := nodup_roots hsep
  -- but every root equals ∛3
  have hsub : (X ^ 3 - C 3 : ℝ[X]).roots.toFinset ⊆ {cbrt3} := by
    intro r hr
    rw [Multiset.mem_toFinset, mem_roots'] at hr
    obtain ⟨-, hroot⟩ := hr
    rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C] at hroot
    rw [Finset.mem_singleton]
    exact real_root_eq_cbrt3 (by linarith [hroot])
  have h1 : (X ^ 3 - C 3 : ℝ[X]).roots.toFinset.card ≤ 1 := by
    refine le_trans (Finset.card_le_card hsub) ?_
    simp
  rw [Multiset.toFinset_card_of_nodup hnodup, hcard] at h1
  omega

/-! ### The obstruction and the headline non-normality result -/

/-- **The minimal polynomial of ∛3 does not split in ℚ(∛3).** This is the direct
obstruction to normality: the two complex conjugate roots of `X³ − 3` lie outside
the real field ℚ(∛3). -/
theorem minpoly_not_splits_adjoin :
    ¬ ((X ^ 3 - C 3 : ℚ[X]).map (algebraMap ℚ ℚ⟮cbrt3⟯)).Splits := by
  intro h
  have hR : ((X ^ 3 - C 3 : ℚ[X]).map (algebraMap ℚ ℝ)).Splits :=
    splits_of_algHom h (IntermediateField.val ℚ⟮cbrt3⟯)
  rw [map_X_cubed_sub_three] at hR
  exact not_splits_real hR

/-- **ℚ(∛3)/ℚ is not a normal extension.** The classical first example of a
finite, non-normal field extension. -/
theorem not_normal_adjoin_cbrt3 : ¬ Normal ℚ ℚ⟮cbrt3⟯ := by
  intro hnormal
  have hsplitK : ((minpoly ℚ (AdjoinSimple.gen ℚ cbrt3)).map
      (algebraMap ℚ ℚ⟮cbrt3⟯)).Splits := hnormal.splits (AdjoinSimple.gen ℚ cbrt3)
  rw [minpoly_gen, minpoly_cbrt3] at hsplitK
  exact minpoly_not_splits_adjoin hsplitK

/-- **ℚ(∛3)/ℚ is not a Galois extension**, since Galois extensions are normal. -/
theorem not_isGalois_adjoin_cbrt3 : ¬ IsGalois ℚ ℚ⟮cbrt3⟯ := by
  intro h
  exact not_normal_adjoin_cbrt3 (IsGalois.to_normal)

end CubeRoot3IrrationalOQ03OQ03
