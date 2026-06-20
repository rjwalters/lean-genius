import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

/-
# The Three Subgroups Lemma, normal-subgroup form

## What This Proves

For subgroups `H K L N` of a group `G` with `N` **normal**, the *three subgroups lemma*
states that the three iterated commutators

  ⁅⁅H, K⁆, L⁆ ,  ⁅⁅K, L⁆, H⁆ ,  ⁅⁅L, H⁆, K⁆

are cyclically interchangeable modulo `N`: if any two of them are contained in `N`,
so is the third.  The headline statement is

  ⁅⁅H, K⁆, L⁆ ≤ N  →  ⁅⁅K, L⁆, H⁆ ≤ N  →  ⁅⁅L, H⁆, K⁆ ≤ N.

## What Mathlib has — and what this adds

Mathlib proves the **`= ⊥` special case** in `Mathlib/GroupTheory/Commutator/Basic.lean`:

  `Subgroup.commutator_commutator_eq_bot_of_rotate`
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ = ⊥) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ = ⊥) : ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥

obtained from the Hall–Witt identity.  It does **not** record the classical
textbook statement relative to an arbitrary normal subgroup `N` (the version that
actually gets used to build the lower central series and prove `⁅Gᵢ, Gⱼ⁆ ≤ G₍ᵢ₊ⱼ₎`).
A search of Mathlib's commutator files turns up only the `= ⊥` form and no
`≤ N` generalization.

The bridge is short but genuinely mathematical: pass to the quotient `G ⧸ N`.
Under the projection `f = QuotientGroup.mk' N` (whose kernel is exactly `N`),
`X ≤ N` is equivalent to `X.map f = ⊥`, and `map` commutes with the commutator
bracket (`Subgroup.map_commutator`).  So the three `≤ N` hypotheses become three
`= ⊥` statements in `G ⧸ N`, where Mathlib's lemma applies verbatim, and the
conclusion pulls back along `f`.  The `= ⊥` lemma is recovered as the case `N = ⊥`.

Verified: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace ThreeSubgroupsLemmaOQ01

open Subgroup

variable {G : Type*} [Group G]

/-! ## The normal-subgroup three subgroups lemma -/

/-- **Three Subgroups Lemma (normal-subgroup form).**  If `N` is normal and both
`⁅⁅H, K⁆, L⁆` and `⁅⁅K, L⁆, H⁆` lie in `N`, then so does `⁅⁅L, H⁆, K⁆`.

This is the classical `≤ N` statement; Mathlib only records the `N = ⊥` case
(`Subgroup.commutator_commutator_eq_bot_of_rotate`).  The proof projects to
`G ⧸ N` and applies that lemma there. -/
theorem commutator_le_of_rotate {H K L N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅H, K⁆, L⁆ ≤ N) (h2 : ⁅⁅K, L⁆, H⁆ ≤ N) :
    ⁅⁅L, H⁆, K⁆ ≤ N := by
  -- Rewrite `_ ≤ N` as `_ ≤ ker (mk' N)`, then as `map (mk' N) _ = ⊥`.
  rw [← QuotientGroup.ker_mk' N] at h1 h2 ⊢
  rw [← Subgroup.map_eq_bot_iff] at h1 h2 ⊢
  -- `map` distributes over the commutator bracket.
  simp only [Subgroup.map_commutator] at h1 h2 ⊢
  -- Mathlib's `= ⊥` three subgroups lemma, now in `G ⧸ N`.
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

/-! ## Full cyclic symmetry: any two imply the third

The statement is invariant under the cyclic relabelling `(H, K, L) ↦ (K, L, H)`,
so the same lemma supplies all three implications. -/

/-- From `⁅⁅K, L⁆, H⁆ ≤ N` and `⁅⁅L, H⁆, K⁆ ≤ N` conclude `⁅⁅H, K⁆, L⁆ ≤ N`. -/
theorem commutator_le_of_rotate₂ {H K L N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅K, L⁆, H⁆ ≤ N) (h2 : ⁅⁅L, H⁆, K⁆ ≤ N) :
    ⁅⁅H, K⁆, L⁆ ≤ N :=
  commutator_le_of_rotate h1 h2

/-- From `⁅⁅L, H⁆, K⁆ ≤ N` and `⁅⁅H, K⁆, L⁆ ≤ N` conclude `⁅⁅K, L⁆, H⁆ ≤ N`. -/
theorem commutator_le_of_rotate₃ {H K L N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅L, H⁆, K⁆ ≤ N) (h2 : ⁅⁅H, K⁆, L⁆ ≤ N) :
    ⁅⁅K, L⁆, H⁆ ≤ N :=
  commutator_le_of_rotate h1 h2

/-! ## Inner-commutator-first formulation

The textbook bracket notation usually puts the iterated commutator with the inner
bracket first, `⁅H, ⁅K, L⁆⁆`.  Since the bracket is symmetric on subgroups
(`Subgroup.commutator_comm : ⁅A, B⁆ = ⁅B, A⁆`), this is literally the same lemma. -/

/-- The three subgroups lemma in the symmetric notation `⁅H, ⁅K, L⁆⁆`:
if `⁅L, ⁅H, K⁆⁆ ≤ N` and `⁅H, ⁅K, L⁆⁆ ≤ N` then `⁅K, ⁅L, H⁆⁆ ≤ N`. -/
theorem commutator_le_of_rotate_symm {H K L N : Subgroup G} [N.Normal]
    (h1 : ⁅L, ⁅H, K⁆⁆ ≤ N) (h2 : ⁅H, ⁅K, L⁆⁆ ≤ N) :
    ⁅K, ⁅L, H⁆⁆ ≤ N := by
  rw [commutator_comm] at h1 h2 ⊢
  exact commutator_le_of_rotate h1 h2

/-! ## Consistency: recovering Mathlib's `= ⊥` lemma

Taking `N = ⊥` collapses `≤ ⊥` to `= ⊥`, recovering
`Subgroup.commutator_commutator_eq_bot_of_rotate`. -/

/-- The `N = ⊥` specialisation reproduces Mathlib's Hall–Witt three subgroups lemma. -/
theorem commutator_eq_bot_of_rotate {H K L : Subgroup G}
    (h1 : ⁅⁅H, K⁆, L⁆ = ⊥) (h2 : ⁅⁅K, L⁆, H⁆ = ⊥) :
    ⁅⁅L, H⁆, K⁆ = ⊥ :=
  le_bot_iff.mp <| commutator_le_of_rotate (le_of_eq h1) (le_of_eq h2)

/-! ## A worked consequence

If, modulo a normal `N`, a subgroup `H` commutes with both `K` and `L`
(i.e. `⁅H, K⁆ ≤ N` and `⁅H, L⁆ ≤ N`), then `H` commutes with their commutator
`⁅K, L⁆` as well.  This is the standard corollary of the three subgroups lemma:
both `⁅⁅H, K⁆, L⁆` and `⁅⁅L, H⁆, K⁆` are forced into `N` (a commutator of a
subgroup contained in the normal `N` stays inside `N`), so the lemma supplies the
third, `⁅⁅K, L⁆, H⁆ = ⁅H, ⁅K, L⁆⁆ ≤ N`. -/
theorem commutator_commutator_le_of_both {H K L N : Subgroup G} [N.Normal]
    (hK : ⁅H, K⁆ ≤ N) (hL : ⁅H, L⁆ ≤ N) :
    ⁅H, ⁅K, L⁆⁆ ≤ N := by
  have hLH : ⁅L, H⁆ ≤ N := by rw [commutator_comm]; exact hL
  -- Goal `⁅H, ⁅K, L⁆⁆ ≤ N` becomes `⁅⁅K, L⁆, H⁆ ≤ N`.
  rw [commutator_comm]
  refine commutator_le_of_rotate₃ ?_ ?_
  · -- ⁅⁅L, H⁆, K⁆ ≤ ⁅N, K⁆ ≤ N
    exact (commutator_mono hLH le_rfl).trans (commutator_le_left N K)
  · -- ⁅⁅H, K⁆, L⁆ ≤ ⁅N, L⁆ ≤ N
    exact (commutator_mono hK le_rfl).trans (commutator_le_left N L)

end ThreeSubgroupsLemmaOQ01
