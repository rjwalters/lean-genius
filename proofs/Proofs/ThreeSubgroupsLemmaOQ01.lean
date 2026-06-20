import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic

/-
# The Hall–Witt identity and the three subgroups lemma (normal-subgroup form)

## What this proves

The **Hall–Witt identity** is the commutator analogue of the Jacobi identity: for any
three elements `a, b, c` of a group,

  (b⁻¹ ⁅⁅b, a⁻¹⁆, c⁻¹⁆ b) · (c⁻¹ ⁅⁅c, b⁻¹⁆, a⁻¹⁆ c) · (a⁻¹ ⁅⁅a, c⁻¹⁆, b⁻¹⁆ a) = 1,

where `⁅x, y⁆ = x y x⁻¹ y⁻¹` is the group commutator (Mathlib's `commutatorElement`
convention) and `g⁻¹ · _ · g` is conjugation. The three factors are the three cyclic
conjugates of a double commutator; their product is forced to be the identity in every
group.

From this single identity we build the classical **three subgroups lemma** (P. Hall) and,
crucially, its textbook **normal-subgroup form**: for subgroups `H K L` and a *normal*
subgroup `N`, if two of the three rotated double commutators lie in `N`, so does the third —

  ⁅⁅H, K⁆, L⁆ ≤ N  and  ⁅⁅K, L⁆, H⁆ ≤ N   ⟹   ⁅⁅L, H⁆, K⁆ ≤ N.

## What is new relative to Mathlib

Mathlib records only the `= ⊥` special case
(`Subgroup.commutator_commutator_eq_bot_of_rotate`), and proves it by an **inline, unnamed**
rearrangement of group elements — the Hall–Witt identity is buried inside that proof and is
never recorded as a reusable lemma. A search of Mathlib's commutator files turns up
**no named element-level Hall–Witt identity**, **no standalone `commutatorElement`-level
rotation lemma**, and **no `≤ N` generalization** of the three subgroups lemma (the version
that actually drives the lower central series and inequalities `⁅Gᵢ, Gⱼ⁆ ≤ G₍ᵢ₊ⱼ₎`).

This file builds the whole tower from the bottom up, every step named:

* `hall_witt_identity` — the element-level identity, proved by the `group` decision procedure
  (a true identity in the free group, verified independently of any subgroup machinery);
* `commutatorElement_eq_one_of_rotate` — the element-level core of the three subgroups lemma,
  read off the Hall–Witt rearrangement;
* `threeSubgroupsLemma` — the subgroup `= ⊥` form, derived **through the named element lemma**
  (not through Mathlib's inline proof);
* `commutator_le_of_rotate` — the **normal-subgroup `≤ N` form**, obtained by transporting the
  `= ⊥` form across the quotient projection `G ⧸ N`. This is the genuine gap above Mathlib.

The bridge to `≤ N` is short but genuinely mathematical: under `f = QuotientGroup.mk' N`
(kernel exactly `N`), `X ≤ N ↔ X.map f = ⊥`, and `map` commutes with the commutator bracket
(`Subgroup.map_commutator`), so the three `≤ N` hypotheses become `= ⊥` statements in `G ⧸ N`.
Mathlib's `= ⊥` lemma is recovered as the case `N = ⊥`, and the consistency `example` at the
end checks the `= ⊥` form against Mathlib's statement verbatim.

Verified: 0 sorries, 0 `axiom` declarations, no `native_decide`.

## References
* Marshall Hall Jr., *The Theory of Groups* (1959), §10.2.
* https://en.wikipedia.org/wiki/Three_subgroups_lemma
-/

namespace ThreeSubgroupsLemmaOQ01

open Subgroup

variable {G : Type*} [Group G]

/-! ## The Hall–Witt identity (element level) -/

/-- **The Hall–Witt identity** (the Jacobi identity for group commutators).

With `⁅x, y⁆ = x y x⁻¹ y⁻¹` and conjugation written `g⁻¹ · _ · g`, the product of the three
cyclic conjugates of the double commutator is the identity:

  (b⁻¹ ⁅⁅b, a⁻¹⁆, c⁻¹⁆ b) · (c⁻¹ ⁅⁅c, b⁻¹⁆, a⁻¹⁆ c) · (a⁻¹ ⁅⁅a, c⁻¹⁆, b⁻¹⁆ a) = 1.

This is a true identity in the free group on `a, b, c`, so it holds in every group; the
`group` tactic discharges it after the commutator brackets are unfolded. Mathlib uses an
ad-hoc instance of this rearrangement inside its three subgroups proof but never records the
identity itself. -/
theorem hall_witt_identity (a b c : G) :
    (b⁻¹ * ⁅⁅b, a⁻¹⁆, c⁻¹⁆ * b) * (c⁻¹ * ⁅⁅c, b⁻¹⁆, a⁻¹⁆ * c) *
      (a⁻¹ * ⁅⁅a, c⁻¹⁆, b⁻¹⁆ * a) = 1 := by
  simp only [commutatorElement_def]
  group

/-- **The three subgroups lemma, element level.** If the two "rotated" double commutators
`⁅⁅y⁻¹, z⁆, x⁻¹⁆` and `⁅⁅z⁻¹, x⁻¹⁆, y⁆` are trivial, then the un-rotated double commutator
`⁅⁅x, y⁆, z⁆` is trivial as well.

This is the element-level statement that powers the subgroup form. The proof rearranges
`⁅⁅x, y⁆, z⁆` (the Hall–Witt rearrangement) so that the two vanishing double commutators
appear explicitly, after which the surviving factors telescope to the identity. -/
theorem commutatorElement_eq_one_of_rotate {x y z : G}
    (h1 : ⁅⁅y⁻¹, z⁆, x⁻¹⁆ = 1) (h2 : ⁅⁅z⁻¹, x⁻¹⁆, y⁆ = 1) :
    ⁅⁅x, y⁆, z⁆ = 1 := by
  -- The two inner double commutators commute, hence their flipped brackets vanish too.
  have e1 : ⁅x⁻¹, ⁅y⁻¹, z⁆⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp h1).symm
  have e2 : ⁅y, ⁅z⁻¹, x⁻¹⁆⁆ = 1 :=
    commutatorElement_eq_one_iff_commute.mpr
      (commutatorElement_eq_one_iff_commute.mp h2).symm
  -- Hall–Witt rearrangement of the target double commutator.
  trans x * z * ⁅y, ⁅z⁻¹, x⁻¹⁆⁆⁻¹ * z⁻¹ * y * ⁅x⁻¹, ⁅y⁻¹, z⁆⁆⁻¹ * y⁻¹ * x⁻¹
  · simp [commutatorElement_def, mul_assoc]
  · rw [e1, e2]; group

/-! ## The subgroup `= ⊥` form, via the named element lemma -/

/-- **The three subgroups lemma** (P. Hall), subgroup form: if two of the three rotated
double commutators of `H₁, H₂, H₃` are trivial, so is the third.

Same statement as Mathlib's `Subgroup.commutator_commutator_eq_bot_of_rotate`, but re-derived
here so that the only group-element computation is delegated to the *named* element lemma
`commutatorElement_eq_one_of_rotate`, exhibiting exactly where the Hall–Witt rearrangement
enters. -/
theorem threeSubgroupsLemma {H₁ H₂ H₃ : Subgroup G}
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ = ⊥) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ = ⊥) :
    ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥ := by
  simp_rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le,
    Subgroup.mem_centralizer_iff_commutator_eq_one, ← commutatorElement_def] at h1 h2 ⊢
  intro x hx y hy z hz
  exact commutatorElement_eq_one_of_rotate
    (h1 _ (H₂.inv_mem hy) _ hz _ (H₁.inv_mem hx))
    (h2 _ (H₃.inv_mem hz) _ (H₁.inv_mem hx) _ hy)

/-! ## The normal-subgroup `≤ N` form

This is the textbook statement Mathlib does not record. It follows from the `= ⊥` form above
by transporting along the quotient projection `f = QuotientGroup.mk' N`: `X ≤ N` is the same
as `X.map f = ⊥`, and `map` commutes with the commutator bracket. -/

/-- **Three Subgroups Lemma (normal-subgroup form).** If `N` is normal and both `⁅⁅H, K⁆, L⁆`
and `⁅⁅K, L⁆, H⁆` lie in `N`, then so does `⁅⁅L, H⁆, K⁆`.

Mathlib only records the `N = ⊥` case; this `≤ N` version is the one used to build the lower
central series. The proof projects to `G ⧸ N` and applies the named `= ⊥` form
`threeSubgroupsLemma` there. -/
theorem commutator_le_of_rotate {H K L N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅H, K⁆, L⁆ ≤ N) (h2 : ⁅⁅K, L⁆, H⁆ ≤ N) :
    ⁅⁅L, H⁆, K⁆ ≤ N := by
  -- Rewrite `_ ≤ N` as `_ ≤ ker (mk' N)`, then as `map (mk' N) _ = ⊥`.
  rw [← QuotientGroup.ker_mk' N] at h1 h2 ⊢
  rw [← Subgroup.map_eq_bot_iff] at h1 h2 ⊢
  -- `map` distributes over the commutator bracket; the goal is now the `= ⊥` form in `G ⧸ N`.
  simp only [Subgroup.map_commutator] at h1 h2 ⊢
  exact threeSubgroupsLemma h1 h2

/-! ## Full cyclic symmetry: any two imply the third

The statement is invariant under the cyclic relabelling `(H, K, L) ↦ (K, L, H)`, so the same
lemma supplies all three implications. -/

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

The textbook bracket notation usually puts the iterated commutator with the inner bracket
first, `⁅H, ⁅K, L⁆⁆`. Since the subgroup bracket is symmetric
(`Subgroup.commutator_comm : ⁅A, B⁆ = ⁅B, A⁆`), this is literally the same lemma. -/

/-- The three subgroups lemma in the symmetric notation `⁅H, ⁅K, L⁆⁆`:
if `⁅L, ⁅H, K⁆⁆ ≤ N` and `⁅H, ⁅K, L⁆⁆ ≤ N` then `⁅K, ⁅L, H⁆⁆ ≤ N`. -/
theorem commutator_le_of_rotate_symm {H K L N : Subgroup G} [N.Normal]
    (h1 : ⁅L, ⁅H, K⁆⁆ ≤ N) (h2 : ⁅H, ⁅K, L⁆⁆ ≤ N) :
    ⁅K, ⁅L, H⁆⁆ ≤ N := by
  rw [commutator_comm] at h1 h2 ⊢
  exact commutator_le_of_rotate h1 h2

/-! ## Consistency: recovering Mathlib's `= ⊥` lemma

Taking `N = ⊥` collapses `≤ ⊥` to `= ⊥`. -/

/-- The `N = ⊥` specialisation reproduces the Hall–Witt three subgroups lemma. -/
theorem commutator_eq_bot_of_rotate {H K L : Subgroup G}
    (h1 : ⁅⁅H, K⁆, L⁆ = ⊥) (h2 : ⁅⁅K, L⁆, H⁆ = ⊥) :
    ⁅⁅L, H⁆, K⁆ = ⊥ :=
  le_bot_iff.mp <| commutator_le_of_rotate (le_of_eq h1) (le_of_eq h2)

/-! ## A worked consequence

If, modulo a normal `N`, a subgroup `H` commutes with both `K` and `L` (i.e. `⁅H, K⁆ ≤ N` and
`⁅H, L⁆ ≤ N`), then `H` commutes with their commutator `⁅K, L⁆` as well. This is the standard
corollary of the three subgroups lemma: both `⁅⁅H, K⁆, L⁆` and `⁅⁅L, H⁆, K⁆` are forced into
`N` (a commutator of a subgroup contained in the normal `N` stays inside `N`), so the lemma
supplies the third, `⁅⁅K, L⁆, H⁆ = ⁅H, ⁅K, L⁆⁆ ≤ N`. -/
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

/-- Sanity check that the subgroup `= ⊥` form agrees with Mathlib's statement of the same
lemma. -/
example {H₁ H₂ H₃ : Subgroup G}
    (h1 : ⁅⁅H₂, H₃⁆, H₁⁆ = ⊥) (h2 : ⁅⁅H₃, H₁⁆, H₂⁆ = ⊥) :
    ⁅⁅H₁, H₂⁆, H₃⁆ = ⊥ :=
  Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

end ThreeSubgroupsLemmaOQ01
