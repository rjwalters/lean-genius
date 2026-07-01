/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic

/-!
# Metabelian and Metacyclic Groups Are Solvable of Derived Length ≤ 2 (OQ-04·OQ-02·OQ-04·OQ-03)

The parent entry (`AbelRuffiniOQ04OQ02OQ04`) proved that every dihedral group `Dₙ` is
solvable, by exhibiting the concrete short exact sequence

`1 → ⟨rotation⟩ → Dₙ → ℤ/2 → 1`

with abelian kernel and abelian quotient, and invoking `solvable_of_ker_le_range`.

Its open question OQ-03 asks for the **structural generalisation** that this argument
really proves: *any* group built as a cyclic-by-cyclic (more generally abelian-by-abelian)
extension is solvable.  This file settles it, and sharpens "solvable" to the exact
**solvable class**:

> **Metabelian ⟹ derived length ≤ 2.**  If `G` has a normal subgroup `N` with `N` abelian
> and `G ⧸ N` abelian, then `derivedSeries G 2 = ⊥`.

Mathlib's `solvable_of_ker_le_range` only yields *some* trivialising index; the theorem
below pins it at `2` as an explicit subgroup equality — the precise statement that a
metabelian group has solvability class at most `2` (i.e. `[[G,G],[G,G]] = 1`).

## Results

* `comm_of_isCyclic` : a cyclic group is commutative (extracted commutativity, no instance
  side effects for the caller).
* `derivedSeries_two_eq_bot_of_metabelian` : the headline — `derivedSeries G 2 = ⊥` for a
  metabelian group.
* `isSolvable_of_metabelian` : the solvability corollary for abelian-by-abelian extensions.
* `isSolvable_of_metacyclic` : the cyclic-by-cyclic (metacyclic) specialisation answering
  OQ-03 verbatim — `N.Normal`, `IsCyclic N`, `IsCyclic (G ⧸ N)` ⟹ `IsSolvable G`.
* `derivedSeries_two_eq_bot_of_metacyclic` : the metacyclic case as the sharp class-`2`
  bound.  The parent's dihedral groups `Dₙ` and the solvable symmetric groups `S₂,S₃,S₄`
  are all instances of this pattern.

## Method

The commutator subgroup `derivedSeries G 1 = ⁅⊤,⊤⁆` maps to the (trivial) commutator of the
abelian quotient under `mk' N`, so `derivedSeries G 1 ≤ N`; then
`derivedSeries G 2 = ⁅derivedSeries G 1, derivedSeries G 1⁆ ≤ ⁅N,N⁆ = ⊥` because `N` is
abelian.  Cyclic groups are commutative (`IsCyclic.commGroup`), so the metacyclic case is
an immediate corollary.
-/

open Subgroup MonoidHom

namespace AbelRuffiniOQ04OQ02OQ04OQ03

/-! ## Cyclic groups are commutative -/

/-- A cyclic group is commutative.  We extract the bare commutativity statement so callers
avoid introducing a competing `CommGroup` instance. -/
theorem comm_of_isCyclic {H : Type*} [Group H] [IsCyclic H] (a b : H) : a * b = b * a := by
  letI := IsCyclic.commGroup (α := H)
  exact mul_comm a b

/-! ## The derived length of a metabelian group -/

/-- **Metabelian ⟹ derived length ≤ 2.**  If `N ◁ G` is abelian and the quotient `G ⧸ N` is
abelian, then the second derived subgroup of `G` is trivial: `derivedSeries G 2 = ⊥`.  This
is the sharp form of "metabelian groups are solvable of class at most `2`". -/
theorem derivedSeries_two_eq_bot_of_metabelian
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : ∀ a b : G, a ∈ N → b ∈ N → a * b = b * a)
    (hQ : ∀ a b : G ⧸ N, a * b = b * a) :
    derivedSeries G 2 = ⊥ := by
  -- Step 1: the commutator subgroup lands inside `N`, because `G ⧸ N` is abelian.
  have h1 : derivedSeries G 1 ≤ N := by
    rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        map_derivedSeries_eq (QuotientGroup.mk'_surjective N) 1,
        derivedSeries_succ, derivedSeries_zero, commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hQ y x
  -- Step 2: `N` abelian forces the commutator of `N` — hence of anything inside it — trivial.
  have hNN : (⁅N, N⁆ : Subgroup G) = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hN y x hy hx
  rw [derivedSeries_succ]
  exact le_bot_iff.mp (hNN ▸ commutator_mono h1 h1)

/-- **Metabelian ⟹ solvable.**  Abelian-by-abelian extensions are solvable (indeed of class
at most `2`). -/
theorem isSolvable_of_metabelian
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : ∀ a b : G, a ∈ N → b ∈ N → a * b = b * a)
    (hQ : ∀ a b : G ⧸ N, a * b = b * a) :
    IsSolvable G :=
  ⟨⟨2, derivedSeries_two_eq_bot_of_metabelian N hN hQ⟩⟩

/-! ## The metacyclic case (OQ-03) -/

/-- **Metacyclic ⟹ solvable (OQ-03).**  A cyclic-by-cyclic group — one with a cyclic normal
subgroup and cyclic quotient — is solvable.  This is the structural theorem underlying the
parent's dihedral result. -/
theorem isSolvable_of_metacyclic
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [IsCyclic N] [IsCyclic (G ⧸ N)] : IsSolvable G := by
  refine isSolvable_of_metabelian N ?_ ?_
  · intro a b ha hb
    have h := comm_of_isCyclic (H := N) ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg (fun z : N => (z : G)) h
  · intro a b
    exact comm_of_isCyclic a b

/-- The same, packaged as the exact derived-length bound `derivedSeries G 2 = ⊥`. -/
theorem derivedSeries_two_eq_bot_of_metacyclic
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    [IsCyclic N] [IsCyclic (G ⧸ N)] : derivedSeries G 2 = ⊥ := by
  refine derivedSeries_two_eq_bot_of_metabelian N ?_ ?_
  · intro a b ha hb
    have h := comm_of_isCyclic (H := N) ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg (fun z : N => (z : G)) h
  · intro a b
    exact comm_of_isCyclic a b

end AbelRuffiniOQ04OQ02OQ04OQ03
