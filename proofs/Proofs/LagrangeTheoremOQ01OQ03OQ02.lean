import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Order.Minimal
import Mathlib.Tactic

/-
# Minimal normal subgroups: existence and abelianness in the solvable case (0 axioms)

## Open Question (continuation of lagrange-theorem-oq-01-oq-03, OQ-01)

The sibling file `LagrangeTheoremOQ01OQ03OQ01.lean` proved the Schur–Zassenhaus
*lifting step* of Hall's theorem with 0 axioms, and pinpointed the remaining gap:
a 0-axiom proof of Hall's theorem for solvable groups needs the **minimal normal
subgroup** machinery, which Mathlib 4.26 lacks:

* existence of a *minimal* normal subgroup of a nontrivial finite group, and
* the fact that in a *solvable* group such a subgroup is abelian (indeed
  elementary abelian).

This file supplies the first two of those facts, **with 0 axioms**.

## What this file proves

| Theorem | Statement | Status |
|---------|-----------|--------|
| `exists_minimal_normal_subgroup` | A nontrivial finite group has a minimal normal subgroup `N` (normal, `≠ ⊥`, and no proper nontrivial normal subgroup sits below it) | Proved (0 axioms) |
| `minimal_normal_abelian_of_solvable` | A minimal normal subgroup of a solvable group is abelian | Proved (0 axioms) |
| `exists_abelian_minimal_normal_subgroup` | A nontrivial finite solvable group has an abelian minimal normal subgroup | Proved (0 axioms) |

## Proof ideas

* **Existence.** For finite `G` the lattice `Subgroup G` is finite, so the set
  `{K | K.Normal ∧ K ≠ ⊥}` is a finite, nonempty (`⊤` belongs, as `G` is
  nontrivial) subset of a partial order, hence has a minimal element
  (`Set.Finite.exists_minimal`). Minimality in the order *restricted to that set*
  is exactly minimality among nontrivial normal subgroups.

* **Abelianness.** Let `N` be a minimal normal subgroup of a solvable group.
  The commutator `⁅N, N⁆` is normal in `G` (`Subgroup.commutator_normal`), is
  contained in `N` (`Subgroup.commutator_le_self`), and is *strictly* smaller than
  `N` because `G` is solvable (`IsSolvable.commutator_lt_of_ne_bot`). By
  minimality a normal subgroup strictly below `N` cannot be nontrivial, so
  `⁅N, N⁆ = ⊥`; equivalently `N ≤ centralizer N`, i.e. `N` is abelian.

## The remaining gap (toward a full 0-axiom Hall theorem)

Still missing: that an abelian minimal normal subgroup of a finite group is
*elementary abelian* (a `p`-group of exponent `p`). The argument: for a prime
`p ∣ |N|`, the `p`-torsion of the abelian group `N` is characteristic in `N`,
hence normal in `G`, and nontrivial by Cauchy — so by minimality it is all of
`N`, forcing exponent `p`. Formalizing the characteristic-`p`-torsion subgroup is
the next increment.

## References
- Hall, P. (1928), "A note on soluble groups", J. London Math. Soc.
- Gorenstein, "Finite Groups", Ch. 6.
-/

namespace LagrangeOQ01OQ03OQ02

open Subgroup

variable {G : Type*} [Group G]

/-- The minimality predicate used below: `N` is a *minimal normal subgroup* if it
is normal, nontrivial, and every nontrivial normal subgroup contained in `N`
equals `N`. -/
def IsMinimalNormal (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≤ N → M ≠ ⊥ → M = N

-- ============================================================
-- Part I: Existence of a minimal normal subgroup
-- ============================================================

/-- **Existence of a minimal normal subgroup.** Every nontrivial finite group has
a minimal normal subgroup: a normal subgroup `N ≠ ⊥` such that no nontrivial
normal subgroup lies strictly below it. Proved with 0 axioms. -/
theorem exists_minimal_normal_subgroup [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, IsMinimalNormal N := by
  -- The set of nontrivial normal subgroups, as a subset of the finite lattice.
  set s : Set (Subgroup G) := {K | K.Normal ∧ K ≠ ⊥} with hs
  -- It is nonempty: `⊤` is normal and `≠ ⊥` since `G` is nontrivial.
  have hne : s.Nonempty := ⟨⊤, ⟨inferInstance, top_ne_bot⟩⟩
  -- It is finite: `Subgroup G` injects into the finite `Set G`, so it is finite.
  haveI : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  have hfin : s.Finite := Set.toFinite s
  -- Pick a minimal element with respect to the subgroup order.
  obtain ⟨N, hN⟩ := hfin.exists_minimal hne
  obtain ⟨⟨hNnorm, hNbot⟩, hmin⟩ := hN
  refine ⟨N, hNnorm, hNbot, ?_⟩
  intro M hMnorm hMle hMbot
  -- `M` belongs to `s`, sits below `N`, so by minimality `N ≤ M`, hence `M = N`.
  exact le_antisymm hMle (hmin ⟨hMnorm, hMbot⟩ hMle)

-- ============================================================
-- Part II: Minimal normal subgroups of solvable groups are abelian
-- ============================================================

/-- **A minimal normal subgroup of a solvable group is abelian.** If `N` is a
minimal normal subgroup of a solvable group `G`, then any two elements of `N`
commute. Proved with 0 axioms. -/
theorem minimal_normal_abelian_of_solvable [IsSolvable G]
    {N : Subgroup G} (hN : IsMinimalNormal N) :
    ∀ a b : N, a * b = b * a := by
  obtain ⟨hNnorm, hNbot, hmin⟩ := hN
  -- Register `N.Normal` as an instance so `commutator_normal` applies.
  haveI : N.Normal := hNnorm
  -- `⁅N, N⁆` is normal in `G`, contained in `N`, and strictly below `N`.
  have hcn : (⁅N, N⁆ : Subgroup G).Normal := Subgroup.commutator_normal N N
  have hle : (⁅N, N⁆ : Subgroup G) ≤ N := Subgroup.commutator_le_self N
  have hlt : (⁅N, N⁆ : Subgroup G) < N := IsSolvable.commutator_lt_of_ne_bot hNbot
  -- A normal subgroup strictly below the minimal `N` cannot be nontrivial.
  have hbot : (⁅N, N⁆ : Subgroup G) = ⊥ := by
    by_contra h
    exact (ne_of_lt hlt) (hmin _ hcn hle h)
  -- `⁅N, N⁆ = ⊥` means `N` centralizes itself, i.e. `N` is abelian.
  have hcent : N ≤ Subgroup.centralizer (N : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  intro a b
  have h : (b : G) * (a : G) = (a : G) * (b : G) :=
    (Subgroup.mem_centralizer_iff.mp (hcent a.2)) b b.2
  exact Subtype.ext h.symm

/-- **Existence of an abelian minimal normal subgroup.** Every nontrivial finite
solvable group has a minimal normal subgroup, and it is abelian. This packages
exactly the structural input that a 0-axiom proof of Hall's theorem requires (cf.
the lifting step in `LagrangeTheoremOQ01OQ03OQ01.lean`). Proved with 0 axioms. -/
theorem exists_abelian_minimal_normal_subgroup
    [Finite G] [Nontrivial G] [IsSolvable G] :
    ∃ N : Subgroup G, IsMinimalNormal N ∧ ∀ a b : N, a * b = b * a := by
  obtain ⟨N, hN⟩ := exists_minimal_normal_subgroup (G := G)
  exact ⟨N, hN, minimal_normal_abelian_of_solvable hN⟩

end LagrangeOQ01OQ03OQ02
