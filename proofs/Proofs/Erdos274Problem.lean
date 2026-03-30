/-
Erdős Problem #274: Exact Coverings of Groups by Cosets (Herzog-Schönheim Conjecture)

Can a group G have an exact covering by cosets of subgroups with pairwise distinct indices?

**Answer (Abelian case)**: NO - proved by Sun (2004) for subnormal subgroups,
which includes all abelian groups.

**General case**: OPEN - verified computationally for |G| < 1440 by Margolis & Schnabel (2019).

The Herzog-Schönheim conjecture states that if G is any group and a₁G₁, ..., aₖGₖ
are finitely many cosets that partition G, then at least two indices [G:Gᵢ] must be equal.

Reference: https://erdosproblems.com/274
Wikipedia: https://en.wikipedia.org/wiki/Herzog–Schönheim_conjecture
-/

import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Subgroup BigOperators

namespace Erdos274

/- ## Core Definitions -/

/-- An exact covering of a group G by k cosets is a collection of subgroups H₁,...,Hₖ
and representatives g₁,...,gₖ such that the cosets gᵢHᵢ partition G. -/
structure ExactCovering (G : Type*) [Group G] (k : ℕ) where
  /-- The subgroups whose cosets form the covering -/
  subgroups : Fin k → Subgroup G
  /-- The coset representatives -/
  reps : Fin k → G
  /-- Every element of G belongs to exactly one coset gᵢHᵢ -/
  covers : ∀ g : G, ∃! i : Fin k, g ∈ leftCoset (reps i) (subgroups i)

/-- A covering has distinct indices if all [G:Hᵢ] are pairwise different. -/
def hasDistinctIndices {G : Type*} [Group G] {k : ℕ} (C : ExactCovering G k) : Prop :=
  ∀ i j : Fin k, i ≠ j → (C.subgroups i).index ≠ (C.subgroups j).index

/- ## The Herzog-Schönheim Conjecture -/

/--
**Herzog-Schönheim Conjecture** (OPEN in general):
If k > 1 cosets partition a group G, at least two must have the same index.

Proved for:
- Abelian groups (Sun 2004)
- All groups with |G| < 1440 (Margolis & Schnabel 2019)
-/
def HerzogSchonheimConjecture (G : Type*) [Group G] : Prop :=
  ∀ (k : ℕ) (_hk : k > 1), ∀ C : ExactCovering G k, ¬hasDistinctIndices C

/- ## Solved Case: Abelian Groups -/

/--
**Sun's Theorem** (2004):
For finite abelian groups, the Herzog-Schönheim conjecture holds.

This settles Erdős's original question: the answer is NO for abelian groups.
-/
axiom sun_abelian_case (G : Type*) [CommGroup G] [Fintype G]
    (k : ℕ) (hk : k > 1) (C : ExactCovering G k) :
    ¬hasDistinctIndices C

/-- Equivalent formulation: there exist indices with equal subgroup index. -/
theorem abelian_has_repeated_index (G : Type*) [CommGroup G] [Fintype G]
    (k : ℕ) (hk : k > 1) (C : ExactCovering G k) :
    ∃ i j : Fin k, i ≠ j ∧ (C.subgroups i).index = (C.subgroups j).index := by
  have h := sun_abelian_case G k hk C
  unfold hasDistinctIndices at h
  push_neg at h
  exact h

/- ## Computational Verification -/

/--
**Margolis-Schnabel Theorem** (2019):
The conjecture holds for all groups of order < 1440.
-/
/- ## The Open Problem -/

/--
**Erdős Problem #274** (OPEN for general groups):

Is the Herzog-Schönheim conjecture true for all groups?

Known:
- YES for abelian groups (Sun 2004)
- YES for subnormal subgroups (Sun 2004)
- YES for |G| < 1440 (Margolis & Schnabel 2019)
-/
theorem erdos_274_abelian_solved (G : Type*) [CommGroup G] [Fintype G] :
    HerzogSchonheimConjecture G := by
  intro k hk C
  exact sun_abelian_case G k hk C

/- ## Index Sum Lemma -/

/--
**Necessary Condition**:
If k cosets partition G with indices n₁, ..., nₖ, then
|G| = Σᵢ |Hᵢ| = |G| · Σᵢ (1/nᵢ), so Σᵢ (1/nᵢ) = 1.

Example: Indices 2, 3, 6 satisfy 1/2 + 1/3 + 1/6 = 1.
-/
/- ## Summary -/

/--
**Erdős Problem #274: Summary**

PROBLEM: Can a group be exactly covered by cosets with pairwise distinct indices?
STATUS: Partially solved

KNOWN:
- Abelian groups: NO (Sun 2004)
- Groups of order < 1440: NO (Margolis-Schnabel 2019)
- General case: OPEN

The abelian case settles Erdős's original question.
-/
theorem erdos_274_summary (G : Type*) [CommGroup G] [Fintype G] :
    HerzogSchonheimConjecture G :=
  erdos_274_abelian_solved G

end Erdos274
