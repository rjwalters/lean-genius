/-
Erdős Problem #1159: Bounded Blocking Sets in Projective Planes

Source: https://erdosproblems.com/1159
Status: OPEN

Statement:
Does there exist a constant C > 1 such that for any finite projective plane P,
one can find a set of points S where each line ℓ intersects S in at least 1
but at most C points?

Such a set S is called a "C-bounded blocking set" — it blocks every line
(meets it in ≥1 point) while keeping the intersection with any line at most C.

Background:
A blocking set in a projective plane is a set of points that meets every line
in at least one point. Trivially, any line is a blocking set (with n+1 points
on each line through it), but the question asks for *uniformly bounded*
intersections across ALL lines, independent of the plane's order n.

Key Results:
- Erdős, Silverman, and Stein (1983) proved there exists a blocking set S
  with |S ∩ ℓ| = O(log n) for all lines ℓ in a plane of order n.
- The open question is whether O(log n) can be replaced by an absolute
  constant C, independent of n.

Related: Problem #664 poses a stronger variant for block designs.

References:
- Erdős (1981), original formulation
- Erdős, Silverman, and Stein (1983)
-/

import Mathlib

open Configuration

namespace Erdos1159

-- ## Part I: Blocking Set Definitions

/-- A set of points S is a blocking set if every line contains at least one point of S. -/
def IsBlockingSet {P L : Type*} [Membership P L] (S : Set P) : Prop :=
  ∀ l : L, ∃ p ∈ S, p ∈ l

-- ## Part II: Basic Properties (Proved)

/-- If S is a blocking set and S ⊆ T, then T is also a blocking set. -/
theorem blocking_set_mono {P L : Type*} [Membership P L]
    {S T : Set P} (hST : S ⊆ T) (hS : IsBlockingSet S) : IsBlockingSet (L := L) T := by
  intro l
  obtain ⟨p, hpS, hpl⟩ := hS l
  exact ⟨p, hST hpS, hpl⟩

/-- The empty set is not a blocking set in any nontrivial configuration. -/
theorem empty_not_blocking_set {P L : Type*} [Membership P L] [Nonempty L] :
    ¬IsBlockingSet (∅ : Set P) := by
  intro h
  obtain ⟨l⟩ := ‹Nonempty L›
  obtain ⟨p, hp, _⟩ := h l
  exact Set.not_mem_empty p hp

-- ## Part III: Structural Results (Proved from Mathlib)

/-- In a projective plane, every line has exactly order + 1 points. -/
theorem pointCount_eq' {P L : Type*} [Membership P L] [ProjectivePlane P L]
    [Finite P] [Finite L] (l : L) :
    pointCount P l = ProjectivePlane.order P L + 1 :=
  ProjectivePlane.pointCount_eq P L l

/-- In a projective plane, every point lies on exactly order + 1 lines. -/
theorem lineCount_eq' {P L : Type*} [Membership P L] [ProjectivePlane P L]
    [Finite P] [Finite L] (p : P) :
    lineCount L p = ProjectivePlane.order P L + 1 :=
  ProjectivePlane.lineCount_eq L p

/-- A projective plane of order n has n² + n + 1 points. -/
theorem card_points' {P L : Type*} [Membership P L] [ProjectivePlane P L]
    [Fintype P] [Finite L] :
    Fintype.card P = (ProjectivePlane.order P L) ^ 2 + ProjectivePlane.order P L + 1 :=
  ProjectivePlane.card_points P L

/-- A projective plane of order n has n² + n + 1 lines. -/
theorem card_lines' {P L : Type*} [Membership P L] [ProjectivePlane P L]
    [Finite P] [Fintype L] :
    Fintype.card L = (ProjectivePlane.order P L) ^ 2 + ProjectivePlane.order P L + 1 :=
  ProjectivePlane.card_lines P L

-- ## Part IV: Known Bound (Erdős-Silverman-Stein 1983)

/-- **Erdős-Silverman-Stein (1983)**: In any finite projective plane of order n,
    there exists a blocking set S such that every line meets S in at most
    O(log n) points.

    This is a known result from the literature, established by probabilistic
    methods. A random subset of points where each point is included independently
    with probability c·(log n)/n yields a blocking set with the desired property
    with high probability. -/
axiom ess_log_blocking_set :
    ∀ (P L : Type*) [Membership P L] [inst : ProjectivePlane P L]
      [Fintype P] [Fintype L],
    ∃ (S : Set P),
      IsBlockingSet S ∧
      ∀ l : L, Nat.card {p : P | p ∈ S ∧ p ∈ l} ≤
        3 * (Nat.log 2 (ProjectivePlane.order P L) + 1)

-- ## Part V: The Open Problem (Erdős #1159)

/- **Erdős Problem #1159** (Open):
    Does there exist an absolute constant C such that every finite projective
    plane has a C-bounded blocking set?

    The ESS result gives O(log n), but the question is whether this can be
    improved to an absolute constant independent of n. -/

/-- The formal statement of Erdős Problem #1159: there exists an absolute
    constant C such that every finite projective plane admits a blocking set
    meeting every line in between 1 and C points. -/
def BoundedBlockingSetConjecture : Prop :=
  ∃ C : ℕ, ∀ (P L : Type*) [Membership P L] [ProjectivePlane P L]
    [Fintype P] [Fintype L],
    ∃ S : Set P,
      IsBlockingSet S ∧
      ∀ l : L, Nat.card {p : P | p ∈ S ∧ p ∈ l} ≤ C

/-- The ESS result implies that no counterexample exists at any fixed order:
    for each order n, there exists C(n) = O(log n) that works. The open
    question is whether C can be made uniform across all n. -/
theorem ess_implies_per_order_bound :
    ∀ (P L : Type*) [Membership P L] [inst : ProjectivePlane P L]
      [Fintype P] [Fintype L],
    ∃ C : ℕ, ∃ S : Set P,
      IsBlockingSet S ∧
      ∀ l : L, Nat.card {p : P | p ∈ S ∧ p ∈ l} ≤ C := by
  intro P L _ _ _ _
  obtain ⟨S, hblock, hbound⟩ := ess_log_blocking_set P L
  exact ⟨3 * (Nat.log 2 (ProjectivePlane.order P L) + 1), S, hblock, hbound⟩

-- ## Part VI: Related Problems

/- Problem #664 asks the stronger question for all pairwise balanced
    block designs, not just projective planes. -/

end Erdos1159
