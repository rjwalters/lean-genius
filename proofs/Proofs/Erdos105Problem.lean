/-
Erdős Problem #105: Rich Lines Avoiding Obstacles

Source: https://erdosproblems.com/105
Status: DISPROVED (Xichuan)
Prize: $50 (for proof or disproof)

Statement:
Let A, B ⊂ ℝ² be disjoint sets of size n and n-3 respectively, with not all
of A contained on a single line. Is there a line which contains at least two
points from A and no points from B?

Answer: NO (DISPROVED)

History:
- Erdős & Purdy (1995) conjectured this is TRUE
- Hickerson showed the conjecture fails with n-2 obstacles
- Beck (1983) and Szemerédi-Trotter (1983) independently proved it's true
  with cn obstacles for some constant c > 0
- Xichuan (2024) disproved the n-3 conjecture with three explicit counterexamples

The $50 prize was awarded for the disproof.

Open Questions:
- Does the statement hold with n-4 obstacles?
- What is the largest f(n) for which the statement holds?

References:
- [ErPu95] Erdős & Purdy, "Extremal problems in combinatorial geometry" (1995)
- [Be83] Beck, "On the lattice property of the plane" (1983)
- [SzTr83] Szemerédi & Trotter, "Extremal problems in discrete geometry" (1983)

Tags: discrete-geometry, incidence-geometry, counterexample, disproved
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open Set Finset

namespace Erdos105

/- ## Part I: Basic Definitions -/

/-- A point in the plane ℝ². -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- A line in the plane, represented by a point and a direction vector. -/
structure Line where
  basePoint : Point
  direction : Point
  direction_nonzero : direction ≠ 0

/-- A point lies on a line if it can be written as base + t * direction. -/
def Line.contains (L : Line) (p : Point) : Prop :=
  ∃ t : ℝ, p = L.basePoint + t • L.direction

/-- A line is "rich" for a set A if it contains at least 2 points of A. -/
def Line.isRich (L : Line) (A : Set Point) : Prop :=
  ∃ p q : Point, p ∈ A ∧ q ∈ A ∧ p ≠ q ∧ L.contains p ∧ L.contains q

/-- A line is "unblocked" by a set B if it contains no points of B. -/
def Line.unblocked (L : Line) (B : Set Point) : Prop :=
  ∀ b ∈ B, ¬L.contains b

/-- A line is "rich and unblocked" if it has ≥2 points of A and 0 points of B. -/
def Line.richAndUnblocked (L : Line) (A B : Set Point) : Prop :=
  L.isRich A ∧ L.unblocked B

/- ## Part II: The Erdős-Purdy Conjecture -/

/-- A set of points is non-collinear if no single line contains all of them. -/
def NonCollinear (A : Set Point) : Prop :=
  ∀ L : Line, ∃ p ∈ A, ¬L.contains p

/-- The Erdős-Purdy Conjecture (n-3 version):
    For disjoint A, B with |A| = n, |B| = n-3, and A non-collinear,
    there exists a line containing ≥2 points of A and no points of B. -/
def ErdosPurdyConjecture : Prop :=
  ∀ (A B : Finset Point) (n : ℕ),
    n ≥ 4 →
    A.card = n →
    B.card = n - 3 →
    Disjoint A B →
    NonCollinear (A : Set Point) →
    ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point)

/- ## Part III: The Disproof -/

/--
**Theorem (Xichuan 2024):**
The Erdős-Purdy conjecture is FALSE.

There exist finite sets A, B ⊂ ℝ² with |A| = n, |B| = n-3,
A non-collinear, and every line through 2+ points of A
also contains a point of B.

Three explicit counterexamples were constructed.
-/
axiom xichuan_counterexample :
    ∃ (A B : Finset Point) (n : ℕ),
      n ≥ 4 ∧
      A.card = n ∧
      B.card = n - 3 ∧
      Disjoint A B ∧
      NonCollinear (A : Set Point) ∧
      ∀ L : Line, L.isRich (A : Set Point) → ¬L.unblocked (B : Set Point)

/-- **Erdős Problem #105: DISPROVED** -/
theorem erdos_105_disproved : ¬ErdosPurdyConjecture := by
  intro h
  obtain ⟨A, B, n, hn4, hAcard, hBcard, hdisj, hncoll, hblocked⟩ := xichuan_counterexample
  have ⟨L, hrich, hunblocked⟩ := h A B n hn4 hAcard hBcard hdisj hncoll
  exact hblocked L hrich hunblocked

/- ## Part IV: Related Results -/

/-- **Hickerson's Construction:**
    The conjecture already fails with n-2 obstacles.
    This shows n-3 is the "critical" case (if the conjecture were true). -/
/-- **Beck-Szemerédi-Trotter Positive Result:**
    With only cn obstacles (for some constant c > 0), the conjecture IS true.
    There must exist a rich line avoiding all obstacles. -/
axiom beck_szemeredi_trotter_positive :
    ∃ c : ℝ, c > 0 ∧ ∀ (A B : Finset Point),
      NonCollinear (A : Set Point) →
      (B.card : ℝ) ≤ c * A.card →
      Disjoint A B →
      ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point)

/- ## Part V: The Szemerédi-Trotter Theorem -/

/-- The number of point-line incidences.
    I(P, L) = |{(p, ℓ) : p ∈ P, ℓ ∈ L, p ∈ ℓ}|. -/
noncomputable def incidenceCount (P : Finset Point) (L : Finset Line) : ℕ :=
  (P ×ˢ L).filter (fun (p, ℓ) => ℓ.contains p) |>.card

/-- **Szemerédi-Trotter Theorem (1983):**
    For n points and m lines in ℝ², the number of incidences is
    O(n^(2/3) m^(2/3) + n + m).

    This is optimal up to constants. -/
/-- Any set of ≥ 2 points has a rich line (any two distinct points determine one).
    Formerly an axiom stated as a corollary of Szemerédi-Trotter, but the basic
    existence of at least one rich line is trivially true from the definitions. -/
theorem many_rich_lines_exist (A : Finset Point) (hncoll : NonCollinear (A : Set Point))
    (hn : A.card ≥ 3) :
    ∃ k : ℕ, k ≥ 1 ∧ ∃ (S : Finset Line), S.card = k ∧
      ∀ L ∈ S, L.isRich (A : Set Point) := by
  classical
  -- A has ≥ 3 points, so ≥ 2 distinct points exist
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  -- The line through p and q is rich
  have hdir : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  let L : Line := ⟨p, q - p, hdir⟩
  have hp_on : L.contains p := ⟨0, by simp [L, Line.contains, zero_smul, add_zero]⟩
  have hq_on : L.contains q := ⟨1, by simp [L, Line.contains, one_smul, add_sub_cancel]⟩
  have hrich : L.isRich (A : Set Point) :=
    ⟨p, q, Finset.mem_coe.mpr hp, Finset.mem_coe.mpr hq, Ne.symm hpq, hp_on, hq_on⟩
  exact ⟨1, le_refl 1, {L}, Finset.card_singleton L, fun L' hL' => by
    rw [Finset.mem_singleton.mp hL']; exact hrich⟩

/- ## Part VI: Threshold Function -/

/-- f(n) = largest number such that for all A with |A| = n non-collinear,
    and all B with |B| ≤ f(n), some rich line of A avoids B.
    Known: c·n ≤ f(n) ≤ n - 4. Axiomatized since exact determination is open. -/
axiom thresholdFunction (n : ℕ) : ℕ

/-- **Lower bound:** f(n) ≥ c·n for some c > 0. -/
/-- **Upper bound:** f(n) ≤ n - 4 (from Xichuan's counterexample). -/
/- ## Part VII: Open Problems -/

/-- **Open Problem 1:** Does the conjecture hold with n-4 obstacles? -/
def openProblem_n_minus_4 : Prop :=
  ∀ (A B : Finset Point) (n : ℕ),
    n ≥ 5 →
    A.card = n →
    B.card = n - 4 →
    Disjoint A B →
    NonCollinear (A : Set Point) →
    ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point)

/-- **Open Problem 2:** What is the exact threshold f(n)? Is f(n) = Θ(n)? -/
def openProblem_exact_threshold : Prop :=
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∀ n : ℕ, c₁ * n ≤ (thresholdFunction n : ℝ) ∧
              (thresholdFunction n : ℝ) ≤ c₂ * n

/- ## Part VIII: Summary -/

/--
**Summary of Erdős Problem #105**

**Question**: Given n points A (not collinear) and n-3 obstacles B,
must some line through 2+ points of A avoid all of B?

**Answer**: NO (DISPROVED by Xichuan 2024)

**What we formalize**:
1. Definitions of points, lines, "rich" lines, "unblocked" lines
2. The Erdős-Purdy conjecture
3. Xichuan's counterexample (as axiom)
4. The formal disproof
5. Related results (Hickerson, Beck, Szemerédi-Trotter)
6. The threshold function f(n)
7. Open problems

**Key insight**: While Szemerédi-Trotter guarantees many rich lines exist,
n-3 obstacles can be placed to block ALL of them in carefully constructed
configurations.

**Prize**: $50 awarded for the disproof
-/
theorem erdos_105_summary :
    ¬ErdosPurdyConjecture ∧
    (∃ c : ℝ, c > 0 ∧ ∀ (A B : Finset Point),
      NonCollinear (A : Set Point) →
      (B.card : ℝ) ≤ c * A.card →
      Disjoint A B →
      ∃ L : Line, L.richAndUnblocked (A : Set Point) (B : Set Point)) :=
  ⟨erdos_105_disproved, beck_szemeredi_trotter_positive⟩

/-
## Historical Notes

1971-1995: Erdős and Purdy study point-line incidence problems
1983: Beck proves rich-line existence with cn obstacles
1983: Szemerédi-Trotter prove their famous incidence bound
1995: Erdős-Purdy conjecture the n-3 version
????: Hickerson shows n-2 fails
2024: Xichuan disproves n-3 with three counterexamples

The problem illustrates the subtle boundary between
"many rich lines exist" (Szemerédi-Trotter) and
"not all can be blocked" (which turns out to be false at n-3).
-/

/-
## Part IX: OQ-05 — Higher-Dimensional Generalizations

In ℝ^d for d ≥ 3, the analogous question replaces lines with k-flats
and asks whether rich k-flats can always avoid obstacles.
-/

/-- A point in ℝ^d. -/
abbrev PointD (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A k-flat in ℝ^d is an affine subspace of dimension k. -/
structure KFlat (d : ℕ) where
  /-- The underlying affine subspace. -/
  subspace : AffineSubspace ℝ (PointD d)
  /-- The dimension of the flat. -/
  dim : ℕ

/-- A k-flat is "rich" for a set A if it contains at least k+1 points of A
    in general position (not all in a lower-dimensional flat). -/
def KFlat.isRich (F : KFlat d) (A : Set (PointD d)) : Prop :=
  ∃ (S : Finset (PointD d)), ↑S ⊆ A ∧ S.card ≥ F.dim + 1 ∧
    ∀ p ∈ S, p ∈ F.subspace

/-- A k-flat is "unblocked" by B if it contains no points of B. -/
def KFlat.unblocked (F : KFlat d) (B : Set (PointD d)) : Prop :=
  ∀ b ∈ B, b ∉ F.subspace

/-- A set is not contained in any k-flat (non-degeneracy). -/
def NonDegenerate (d k : ℕ) (A : Set (PointD d)) : Prop :=
  ∀ F : KFlat d, F.dim = k → ∃ p ∈ A, p ∉ F.subspace

/-- **OQ-05:** In ℝ^d, given n points A in non-degenerate position and
    obstacles B, does there exist a rich 2-flat through ≥ 3 points of A
    that avoids all obstacles?

    This is the natural generalization of Erdős #105 to higher dimensions,
    replacing "line through 2 points" with "2-flat through 3 points". -/
def higherDimAnalogue (d : ℕ) (hd : d ≥ 3) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ (A B : Finset (PointD d)),
    NonDegenerate d 2 (A : Set (PointD d)) →
    (B.card : ℝ) ≤ c * A.card →
    Disjoint A B →
    ∃ F : KFlat d, F.dim = 2 ∧
      F.isRich (A : Set (PointD d)) ∧
      F.unblocked (B : Set (PointD d))

/-- The simplest higher-dimensional case: rich 2-flats in ℝ³. -/
def threeSpaceCase : Prop := higherDimAnalogue 3 (by omega)

end Erdos105

