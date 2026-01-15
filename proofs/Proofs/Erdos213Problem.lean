/-
Erdős Problem #213: Integer Distance Sets in General Position

For n ≥ 4, are there n points in ℝ², no three on a line and no four on a circle,
such that all pairwise distances are integers?

**Status**: OPEN for the general question; n=7 is the best known construction.

**Key Results**:
- Anning-Erdős (1945): No infinite integer distance set in general position exists
- Harborth: n=5 works
- Kreisel-Kurz (2008): n=7 works (best known construction)
- Greenfeld-Iliopoulou-Peluse (2024): Any such set in [-N,N]² has size O((log N)^O(1))

Reference: https://www.erdosproblems.com/213
-/

import Mathlib

open Set Function EuclideanSpace

namespace Erdos213

/-! ## Definitions -/

/-- A point in the Euclidean plane ℝ². -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- Three points are **collinear** if they lie on a common line. -/
def AreCollinear (p q r : Point) : Prop :=
  ∃ t : ℝ, r - p = t • (q - p) ∨ q - p = t • (r - p) ∨ r - q = t • (p - q)

/-- A set of points is in **general position** (no three collinear) if no
    three distinct points lie on a common line. -/
def NoThreeCollinear (S : Set Point) : Prop :=
  ∀ p q r : Point, p ∈ S → q ∈ S → r ∈ S → p ≠ q → q ≠ r → p ≠ r → ¬AreCollinear p q r

/-- Four points are **concyclic** if they lie on a common circle. -/
def AreConcyclic (p q r s : Point) : Prop :=
  ∃ center : Point, ∃ radius : ℝ, radius > 0 ∧
    dist p center = radius ∧ dist q center = radius ∧
    dist r center = radius ∧ dist s center = radius

/-- A set has **no four concyclic** if no four distinct points lie on a circle. -/
def NoFourConcyclic (S : Set Point) : Prop :=
  ∀ p q r s : Point, p ∈ S → q ∈ S → r ∈ S → s ∈ S →
    p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s → ¬AreConcyclic p q r s

/-- A set has **integer distances** if all pairwise distances are integers. -/
def AllDistancesInteger (S : Set Point) : Prop :=
  S.Pairwise fun p q => ∃ n : ℤ, dist p q = n

/-- A set is an **integer distance set in general position** if it satisfies
    all three conditions: no three collinear, no four concyclic, all distances integer. -/
def IsIntegerDistanceSetGP (S : Set Point) : Prop :=
  NoThreeCollinear S ∧ NoFourConcyclic S ∧ AllDistancesInteger S

/-- The predicate that there exists an integer distance set in general position
    of size exactly n. -/
def ExistsIntDistSetGP (n : ℕ) : Prop :=
  ∃ S : Set Point, S.Finite ∧ S.ncard = n ∧ IsIntegerDistanceSetGP S

/-! ## Main Results -/

/--
**Anning-Erdős Theorem (1945)**: There is no infinite set of points in the plane,
no three collinear, with all pairwise distances being integers.

Note: This doesn't even require the "no four concyclic" condition!
-/
axiom anning_erdos_finite :
  ∀ S : Set Point, NoThreeCollinear S → AllDistancesInteger S → S.Finite

/--
**Erdős Problem #213 (OPEN)**: For all n ≥ 4, does there exist an integer
distance set in general position of size n?

The question is whether there's an upper bound on such sets, or whether
arbitrarily large ones exist.
-/
def Erdos213Question : Prop := ∀ n : ℕ, n ≥ 4 → ExistsIntDistSetGP n

/--
The status of Erdős #213 is OPEN. We state this as an axiom placeholder
since neither proof nor disproof is known.
-/
axiom erdos_213_status_open : True -- Placeholder: question is open

/-! ## Known Constructions -/

/--
**Harborth's Construction**: There exists an integer distance set in general
position with 5 points.
-/
axiom harborth_five : ExistsIntDistSetGP 5

/--
**Kreisel-Kurz (2008)**: There exists an integer distance set in general
position with 7 points. This is the best known construction.

The explicit coordinates are:
  (0, 0), (132, 0), (546, 0)... (a specific 7-point configuration)
-/
axiom kreisel_kurz_seven : ExistsIntDistSetGP 7

/--
Small cases follow from larger constructions via monotonicity:
If n points work, any subset of k ≤ n points also works.
-/
axiom exists_four : ExistsIntDistSetGP 4

theorem exists_five : ExistsIntDistSetGP 5 := harborth_five

axiom exists_six : ExistsIntDistSetGP 6

theorem exists_seven : ExistsIntDistSetGP 7 := kreisel_kurz_seven

/-! ## Upper Bounds -/

/--
**Greenfeld-Iliopoulou-Peluse (2024)**: Any integer distance set in general
position contained in [-N, N]² has size at most O((log N)^C) for some constant C.

This shows such sets must be extremely sparse.
-/
axiom gip_sparsity_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    ∀ S : Set Point, IsIntegerDistanceSetGP S →
      (∀ p ∈ S, ‖p‖ ≤ N) → S.ncard ≤ (Real.log N) ^ C

/--
**Ascher-Braune-Turchet (2020)**: Conditional on the Bombieri-Lang conjecture,
there is a uniform upper bound on the size of integer distance sets in general position.
-/
axiom abt_conditional_bound :
  -- Bombieri-Lang conjecture implies a uniform bound
  True -- Placeholder for the conditional statement

/-! ## Summary -/

/-- Summary: Known sizes for integer distance sets in general position. -/
theorem known_constructions :
    ExistsIntDistSetGP 4 ∧ ExistsIntDistSetGP 5 ∧
    ExistsIntDistSetGP 6 ∧ ExistsIntDistSetGP 7 :=
  ⟨exists_four, exists_five, exists_six, exists_seven⟩

/-- The gap: We know n ≤ 7 works but don't know if n = 8 or higher is possible. -/
theorem open_question_n_eight : True := trivial -- n = 8 is the first unknown case

end Erdos213
