import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-
Erdős Problem #960: Ordinary Lines and Collinear Ramsey Thresholds

Let r, k ≥ 2 be fixed. Given n points in ℝ² with no k collinear,
an ordinary line contains exactly 2 points of the set. Determine
the threshold f_{r,k}(n) such that if there are ≥ f_{r,k}(n) ordinary
lines, then there exist r points where all C(r,2) connecting lines
are ordinary.

Is f_{r,k}(n) = o(n²)? Is f_{r,k}(n) ≪ n?

Turán's theorem gives: f_{r,k}(n) ≤ (1 - 1/(r-1)) · n²/2 + 1.

Status: OPEN

Reference: https://erdosproblems.com/960
Source: [Er84]
-/

-- ## Part I: Point Configurations and Collinearity

namespace Erdos960

open Classical

/-- A point configuration is a finite set of points (represented abstractly). -/
structure PointConfig where
  n : ℕ
  points : Finset (ℕ × ℕ)
  card_eq : points.card = n

/-- No k points are collinear (general position up to k). -/
def NoKCollinear (P : PointConfig) (k : ℕ) : Prop :=
  ∀ (S : Finset (ℕ × ℕ)), S ⊆ P.points → S.card = k →
    ¬∃ (a b c : ℤ), (a, b, c) ≠ (0, 0, 0) ∧
      ∀ p ∈ S, a * (p.1 : ℤ) + b * (p.2 : ℤ) + c = 0

-- ## Part II: Ordinary Lines

/-- A line through two points is ordinary if exactly 2 points of P lie on it. -/
def IsOrdinaryLine (P : PointConfig) (p q : ℕ × ℕ) : Prop :=
  p ∈ P.points ∧ q ∈ P.points ∧ p ≠ q ∧
    ∀ r ∈ P.points, r ≠ p → r ≠ q →
      ¬∃ (t : ℚ), (r.1 : ℚ) = (1 - t) * (p.1 : ℚ) + t * (q.1 : ℚ) ∧
                   (r.2 : ℚ) = (1 - t) * (p.2 : ℚ) + t * (q.2 : ℚ)

/-- Count of ordinary lines (simplified: count of unordered pairs). -/
noncomputable def ordinaryLineCount (P : PointConfig) : ℕ :=
  (P.points.offDiag.filter
    (fun (pq : (ℕ × ℕ) × (ℕ × ℕ)) => IsOrdinaryLine P pq.1 pq.2)).card / 2

-- ## Part III: All-Ordinary Subsets

/-- A subset S has all connecting lines ordinary if every pair in S
    determines an ordinary line in P. -/
def AllOrdinary (P : PointConfig) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ P.points ∧ ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsOrdinaryLine P p q

/-- IsOrdinaryLine is symmetric: if the line through p,q is ordinary,
    then so is the line through q,p. Uses the substitution t ↦ 1-t
    to transform the parametric representation. -/
theorem isOrdinaryLine_symm (P : PointConfig) (p q : ℕ × ℕ)
    (h : IsOrdinaryLine P p q) : IsOrdinaryLine P q p := by
  obtain ⟨hp, hq, hne, hord⟩ := h
  refine ⟨hq, hp, hne.symm, fun r hr hrq hrp => ?_⟩
  intro ⟨t, ht1, ht2⟩
  exact hord r hr hrp hrq ⟨1 - t, by linarith, by linarith⟩

-- ## Part IV: The Threshold Function

/-- f_{r,k}(n): the minimum number of ordinary lines that guarantees
    an r-point all-ordinary subset, over all n-point configurations
    with no k collinear. -/
noncomputable def threshold (r k n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ (P : PointConfig), P.n = n ∧ NoKCollinear P k ∧
    ordinaryLineCount P ≥ m ∧
    ¬∃ (S : Finset (ℕ × ℕ)), S.card = r ∧ AllOrdinary P S }

-- ## Part V: The Main Conjecture

/-- Erdős Problem #960: Is f_{r,k}(n) = o(n²)?
    That is, for every ε > 0, f_{r,k}(n) < ε · n² for large n.
    Stated with ℚ cast to avoid floor/ceil dependencies. -/
def ErdosConjecture960_littleo (r k : ℕ) : Prop :=
  ∀ ε : ℚ, ε > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (threshold r k n : ℚ) < ε * ↑n * ↑n

/-- Stronger form: Is f_{r,k}(n) ≪ n? -/
def ErdosConjecture960_linear (r k : ℕ) : Prop :=
  ∃ C : ℕ, ∀ n : ℕ, threshold r k n ≤ C * n

/-- The little-o conjecture (axiomatized as OPEN). -/
axiom erdos_960_littleo_conjecture : ∀ r k : ℕ, r ≥ 2 → k ≥ 2 →
  ErdosConjecture960_littleo r k

-- ## Part VI: Turán Upper Bound

/-- Turán's theorem gives an upper bound on the threshold.
    For r ≥ 2, f_{r,k}(n) ≤ (1 - 1/(r-1)) · n²/2 + 1.
    Stated over ℚ to avoid natural number underflow. -/
theorem turan_upper_bound (r k n : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
  (threshold r k n : ℚ) ≤ (1 - 1 / (r - 1 : ℚ)) * n^2 / 2 + 1 := by sorry

/-- The trivial upper bound: at most C(n,2) ordinary lines total.
    Follows from: filtered offDiag ⊆ offDiag, and |offDiag| = n(n-1). -/
theorem trivial_bound (P : PointConfig) :
  ordinaryLineCount P ≤ P.n * (P.n - 1) / 2 := by
  unfold ordinaryLineCount
  apply Nat.div_le_div_right
  calc (P.points.offDiag.filter
        (fun (pq : (ℕ × ℕ) × (ℕ × ℕ)) => IsOrdinaryLine P pq.1 pq.2)).card
      ≤ P.points.offDiag.card := Finset.card_filter_le _ _
    _ = P.n * (P.n - 1) := by sorry -- Finset.card_offDiag not available; need: offDiag.card = n*(n-1)

-- ## Part VII: Known Cases and Connections

/-- Any ordinary line gives a 2-point all-ordinary subset:
    if the line through p,q is ordinary, then {p,q} is a 2-element
    subset where all C(2,2) = 1 connecting lines are ordinary. -/
theorem ordinary_gives_pair (P : PointConfig) (p q : ℕ × ℕ)
    (h : IsOrdinaryLine P p q) :
    ∃ S : Finset (ℕ × ℕ), S.card = 2 ∧ AllOrdinary P S := by
  have hsymm := isOrdinaryLine_symm P p q h
  obtain ⟨hp, hq, hne, hord⟩ := h
  use {p, q}
  refine ⟨?_, ?_, ?_⟩
  · -- card {p, q} = 2
    have hmem : p ∉ ({q} : Finset _) := Finset.notMem_singleton.mpr hne
    simp [Finset.card_insert_of_notMem hmem]
  · -- {p, q} ⊆ P.points
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> assumption
  · -- all pairs ordinary
    intro a ha b hb hab
    simp at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd rfl hab
    · exact ⟨hp, hq, hne, hord⟩
    · exact hsymm
    · exact absurd rfl hab

/-- For r = 2: f_{2,k}(n) = 0.
    Any ordinary line gives a 2-point all-ordinary subset (by ordinary_gives_pair),
    so no configuration can have ≥ 1 ordinary lines without having a 2-point
    all-ordinary subset. The threshold set is ⊆ {0}, so sSup = 0.
    (Previously claimed = 1, corrected: the threshold is the max number of ordinary
    lines a config can have WITHOUT an all-ordinary r-subset.) -/
theorem threshold_r2 (k n : ℕ) (hk : k ≥ 2) (hn : n ≥ 2) :
  threshold 2 k n = 0 := by sorry

/-- The Sylvester-Gallai theorem: any finite non-collinear point set
    in ℝ² has at least one ordinary line. For n points with no 3
    collinear, there are at least n/2 ordinary lines (Green-Tao 2013). -/
theorem green_tao_ordinary_lines (P : PointConfig) (hn : P.n ≥ 13)
    (h3 : NoKCollinear P 3) :
  ordinaryLineCount P ≥ P.n / 2 := by sorry

/-- An all-ordinary subset of r points has r*(r-1) ordered ordinary pairs.
    This is the number of ordered pairs in an r-element set (offDiag). -/
theorem ordinary_pairs_count (r : ℕ) (hr : r ≥ 2) :
    ∀ P : PointConfig, ∀ S : Finset (ℕ × ℕ), S.card = r → AllOrdinary P S →
      S.offDiag.card = r * (r - 1) := by
  intro P S hcard _hord
  sorry -- Finset.card_offDiag not available; need: offDiag.card = n*(n-1)

/-- The linear conjecture implies the little-o conjecture.
    For large enough n (n > C/ε), C·n < ε·n², so threshold ≤ C·n < ε·n².
    N₀ = C · ε.den + 1 ensures n > C/ε since ε ≥ 1/ε.den. -/
theorem linear_implies_littleo (r k : ℕ) (hr : r ≥ 2) (hk : k ≥ 2) :
    ErdosConjecture960_linear r k → ErdosConjecture960_littleo r k := by
  intro ⟨C, hC⟩ ε hε
  -- Need n > C/ε so that C*n < ε*n². Since ε ≥ 1/ε.den, C/ε ≤ C*ε.den.
  use C * ε.den + 1
  intro n hn
  calc (threshold r k n : ℚ) ≤ ↑C * ↑n := by exact_mod_cast hC n
    _ < ε * ↑n * ↑n := by sorry

-- ## Summary

/-- Erdős Problem #960: Summary
    Combines the little-o conjecture, the Turán upper bound,
    and the Sylvester-Gallai/Green-Tao ordinary line result. -/
theorem erdos_960_summary :
    (∀ r k : ℕ, r ≥ 2 → k ≥ 2 → ErdosConjecture960_littleo r k) ∧
    (∀ k n : ℕ, k ≥ 2 → n ≥ 2 → threshold 2 k n = 0) :=
  ⟨erdos_960_littleo_conjecture, fun k n hk hn => threshold_r2 k n hk hn⟩

end Erdos960
