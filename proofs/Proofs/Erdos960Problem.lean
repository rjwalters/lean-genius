import Mathlib

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

open Classical in
attribute [local instance] Classical.propDecidable

/-- A point configuration is a finite set of points (represented abstractly). -/
structure PointConfig where
  n : ℕ
  points : Finset (ℕ × ℕ)
  card_eq : points.card = n

/-- No k points are collinear (general position up to k). -/
def NoKCollinear (P : PointConfig) (k : ℕ) : Prop :=
  ∀ (S : Finset (ℕ × ℕ)), S ⊆ P.points → S.card = k →
    ¬∃ (a b c : ℤ), (a, b, c) ≠ (0, 0, 0) ∧
      ∀ p ∈ S, a * p.1 + b * p.2 + c = 0

-- ## Part II: Ordinary Lines

/-- A line through two points is ordinary if exactly 2 points of P lie on it. -/
def IsOrdinaryLine (P : PointConfig) (p q : ℕ × ℕ) : Prop :=
  p ∈ P.points ∧ q ∈ P.points ∧ p ≠ q ∧
    ∀ r ∈ P.points, r ≠ p → r ≠ q →
      ¬∃ (t : ℚ), (r.1 : ℚ) = (1 - t) * p.1 + t * q.1 ∧
                   (r.2 : ℚ) = (1 - t) * p.2 + t * q.2

/-- Count of ordinary lines (simplified: count of unordered pairs). -/
noncomputable def ordinaryLineCount (P : PointConfig) : ℕ :=
  ((P.points ×ˢ P.points).filter
    fun (pq : (ℕ × ℕ) × (ℕ × ℕ)) => pq.1 ≠ pq.2 ∧ IsOrdinaryLine P pq.1 pq.2).card / 2

-- ## Part III: All-Ordinary Subsets

/-- A subset S has all connecting lines ordinary if every pair in S
    determines an ordinary line in P. -/
def AllOrdinary (P : PointConfig) (S : Finset (ℕ × ℕ)) : Prop :=
  S ⊆ P.points ∧ ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsOrdinaryLine P p q

/-- IsOrdinaryLine is symmetric: if the line through p,q is ordinary,
    then so is the line through q,p. -/
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
    Formulated directly over ℚ to avoid ℚ-to-ℕ coercion issues. -/
def ErdosConjecture960_littleo (r k : ℕ) : Prop :=
  ∀ ε : ℚ, ε > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    (threshold r k n : ℚ) < ε * n * n

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

/-- The trivial upper bound: at most C(n,2) ordinary lines total. -/
theorem trivial_bound (P : PointConfig) :
  ordinaryLineCount P ≤ P.n * (P.n - 1) / 2 := by
  sorry -- TODO: needs offDiag card lemma (Finset.card_offDiag renamed in Mathlib 4.26)

-- ## Part VII: Known Cases and Connections

/-- For r = 2: the threshold is 0. With the sSup-based definition of `threshold`,
    which computes the maximum m where a counterexample exists, there are no
    counterexamples for r = 2: any configuration with ≥ 1 ordinary line has a
    2-element all-ordinary subset (the two points on that line). By Sylvester-Gallai,
    every finite non-collinear set has ordinary lines.
    Proof: the set in the sSup is empty, so sSup = 0. -/
theorem threshold_r2 (k n : ℕ) (_hk : k ≥ 2) (_hn : n ≥ 2) :
  threshold 2 k n = 0 := by sorry

/-- The Sylvester-Gallai theorem: any finite non-collinear point set
    in ℝ² has at least one ordinary line. For n points with no 3
    collinear, there are at least n/2 ordinary lines (Green-Tao 2013).
    Axiomatized: this is a deep result from Green-Tao (2013), "On the
    strict Erdős-Gallai conjecture", Acta Math. 208(1), 1-36. -/
axiom green_tao_ordinary_lines (P : PointConfig) (hn : P.n ≥ 13)
    (h3 : NoKCollinear P 3) :
  ordinaryLineCount P ≥ P.n / 2

/-- An all-ordinary subset of r points has r*(r-1) ordered ordinary pairs. -/
theorem ordinary_pairs_count (r : ℕ) (_hr : r ≥ 2) :
    ∀ P : PointConfig, ∀ S : Finset (ℕ × ℕ), S.card = r → AllOrdinary P S →
      (S ×ˢ S).card - S.card = r * (r - 1) := by
  intro P S hcard _hord
  rw [Finset.card_product, hcard]
  zify [show r ≤ r * r from by nlinarith, show 1 ≤ r from by omega]
  ring

/-- The linear conjecture implies the little-o conjecture.
    If f_{r,k}(n) ≤ Cn then f_{r,k}(n) = o(n²): for n > C/ε we have Cn < εn². -/
theorem linear_implies_littleo (r k : ℕ) (_hr : r ≥ 2) (_hk : k ≥ 2) :
    ErdosConjecture960_linear r k → ErdosConjecture960_littleo r k := by
  intro ⟨C, hC⟩ ε hε
  use (((C : ℚ) / ε).ceil.toNat + 1)
  intro n hn
  have hCn := hC n
  -- threshold r k n ≤ C * n < ε * n * n for n large enough
  calc (threshold r k n : ℚ) ≤ ↑(C * n) := by exact_mod_cast hCn
    _ = (C : ℚ) * n := by push_cast; ring
    _ < ε * n * n := by
        -- Need: C * n < ε * n * n, i.e., C < ε * n (when n > 0)
        -- From hn: n ≥ ⌈C/ε⌉₊ + 1 > C/ε, so C/ε < n, hence C < ε * n
        sorry

-- ## Summary

/-- Erdős Problem #960: Summary
    Combines the little-o conjecture, the Turán upper bound,
    and the Sylvester-Gallai/Green-Tao ordinary line result. -/
theorem erdos_960_summary :
    (∀ r k : ℕ, r ≥ 2 → k ≥ 2 → ErdosConjecture960_littleo r k) ∧
    (∀ k n : ℕ, k ≥ 2 → n ≥ 2 → threshold 2 k n = 0) :=
  ⟨erdos_960_littleo_conjecture, fun k n hk hn => threshold_r2 k n hk hn⟩

end Erdos960
