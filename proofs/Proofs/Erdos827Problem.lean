/-!
# Erdős Problem #827: Distinct Circumradii in General Position

Let n_k be the minimal number such that any n_k points in general position
in ℝ² must contain a subset of k points where all C(k,3) triples determine
circles of distinct radii.

Erdős (1975) asked whether n_k exists. He claimed n_k ≤ k + 2·C(k-1,2)·C(k-1,3)
in 1978, but the proof contained errors. Martinez and Roldán-Pensado corrected
the argument and showed n_k ≪ k⁹.

The problem asks to determine n_k more precisely.

Reference: https://erdosproblems.com/827
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Points in General Position -/

/-- A point in the plane. -/
abbrev Point := ℝ × ℝ

/-- The squared distance between two points. -/
noncomputable def distSq (p q : Point) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Points are in general position: no three are collinear. -/
def GeneralPosition (S : Finset Point) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, ∀ r ∈ S,
    p ≠ q → q ≠ r → p ≠ r →
    (p.1 - r.1) * (q.2 - r.2) ≠ (q.1 - r.1) * (p.2 - r.2)

/-! ## Circumradius -/

/-- The squared circumradius of three non-collinear points.
    For the circumcircle of triangle pqr, R² = (|pq|²·|qr|²·|rp|²) / (16·Area²). -/
noncomputable def circumRadiusSq (p q r : Point) : ℝ :=
  let a2 := distSq p q
  let b2 := distSq q r
  let c2 := distSq r p
  let area2 := ((p.1 - r.1) * (q.2 - r.2) - (q.1 - r.1) * (p.2 - r.2)) ^ 2
  a2 * b2 * c2 / (4 * area2)

/-- A subset of k points has all distinct circumradii: every two triples
    determine circles of different radii. -/
def AllDistinctCircumradii (S : Finset Point) : Prop :=
  ∀ p₁ ∈ S, ∀ q₁ ∈ S, ∀ r₁ ∈ S,
  ∀ p₂ ∈ S, ∀ q₂ ∈ S, ∀ r₂ ∈ S,
    p₁ ≠ q₁ → q₁ ≠ r₁ → p₁ ≠ r₁ →
    p₂ ≠ q₂ → q₂ ≠ r₂ → p₂ ≠ r₂ →
    ({p₁, q₁, r₁} : Finset Point) ≠ {p₂, q₂, r₂} →
    circumRadiusSq p₁ q₁ r₁ ≠ circumRadiusSq p₂ q₂ r₂

/-! ## The Minimal Number n_k -/

/-- n_k exists: for each k, there is a threshold such that any set of
    that many points in general position contains a k-subset with all
    distinct circumradii. -/
def NkExists (k : ℕ) : Prop :=
  ∃ n : ℕ, ∀ S : Finset Point, GeneralPosition S → n ≤ S.card →
    ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T

/-- n_k is the minimal such number. -/
axiom minimalNk : ℕ → ℕ

/-- minimalNk k is a valid threshold. -/
axiom minimalNk_valid (k : ℕ) (hk : 3 ≤ k) :
    ∀ S : Finset Point, GeneralPosition S → minimalNk k ≤ S.card →
      ∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T

/-- minimalNk k is minimal: there exist configurations with minimalNk k - 1
    points that avoid k-subsets with all distinct circumradii. -/
axiom minimalNk_sharp (k : ℕ) (hk : 3 ≤ k) :
    ∃ S : Finset Point, GeneralPosition S ∧ S.card = minimalNk k - 1 ∧
      ¬∃ T : Finset Point, T ⊆ S ∧ T.card = k ∧ AllDistinctCircumradii T

/-! ## Main Problem -/

/-- Erdős Problem 827: Determine n_k. In particular, find the growth rate. -/
def ErdosProblem827 : Prop :=
  ∀ k : ℕ, 3 ≤ k → NkExists k

/-! ## Known Bounds -/

/-- Martinez-Roldán-Pensado: n_k ≪ k⁹. -/
def MartinezBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 3 ≤ k →
    (minimalNk k : ℝ) ≤ C * k ^ 9

/-- Erdős's original (incorrect) claimed bound: n_k ≤ k + 2·C(k-1,2)·C(k-1,3). -/
noncomputable def erdosClaimedBound (k : ℕ) : ℕ :=
  k + 2 * (k - 1).choose 2 * (k - 1).choose 3

/-- Martinez and Roldán-Pensado proved the corrected polynomial bound. -/
axiom martinez_roldan_pensado : MartinezBound

/-! ## Trivial Cases -/

/-- For k = 3, any 3 points in general position form a triangle with
    exactly one circumradius, so n_3 = 3. -/
axiom nk_three : minimalNk 3 = 3

/-- n_k is monotone non-decreasing. -/
axiom nk_monotone (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) (hk : 3 ≤ k₁) :
    minimalNk k₁ ≤ minimalNk k₂

/-- n_k ≥ k trivially. -/
axiom nk_ge_k (k : ℕ) (hk : 3 ≤ k) : k ≤ minimalNk k
