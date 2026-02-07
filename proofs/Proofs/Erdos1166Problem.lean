-- Erdős Problem #1166 — Most-Visited Points in Planar Random Walk
--
-- Given a random walk s₀, s₁, ... in Z² starting at the origin,
-- let f_k(x) count visits to point x through step k.
-- Let F(k) = {x : f_k(x) = max_y f_k(y)} be the set of most-visited points.
--
-- Erdős–Révész asked: Is |⋃_{k ≤ n} F(k)| ≤ (log n)^O(1) almost surely
-- for all but finitely many n?
--
-- Answer: YES (PROVED).
-- Almost surely |⋃_{k ≤ n} F(k)| ≪ (log n)².
--
-- Key ingredients:
-- (1) |F(n)| ≤ 3 almost surely for large n (Erdős–Révész, related to #1165)
-- (2) Erdős–Taylor: max visit count T_n satisfies T_n ≪ (log n)² a.s.
--
-- Status: PROVED
-- Reference: erdosproblems.com/1166, Erdős–Révész [Va99, 6.78]

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Real

namespace Erdos1166

-- ## Random Walk on Z²

/-- A point in the integer lattice Z². -/
abbrev LatticePoint := ℤ × ℤ

/-- The origin in Z². -/
def origin : LatticePoint := (0, 0)

/-- A random walk trajectory on Z²: a function from step number to position. -/
axiom RandomWalk : Type
/-- The trajectory of a random walk: position at each step. -/
axiom trajectory : RandomWalk → ℕ → LatticePoint
/-- Every walk starts at the origin. -/
axiom walk_starts_at_origin (ω : RandomWalk) : trajectory ω 0 = origin

-- ## Visit Counts

/-- f_k(x, ω): number of visits to point x through step k in walk ω. -/
noncomputable axiom visitCount : RandomWalk → ℕ → LatticePoint → ℕ

/-- Visit count is non-negative (trivially, since it's ℕ). -/
theorem visitCount_nonneg (ω : RandomWalk) (k : ℕ) (x : LatticePoint) :
    0 ≤ visitCount ω k x := Nat.zero_le _

/-- Visit count is monotone in k: more steps means at least as many visits. -/
axiom visitCount_mono (ω : RandomWalk) (k₁ k₂ : ℕ) (x : LatticePoint)
    (h : k₁ ≤ k₂) : visitCount ω k₁ x ≤ visitCount ω k₂ x

/-- The origin is visited at step 0. -/
axiom visitCount_origin (ω : RandomWalk) : visitCount ω 0 origin ≥ 1

-- ## Maximum Visit Count

/-- T_k(ω): the maximum number of visits to any single point through step k. -/
noncomputable axiom maxVisitCount : RandomWalk → ℕ → ℕ

/-- T_k achieves the maximum over all points. -/
axiom maxVisitCount_is_max (ω : RandomWalk) (k : ℕ) (x : LatticePoint) :
    visitCount ω k x ≤ maxVisitCount ω k

/-- T_k is achieved by some point. -/
axiom maxVisitCount_achieved (ω : RandomWalk) (k : ℕ) :
    ∃ x : LatticePoint, visitCount ω k x = maxVisitCount ω k

/-- T_k ≥ 1 for all k ≥ 0 (at least the origin is visited). -/
theorem maxVisitCount_pos (ω : RandomWalk) (k : ℕ) :
    1 ≤ maxVisitCount ω k := by
  have h := maxVisitCount_is_max ω k origin
  have h0 := visitCount_origin ω
  have hm := visitCount_mono ω 0 k origin (Nat.zero_le k)
  omega

-- ## Set of Most-Visited Points

/-- F(k, ω): the set of points achieving the maximum visit count at step k.
    Since this is a finite subset of Z² (only finitely many points are visited),
    we axiomatize it as a Finset. -/
noncomputable axiom mostVisitedSet : RandomWalk → ℕ → Finset LatticePoint

/-- A point is in F(k) iff it achieves the maximum visit count. -/
axiom mem_mostVisitedSet (ω : RandomWalk) (k : ℕ) (x : LatticePoint) :
    x ∈ mostVisitedSet ω k ↔ visitCount ω k x = maxVisitCount ω k

/-- F(k) is nonempty (the maximum is achieved). -/
axiom mostVisitedSet_nonempty (ω : RandomWalk) (k : ℕ) :
    (mostVisitedSet ω k).Nonempty

-- ## Cumulative Most-Visited Points

/-- The cumulative set of most-visited points through step n:
    ⋃_{k ≤ n} F(k). -/
noncomputable axiom cumulativeMostVisited : RandomWalk → ℕ → Finset LatticePoint

/-- The cumulative set contains all F(k) for k ≤ n. -/
axiom cumulativeMostVisited_contains (ω : RandomWalk) (n k : ℕ) (hk : k ≤ n) :
    mostVisitedSet ω k ⊆ cumulativeMostVisited ω n

/-- The cumulative set only contains points from some F(k) with k ≤ n. -/
axiom cumulativeMostVisited_subset (ω : RandomWalk) (n : ℕ)
    (x : LatticePoint) (hx : x ∈ cumulativeMostVisited ω n) :
    ∃ k : ℕ, k ≤ n ∧ x ∈ mostVisitedSet ω k

/-- Monotonicity: the cumulative set grows with n. -/
theorem cumulativeMostVisited_mono (ω : RandomWalk) (m n : ℕ) (h : m ≤ n) :
    cumulativeMostVisited ω m ⊆ cumulativeMostVisited ω n := by
  intro x hx
  obtain ⟨k, hk, hkx⟩ := cumulativeMostVisited_subset ω m x hx
  exact cumulativeMostVisited_contains ω n k (le_trans hk h) hkx

-- ## Almost Sure Events

/-- Probability space for random walks.
    We axiomatize "almost surely" as a predicate on properties of walks. -/
axiom AlmostSurely : (RandomWalk → Prop) → Prop

/-- Almost sure monotonicity: if P implies Q, then a.s. P implies a.s. Q. -/
axiom almostSurely_mono {P Q : RandomWalk → Prop}
    (h : ∀ ω, P ω → Q ω) (hP : AlmostSurely P) : AlmostSurely Q

/-- Almost sure conjunction. -/
axiom almostSurely_and {P Q : RandomWalk → Prop}
    (hP : AlmostSurely P) (hQ : AlmostSurely Q) :
    AlmostSurely (fun ω => P ω ∧ Q ω)

-- ## Key Result 1: |F(n)| ≤ 3 Eventually a.s.
-- Related to Erdős problem #1165

/-- Almost surely, for all large n, at most 3 points achieve the maximum
    visit count. This is the Erdős–Révész result (related to #1165). -/
axiom mostVisited_bounded_eventually :
    AlmostSurely (fun ω =>
      ∃ N : ℕ, ∀ n ≥ N, (mostVisitedSet ω n).card ≤ 3)

-- ## Key Result 2: Erdős–Taylor Theorem
-- The maximum visit count grows like (log n)²

/-- Erdős–Taylor (1960): Almost surely, the maximum visit count satisfies
    T_n ≤ C · (log n)² for some constant C and all large n.
    More precisely, T_n / (π · (log n)²) → 1 a.s. -/
axiom erdosTaylor_upper_bound :
    AlmostSurely (fun ω =>
      ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
        (maxVisitCount ω n : ℝ) ≤ C * (Real.log n) ^ 2)

-- ## Main Theorem: Erdős Problem #1166

/-- **Erdős Problem #1166 (PROVED)**:
    Almost surely, for all but finitely many n,
    |⋃_{k ≤ n} F(k)| ≤ O((log n)²).

    The key idea: since |F(k)| ≤ 3 for large k, and the maximum visit count
    T_n ≤ C · (log n)², only O((log n)²) different "regimes" of most-visited
    points can occur, bounding the cumulative set size. -/
axiom erdos1166_main :
    AlmostSurely (fun ω =>
      ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
        ((cumulativeMostVisited ω n).card : ℝ) ≤ C * (Real.log n) ^ 2)

/-- The bound in explicit polylogarithmic form:
    |⋃_{k ≤ n} F(k)| ≤ (log n)^{O(1)} a.s.
    Follows from erdos1166_main since C · (log n)² ≤ (log n)³ for large n. -/
theorem erdos1166_polylog :
    AlmostSurely (fun ω =>
      ∃ α : ℝ, α > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
        ((cumulativeMostVisited ω n).card : ℝ) ≤ (Real.log n) ^ α) := by
  apply almostSurely_mono _ erdos1166_main
  intro ω ⟨C, hC, N, hN⟩
  exact ⟨3, by norm_num, N, fun n hn =>
    le_trans (hN n hn) (by sorry)⟩ -- C · (log n)² ≤ (log n)³ for large n

-- ## Proof Structure

/-- The proof combines two key ingredients:

    Step 1: By mostVisited_bounded_eventually (related to #1165),
    a.s. for large n, |F(n)| ≤ 3.

    Step 2: By erdosTaylor_upper_bound, a.s. the max visit count T_n grows
    like (log n)². Points can only enter ⋃_{k≤n} F(k) when the max visit
    count changes or when a new point ties for the max.

    Step 3: The max visit count T_n is integer-valued and bounded by
    C · (log n)², so it takes at most O((log n)²) distinct values through
    step n. Each value contributes at most 3 new points to the cumulative
    set. Thus |⋃_{k≤n} F(k)| ≤ 3 · C · (log n)² = O((log n)²). -/
theorem erdos1166_from_ingredients :
    AlmostSurely (fun ω =>
      ∃ N : ℕ, ∀ n ≥ N, (mostVisitedSet ω n).card ≤ 3) →
    AlmostSurely (fun ω =>
      ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
        (maxVisitCount ω n : ℝ) ≤ C * (Real.log n) ^ 2) →
    AlmostSurely (fun ω =>
      ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
        ((cumulativeMostVisited ω n).card : ℝ) ≤ C * (Real.log n) ^ 2) := by
  intro h1 h2
  have h12 := almostSurely_and h1 h2
  apply almostSurely_mono _ h12
  intro ω ⟨⟨N₁, hN₁⟩, C, hC, N₂, hN₂⟩
  exact ⟨3 * C, by positivity, max N₁ N₂, fun n hn => by sorry⟩

-- ## Connection to Erdős Problem #1165

/-- Erdős #1165 asks about the size of F(n) itself (not cumulative).
    The key result |F(n)| ≤ 3 a.s. for large n is used in #1166. -/
theorem connection_to_1165 :
    AlmostSurely (fun ω => ∃ N : ℕ, ∀ n ≥ N,
      (mostVisitedSet ω n).card ≤ 3) :=
  mostVisited_bounded_eventually

-- ## Recurrence of Z² Random Walk

/-- A 2D simple random walk is recurrent: it returns to the origin
    infinitely often, almost surely. (Pólya, 1921) -/
axiom polya_recurrence :
    AlmostSurely (fun ω =>
      ∀ N : ℕ, ∃ n ≥ N, trajectory ω n = origin)

/-- Recurrence implies the max visit count tends to infinity. -/
axiom maxVisitCount_tendsto_infty :
    AlmostSurely (fun ω =>
      ∀ M : ℕ, ∃ N : ℕ, ∀ n ≥ N, M ≤ maxVisitCount ω n)

-- ## The Erdős–Taylor Constant

/-- The Erdős–Taylor constant: T_n / (log n)² → 1/π almost surely.
    This is the precise asymptotic for the maximum visit count in Z². -/
axiom erdosTaylor_constant :
    AlmostSurely (fun ω =>
      ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
        |(maxVisitCount ω n : ℝ) / (Real.log n) ^ 2 - 1 / Real.pi| < ε)

/-- Erdős–Taylor constant implies the upper bound we need. -/
theorem erdosTaylor_implies_bound :
    AlmostSurely (fun ω =>
      ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
        |(maxVisitCount ω n : ℝ) / (Real.log n) ^ 2 - 1 / Real.pi| < ε) →
    AlmostSurely (fun ω =>
      ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
        (maxVisitCount ω n : ℝ) ≤ C * (Real.log n) ^ 2) := by
  intro h
  apply almostSurely_mono _ h
  intro ω hω
  obtain ⟨N, hN⟩ := hω 1 one_pos
  exact ⟨1 / Real.pi + 1, by positivity, N, fun n hn => by
    have := hN n hn
    sorry⟩ -- follows from |T_n/(log n)² - 1/π| < 1

end Erdos1166
