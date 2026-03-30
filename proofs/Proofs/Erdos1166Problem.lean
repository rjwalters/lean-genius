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
-- Axioms: 3 declarations + 1 structure field = 4 (down from 12)
-- (AlmostSurely is now a def via Filter; mono/conjunction are Mathlib theorems)
-- Sorries: 0 (cumulative_card_bound proved via induction on interval length)
-- Eliminated: RandomWalk/trajectory/walk_starts_at_origin → structure,
--   erdosTaylor_upper_bound (implied by erdosTaylor_constant),
--   maxVisitCount_tendsto_infty (unused, follows from polya_recurrence),
--   polya_recurrence (orphan: not used by proof chain),
--   erdos1166_main (now theorem: follows from ingredients + Erdős-Taylor)
-- New: maxVisitCount_mono_succ, maxVisitCount_le_of_le, mostVisited_nesting,
--   mostVisited_nesting_range, biUnion_subset_last_of_constant_T,
--   mostVisited_subset_trajectory, erdos1166_from_ingredients (restructured)
-- Reference: erdosproblems.com/1166, Erdős–Révész [Va99, 6.78]

import Mathlib

open Real Filter

namespace Erdos1166

-- ## Random Walk on Z²

/-- A point in the integer lattice Z². -/
abbrev LatticePoint := ℤ × ℤ

/-- The origin in Z². -/
def origin : LatticePoint := (0, 0)

/-- A random walk on Z²: a trajectory (step → position) starting at the origin.
    Defined as a structure, not axiomatized. -/
structure RandomWalk where
  /-- The trajectory of a random walk: position at each step. -/
  trajectory : ℕ → LatticePoint
  /-- Every walk starts at the origin. -/
  starts_at_origin : trajectory 0 = origin

-- ## Visit Counts

/-- f_k(x, ω): number of visits to point x through step k in walk ω.
    Defined as |{n ∈ {0,...,k} | ω.trajectory n = x}|. -/
noncomputable def visitCount (ω : RandomWalk) (k : ℕ) (x : LatticePoint) : ℕ :=
  ((Finset.range (k + 1)).filter (fun n => ω.trajectory n = x)).card

/-- Visit count is non-negative (trivially, since it's ℕ). -/
theorem visitCount_nonneg (ω : RandomWalk) (k : ℕ) (x : LatticePoint) :
    0 ≤ visitCount ω k x := Nat.zero_le _

/-- Visit count is monotone in k: more steps means at least as many visits. -/
theorem visitCount_mono (ω : RandomWalk) (k₁ k₂ : ℕ) (x : LatticePoint)
    (h : k₁ ≤ k₂) : visitCount ω k₁ x ≤ visitCount ω k₂ x := by
  unfold visitCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (by
    intro n hn; simp only [Finset.mem_range] at *; omega))

/-- The origin is visited at step 0. -/
theorem visitCount_origin (ω : RandomWalk) : visitCount ω 0 origin ≥ 1 := by
  unfold visitCount
  exact Finset.card_pos.mpr ⟨0, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (by omega), ω.starts_at_origin⟩⟩

-- ## Maximum Visit Count

/-- T_k(ω): the maximum number of visits to any single point through step k.
    Defined as the supremum of visitCount over all visited points.
    Uses ℕ's OrderBot (⊥ = 0) for Finset.sup. -/
noncomputable def maxVisitCount (ω : RandomWalk) (k : ℕ) : ℕ :=
  ((Finset.range (k + 1)).image (ω.trajectory)).sup (visitCount ω k)

/-- T_k achieves the maximum over all points. -/
theorem maxVisitCount_is_max (ω : RandomWalk) (k : ℕ) (x : LatticePoint) :
    visitCount ω k x ≤ maxVisitCount ω k := by
  unfold maxVisitCount
  by_cases hx : x ∈ (Finset.range (k + 1)).image (ω.trajectory)
  · exact Finset.le_sup hx
  · -- x not visited in first k+1 steps: visitCount = 0
    suffices visitCount ω k x = 0 by omega
    unfold visitCount; rw [Finset.card_eq_zero, Finset.filter_eq_empty]
    intro n hn heq
    exact hx (Finset.mem_image.mpr ⟨n, hn, heq⟩)

/-- T_k is achieved by some point. -/
theorem maxVisitCount_achieved (ω : RandomWalk) (k : ℕ) :
    ∃ x : LatticePoint, visitCount ω k x = maxVisitCount ω k := by
  unfold maxVisitCount
  set visited := (Finset.range (k + 1)).image (ω.trajectory)
  have hne : visited.Nonempty :=
    ⟨ω.trajectory 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image visited (visitCount ω k) hne
  exact ⟨x, (le_antisymm (Finset.sup_le fun y hy => hmax y hy) (Finset.le_sup hx)).symm⟩

/-- T_k ≥ 1 for all k ≥ 0 (at least the origin is visited). -/
theorem maxVisitCount_pos (ω : RandomWalk) (k : ℕ) :
    1 ≤ maxVisitCount ω k := by
  have h := maxVisitCount_is_max ω k origin
  have h0 := visitCount_origin ω
  have hm := visitCount_mono ω 0 k origin (Nat.zero_le k)
  omega

/-- T_k is non-decreasing: maxVisitCount at step k ≤ maxVisitCount at step k+1. -/
theorem maxVisitCount_mono_succ (ω : RandomWalk) (k : ℕ) :
    maxVisitCount ω k ≤ maxVisitCount ω (k + 1) := by
  obtain ⟨x, hx⟩ := maxVisitCount_achieved ω k
  calc maxVisitCount ω k = visitCount ω k x := hx.symm
    _ ≤ visitCount ω (k + 1) x := visitCount_mono ω k (k + 1) x (Nat.le_succ k)
    _ ≤ maxVisitCount ω (k + 1) := maxVisitCount_is_max ω (k + 1) x

/-- T is monotone: a ≤ b → T_a ≤ T_b. -/
theorem maxVisitCount_le_of_le (ω : RandomWalk) {a b : ℕ} (h : a ≤ b) :
    maxVisitCount ω a ≤ maxVisitCount ω b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact le_rfl
  | succ n ih => exact le_trans ih (maxVisitCount_mono_succ ω (a + n))

-- ## Set of Most-Visited Points

/-- F(k, ω): the set of visited points achieving the maximum visit count.
    Defined as the filter of visited points where visitCount equals maxVisitCount. -/
noncomputable def mostVisitedSet (ω : RandomWalk) (k : ℕ) : Finset LatticePoint :=
  ((Finset.range (k + 1)).image (ω.trajectory)).filter
    (fun x => visitCount ω k x = maxVisitCount ω k)

/-- A point is in F(k) iff it achieves the maximum visit count. -/
theorem mem_mostVisitedSet (ω : RandomWalk) (k : ℕ) (x : LatticePoint) :
    x ∈ mostVisitedSet ω k ↔ visitCount ω k x = maxVisitCount ω k := by
  unfold mostVisitedSet
  constructor
  · exact fun hx => (Finset.mem_filter.mp hx).2
  · intro heq
    apply Finset.mem_filter.mpr
    refine ⟨?_, heq⟩
    -- x must be visited since visitCount > 0
    have hpos : 0 < visitCount ω k x := heq ▸ maxVisitCount_pos ω k
    unfold visitCount at hpos
    obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
    have := Finset.mem_filter.mp hn
    exact Finset.mem_image.mpr ⟨n, this.1, this.2⟩

/-- F(k) is nonempty (the maximum is achieved). -/
theorem mostVisitedSet_nonempty (ω : RandomWalk) (k : ℕ) :
    (mostVisitedSet ω k).Nonempty := by
  obtain ⟨x, hx⟩ := maxVisitCount_achieved ω k
  exact ⟨x, (mem_mostVisitedSet ω k x).mpr hx⟩

/-- If T_k = T_{k+1}, then F(k) ⊆ F(k+1). When the maximum visit count
    doesn't change, all previous maximizers remain maximizers. -/
theorem mostVisited_nesting (ω : RandomWalk) (k : ℕ)
    (hT : maxVisitCount ω k = maxVisitCount ω (k + 1)) :
    mostVisitedSet ω k ⊆ mostVisitedSet ω (k + 1) := by
  intro x hx
  rw [mem_mostVisitedSet] at hx ⊢
  have h1 := maxVisitCount_is_max ω (k + 1) x
  have h2 := visitCount_mono ω k (k + 1) x (Nat.le_succ k)
  omega

/-- If T is constant on [a, b], then F(a) ⊆ F(b). -/
theorem mostVisited_nesting_range (ω : RandomWalk) (a b : ℕ) (hab : a ≤ b)
    (hT : maxVisitCount ω a = maxVisitCount ω b) :
    mostVisitedSet ω a ⊆ mostVisitedSet ω b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction d with
  | zero => exact Subset.rfl
  | succ n ih =>
    have hTn : maxVisitCount ω a = maxVisitCount ω (a + n) := by
      apply le_antisymm (maxVisitCount_le_of_le ω (Nat.le_add_right a n))
      have := maxVisitCount_le_of_le ω (show a + n ≤ a + (n + 1) by omega)
      omega
    exact Subset.trans (ih hTn) (mostVisited_nesting ω (a + n) (by
      apply le_antisymm (maxVisitCount_mono_succ ω (a + n))
      have := maxVisitCount_le_of_le ω (show a ≤ a + n by omega)
      omega))

-- ## Cumulative Most-Visited Points

/-- The cumulative set of most-visited points through step n:
    ⋃_{k ≤ n} F(k). Defined as the biUnion of F(k) over k ∈ {0, ..., n}. -/
noncomputable def cumulativeMostVisited (ω : RandomWalk) (n : ℕ) :
    Finset LatticePoint :=
  (Finset.range (n + 1)).biUnion (mostVisitedSet ω)

/-- The cumulative set contains all F(k) for k ≤ n. -/
theorem cumulativeMostVisited_contains (ω : RandomWalk) (n k : ℕ) (hk : k ≤ n) :
    mostVisitedSet ω k ⊆ cumulativeMostVisited ω n := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (by omega), hx⟩

/-- The cumulative set only contains points from some F(k) with k ≤ n. -/
theorem cumulativeMostVisited_subset (ω : RandomWalk) (n : ℕ)
    (x : LatticePoint) (hx : x ∈ cumulativeMostVisited ω n) :
    ∃ k : ℕ, k ≤ n ∧ x ∈ mostVisitedSet ω k := by
  obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
  exact ⟨k, by omega, hxk⟩

/-- Monotonicity: the cumulative set grows with n. -/
theorem cumulativeMostVisited_mono (ω : RandomWalk) (m n : ℕ) (h : m ≤ n) :
    cumulativeMostVisited ω m ⊆ cumulativeMostVisited ω n := by
  intro x hx
  obtain ⟨k, hk, hkx⟩ := cumulativeMostVisited_subset ω m x hx
  exact cumulativeMostVisited_contains ω n k (le_trans hk h) hkx

-- ## Nesting-Based Cumulative Bounds

/-- When T is constant on [a, b], the biUnion of F(k) is contained in F(b).
    This is key: within a "regime" where the max visit count doesn't change,
    the F sets are nested, so their union equals the last one. -/
theorem biUnion_subset_last_of_constant_T (ω : RandomWalk) (a b : ℕ) (hab : a ≤ b)
    (hT : maxVisitCount ω a = maxVisitCount ω b) :
    (Finset.Ico a (b + 1)).biUnion (mostVisitedSet ω) ⊆ mostVisitedSet ω b := by
  intro x hx
  obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
  have hak : a ≤ k := (Finset.mem_Ico.mp hk).1
  have hkb : k ≤ b := by omega
  have hTk : maxVisitCount ω k = maxVisitCount ω b := by
    apply le_antisymm (maxVisitCount_le_of_le ω hkb)
    calc maxVisitCount ω b = maxVisitCount ω a := hT.symm
      _ ≤ maxVisitCount ω k := maxVisitCount_le_of_le ω hak
  exact mostVisited_nesting_range ω k b hkb hTk hxk

/-- Every point in mostVisitedSet ω k is a visited point (in the trajectory image). -/
theorem mostVisited_subset_trajectory (ω : RandomWalk) (k : ℕ) :
    mostVisitedSet ω k ⊆ (Finset.range (k + 1)).image ω.trajectory := by
  intro x hx
  exact (Finset.mem_filter.mp (by unfold mostVisitedSet at hx; exact hx)).1

/-- Counting bound (nesting argument): when |F(k)| ≤ 3 throughout [a, b],
    the cumulative set has card ≤ 3 * (T_b - T_a + 1).

    Proof sketch: Group steps by T-value. Within each constant-T interval,
    F sets are nested (by mostVisited_nesting), so the union equals the last F.
    Each group contributes ≤ 3 points. The number of groups ≤ T_b - T_a + 1.

    This is the core of the Erdős #1166 counting argument. -/
theorem cumulative_card_bound (ω : RandomWalk) (a b : ℕ) (hab : a ≤ b)
    (hcard : ∀ k, a ≤ k → k ≤ b → (mostVisitedSet ω k).card ≤ 3) :
    ((Finset.Ico a (b + 1)).biUnion (mostVisitedSet ω)).card ≤
      3 * (maxVisitCount ω b - maxVisitCount ω a + 1) := by
  -- Induction on interval length b - a. When T is constant, use nesting.
  -- When T increases, split at a+1: if T_{a+1}=T_a, F(a) is absorbed by nesting;
  -- if T_{a+1}>T_a, union bound + IH gives the result.
  suffices ∀ (len a b : ℕ), b - a = len → a ≤ b →
      (∀ k, a ≤ k → k ≤ b → (mostVisitedSet ω k).card ≤ 3) →
      ((Finset.Ico a (b + 1)).biUnion (mostVisitedSet ω)).card ≤
        3 * (maxVisitCount ω b - maxVisitCount ω a + 1) from
    this (b - a) a b rfl hab hcard
  intro len
  induction len with
  | zero =>
    intro a b hlen hab hcard
    have hab' : a = b := by omega
    subst hab'
    have hIco : Finset.Ico a (a + 1) = {a} := by
      ext k; simp only [Finset.mem_Ico, Finset.mem_singleton]; omega
    rw [hIco, Finset.biUnion_singleton]
    have := hcard a le_rfl le_rfl; omega
  | succ n ih =>
    intro a b hlen hab hcard
    have ha_lt_b : a < b := by omega
    by_cases hT : maxVisitCount ω a = maxVisitCount ω b
    · -- T constant on [a, b]: biUnion ⊆ F(b) by nesting
      calc ((Finset.Ico a (b + 1)).biUnion (mostVisitedSet ω)).card
          ≤ (mostVisitedSet ω b).card :=
            Finset.card_le_card (biUnion_subset_last_of_constant_T ω a b hab hT)
        _ ≤ 3 := hcard b hab le_rfl
        _ ≤ 3 * (maxVisitCount ω b - maxVisitCount ω a + 1) := by omega
    · -- T increases: split Ico(a, b+1) = {a} ∪ Ico(a+1, b+1)
      have hlt : maxVisitCount ω a < maxVisitCount ω b :=
        lt_of_le_of_ne (maxVisitCount_le_of_le ω hab) hT
      have hIco : Finset.Ico a (b + 1) = {a} ∪ Finset.Ico (a + 1) (b + 1) := by
        ext k; simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]; omega
      rw [hIco, Finset.biUnion_union, Finset.biUnion_singleton]
      -- IH on [a+1, b]
      have ih_ab : ((Finset.Ico (a + 1) (b + 1)).biUnion (mostVisitedSet ω)).card ≤
          3 * (maxVisitCount ω b - maxVisitCount ω (a + 1) + 1) :=
        ih (a + 1) b (by omega) (by omega) (fun k hak hkb => hcard k (by omega) hkb)
      by_cases hTstep : maxVisitCount ω a = maxVisitCount ω (a + 1)
      · -- T constant at first step: F(a) ⊆ F(a+1) ⊆ biUnion[a+1,b]
        have hFa_sub : mostVisitedSet ω a ⊆
            (Finset.Ico (a + 1) (b + 1)).biUnion (mostVisitedSet ω) := by
          intro x hx
          have hx' := mostVisited_nesting ω a hTstep hx
          exact Finset.mem_biUnion.mpr ⟨a + 1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, hx'⟩
        rw [sup_eq_right.mpr hFa_sub]
        calc ((Finset.Ico (a + 1) (b + 1)).biUnion (mostVisitedSet ω)).card
            ≤ 3 * (maxVisitCount ω b - maxVisitCount ω (a + 1) + 1) := ih_ab
          _ = 3 * (maxVisitCount ω b - maxVisitCount ω a + 1) := by omega
      · -- T increases at first step: union bound
        have hTinc : maxVisitCount ω a < maxVisitCount ω (a + 1) :=
          lt_of_le_of_ne (maxVisitCount_mono_succ ω a) hTstep
        have hTa1b : maxVisitCount ω (a + 1) ≤ maxVisitCount ω b :=
          maxVisitCount_le_of_le ω (by omega)
        calc (mostVisitedSet ω a ∪
                (Finset.Ico (a + 1) (b + 1)).biUnion (mostVisitedSet ω)).card
            ≤ (mostVisitedSet ω a).card +
              ((Finset.Ico (a + 1) (b + 1)).biUnion (mostVisitedSet ω)).card :=
              Finset.card_union_le _ _
          _ ≤ 3 + 3 * (maxVisitCount ω b - maxVisitCount ω (a + 1) + 1) :=
              Nat.add_le_add (hcard a le_rfl (by omega)) ih_ab
          _ ≤ 3 * (maxVisitCount ω b - maxVisitCount ω a + 1) := by omega

-- ## Almost Sure Events
-- Modeled via Mathlib's Filter theory: a.s. events are those that hold
-- "eventually" in a filter on the space of random walks. The filter
-- captures the measure-zero complement structure of probability theory.
-- Monotonicity and conjunction are derived from Filter axioms (Mathlib).

/-- The probability filter on random walks: axiomatizes the notion of
    "measure-one" sets without specifying the full measure space.
    Almost-sure events are exactly those in this filter. -/
axiom asProbFilter : Filter RandomWalk

/-- P holds almost surely: P is true for "almost all" random walks.
    Defined as Filter.Eventually, giving us mono/conjunction for free. -/
def AlmostSurely (P : RandomWalk → Prop) : Prop := ∀ᶠ ω in asProbFilter, P ω

/-- Almost sure monotonicity: derived from Filter.Eventually.mono. -/
theorem almostSurely_mono {P Q : RandomWalk → Prop}
    (h : ∀ ω, P ω → Q ω) (hP : AlmostSurely P) : AlmostSurely Q :=
  hP.mono h

/-- Almost sure conjunction: derived from Filter.inter_mem. -/
theorem almostSurely_and {P Q : RandomWalk → Prop}
    (hP : AlmostSurely P) (hQ : AlmostSurely Q) :
    AlmostSurely (fun ω => P ω ∧ Q ω) :=
  Filter.inter_mem hP hQ

-- ## Key Result 1: |F(n)| ≤ 3 Eventually a.s.
-- Related to Erdős problem #1165

/-- Almost surely, for all large n, at most 3 points achieve the maximum
    visit count. This is the Erdős–Révész result (related to #1165). -/
axiom mostVisited_bounded_eventually :
    AlmostSurely (fun ω =>
      ∃ N : ℕ, ∀ n ≥ N, (mostVisitedSet ω n).card ≤ 3)

-- ## Key Result 2: Erdős–Taylor Theorem
-- The maximum visit count grows like (log n)²
-- [Formerly axiom erdosTaylor_upper_bound — now derived from
--  erdosTaylor_constant via erdosTaylor_implies_bound below.]

-- ## Main Theorem: Erdős Problem #1166

/-- **Erdős Problem #1166 (PROVED)**:
    Almost surely, for all but finitely many n,
    |⋃_{k ≤ n} F(k)| ≤ O((log n)²).

    The key idea: since |F(k)| ≤ 3 for large k, and the maximum visit count
    T_n ≤ C · (log n)², only O((log n)²) different "regimes" of most-visited
    points can occur, bounding the cumulative set size. -/
theorem erdos1166_main :
    AlmostSurely (fun ω =>
      ∃ C : ℝ, C > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
        ((cumulativeMostVisited ω n).card : ℝ) ≤ C * (Real.log n) ^ 2) :=
  erdos1166_from_ingredients mostVisited_bounded_eventually
    (erdosTaylor_implies_bound erdosTaylor_constant)

/-- The bound in explicit polylogarithmic form:
    |⋃_{k ≤ n} F(k)| ≤ (log n)^{O(1)} a.s.
    Follows from erdos1166_main since C · (log n)² ≤ (log n)³ for large n. -/
theorem erdos1166_polylog :
    AlmostSurely (fun ω =>
      ∃ α : ℝ, α > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
        ((cumulativeMostVisited ω n).card : ℝ) ≤ (Real.log n) ^ α) := by
  apply almostSurely_mono _ erdos1166_main
  intro ω ⟨C, hC, N, hN⟩
  -- Choose N' large enough that log n ≥ C for all n ≥ N'
  -- Then C * (log n)² ≤ (log n)³ = (log n)^3
  refine ⟨3, by norm_num, max N (Nat.ceil (Real.exp C) + 1), fun n hn => ?_⟩
  have hN' : N ≤ n := (le_max_left _ _).trans hn
  have hexp : Nat.ceil (Real.exp C) + 1 ≤ n := (le_max_right _ _).trans hn
  have hn_large : (Real.exp C : ℝ) < n := by
    calc Real.exp C ≤ ↑(Nat.ceil (Real.exp C)) := Nat.le_ceil _
      _ < ↑(Nat.ceil (Real.exp C) + 1) := by exact_mod_cast Nat.lt_succ_of_le le_rfl
      _ ≤ (n : ℝ) := by exact_mod_cast hexp
  have hlog_ge : C ≤ Real.log n := by
    rw [← Real.log_exp C]
    exact Real.log_le_log (Real.exp_pos C) (le_of_lt hn_large)
  have hlog_pos : 0 < Real.log n :=
    lt_of_lt_of_le (by positivity) hlog_ge
  calc ((cumulativeMostVisited ω n).card : ℝ) ≤ C * (Real.log ↑n) ^ 2 := hN n hN'
    _ ≤ Real.log ↑n * (Real.log ↑n) ^ 2 := by nlinarith [sq_nonneg (Real.log (n : ℝ))]
    _ = (Real.log ↑n) ^ 3 := by ring

-- ## Proof Structure

/-- The proof combines two key ingredients:

    Step 1: By mostVisited_bounded_eventually (related to #1165),
    a.s. for large n, |F(n)| ≤ 3.

    Step 2: By erdosTaylor_constant (via erdosTaylor_implies_bound), a.s. T_n grows
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
  -- Strategy: split cumulative set into early (k < N₁) and late (k ≥ N₁) parts.
  -- Early: ≤ N₁ points (all visited points before step N₁).
  -- Late: ≤ 3*(T_n - T_{N₁} + 1) ≤ 3*(T_n + 1) by nesting (cumulative_card_bound).
  -- Total ≤ N₁ + 3*T_n + 3 ≤ N₁ + 3*C*(log n)² + 3.
  -- Choose threshold large enough that N₁ + 3 ≤ (log n)², giving total ≤ (3*C+1)*(log n)².
  let N₃ := Nat.ceil (Real.exp (↑N₁ + 4)) + 1
  refine ⟨3 * C + 1, by linarith, max (max N₁ N₂) N₃, fun n hn => ?_⟩
  have hN₁n : N₁ ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hn)
  have hN₂n : N₂ ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hn)
  have hN₃n : N₃ ≤ n := le_trans (le_max_right _ _) hn
  -- T_n is bounded by C * (log n)²
  have hTn : (maxVisitCount ω n : ℝ) ≤ C * (Real.log ↑n) ^ 2 := hN₂ n hN₂n
  -- n > exp(N₁ + 4), so log n > N₁ + 4, so (log n)² > (N₁ + 4)² ≥ N₁ + 3
  have hn_large : (Real.exp (↑N₁ + 4) : ℝ) < ↑n := by
    calc Real.exp (↑N₁ + 4) ≤ ↑(Nat.ceil (Real.exp (↑N₁ + 4))) := Nat.le_ceil _
      _ < ↑(Nat.ceil (Real.exp (↑N₁ + 4)) + 1) := by exact_mod_cast Nat.lt_succ_of_le le_rfl
      _ ≤ (n : ℝ) := by exact_mod_cast hN₃n
  have hlog_large : (↑N₁ + 4 : ℝ) < Real.log ↑n := by
    rw [← Real.log_exp (↑N₁ + 4)]
    exact Real.log_lt_log (Real.exp_pos _) hn_large
  have hlog_pos : (0 : ℝ) < Real.log ↑n := by linarith
  -- (log n)² ≥ N₁ + 4 > N₁ + 3
  have hlog_sq_ge : (↑N₁ + 3 : ℝ) ≤ (Real.log ↑n) ^ 2 := by
    have h1 : (1 : ℝ) ≤ ↑N₁ + 4 := by positivity
    nlinarith [sq_nonneg (Real.log (↑n : ℝ) - 1)]
  -- The cumulative set card bound (combines early + late parts)
  -- This is the key step using the nesting argument infrastructure
  have hcard_bound : ((cumulativeMostVisited ω n).card : ℝ) ≤
      ↑N₁ + 3 * ↑(maxVisitCount ω n) + 3 := by
    -- Suffices to prove in ℕ: card ≤ N₁ + 3*(T_n + 1)
    suffices hnat : (cumulativeMostVisited ω n).card ≤ N₁ + 3 * (maxVisitCount ω n + 1) by
      push_cast [Nat.cast_le] at hnat ⊢; linarith
    -- Split range(n+1) = range(N₁) ∪ Ico(N₁, n+1)
    have hrange : Finset.range (n + 1) = Finset.range N₁ ∪ Finset.Ico N₁ (n + 1) := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
      exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le N₁) (by omega)).symm
    unfold cumulativeMostVisited
    rw [hrange, Finset.biUnion_union]
    -- Card of union ≤ sum of cards
    calc ((Finset.range N₁).biUnion (mostVisitedSet ω) ∪
            (Finset.Ico N₁ (n + 1)).biUnion (mostVisitedSet ω)).card
        ≤ ((Finset.range N₁).biUnion (mostVisitedSet ω)).card +
          ((Finset.Ico N₁ (n + 1)).biUnion (mostVisitedSet ω)).card :=
          Finset.card_union_le _ _
      _ ≤ N₁ + 3 * (maxVisitCount ω n - maxVisitCount ω N₁ + 1) := by
          apply Nat.add_le_add
          -- Early: every point in F(k) for k < N₁ is trajectory(j) for some j < N₁
          · calc ((Finset.range N₁).biUnion (mostVisitedSet ω)).card
                ≤ ((Finset.range N₁).image ω.trajectory).card := by
                  apply Finset.card_le_card; intro x hx
                  obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
                  have hxv := mostVisited_subset_trajectory ω k hxk
                  obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hxv
                  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), hjx⟩
              _ ≤ (Finset.range N₁).card := Finset.card_image_le
              _ = N₁ := Finset.card_range N₁
          -- Late: by cumulative_card_bound (nesting argument)
          · exact cumulative_card_bound ω N₁ n hN₁n (fun k hak hkn => hN₁ k hak)
      _ ≤ N₁ + 3 * (maxVisitCount ω n + 1) := by
          apply Nat.add_le_add_left; apply Nat.mul_le_mul_left; omega
  -- Final assembly: N₁ + 3*T_n + 3 ≤ (3*C+1)*(log n)²
  calc ((cumulativeMostVisited ω n).card : ℝ)
      ≤ ↑N₁ + 3 * ↑(maxVisitCount ω n) + 3 := hcard_bound
    _ ≤ ↑N₁ + 3 * (C * (Real.log ↑n) ^ 2) + 3 := by linarith [hTn]
    _ = (↑N₁ + 3) + 3 * C * (Real.log ↑n) ^ 2 := by ring
    _ ≤ (Real.log ↑n) ^ 2 + 3 * C * (Real.log ↑n) ^ 2 := by linarith [hlog_sq_ge]
    _ = (3 * C + 1) * (Real.log ↑n) ^ 2 := by ring

-- ## Connection to Erdős Problem #1165

/-- Erdős #1165 asks about the size of F(n) itself (not cumulative).
    The key result |F(n)| ≤ 3 a.s. for large n is used in #1166. -/
theorem connection_to_1165 :
    AlmostSurely (fun ω => ∃ N : ℕ, ∀ n ≥ N,
      (mostVisitedSet ω n).card ≤ 3) :=
  mostVisited_bounded_eventually

-- [Pólya recurrence and maxVisitCount_tendsto_infty removed as orphan axioms:
--  not used by the main proof chain. Pólya's theorem (Z² walk is recurrent)
--  would imply max visit count → ∞, but the Erdős–Taylor constant axiom
--  already provides the quantitative bound we need.]

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
  refine ⟨1 / Real.pi + 1, by positivity, max N 2, fun n hn => ?_⟩
  have hN' : N ≤ n := (le_max_left N 2).trans hn
  have hn2 : 2 ≤ n := (le_max_right N 2).trans hn
  have h_abs := hN n hN'
  -- From |T/(log n)² - 1/π| < 1, extract upper bound
  have h_upper := (abs_lt.mp h_abs).2
  -- h_upper : T/(log n)² - 1/π < 1, i.e., T/(log n)² < 1/π + 1
  have hlog_pos : (0 : ℝ) < Real.log n :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlog2_pos : (0 : ℝ) < (Real.log ↑n) ^ 2 := sq_pos_of_pos hlog_pos
  -- T/(log n)² < 1/π + 1, multiply by (log n)²
  have h1 : (maxVisitCount ω n : ℝ) / (Real.log ↑n) ^ 2 < 1 / Real.pi + 1 := by
    linarith
  have h2 : (maxVisitCount ω n : ℝ) < (1 / Real.pi + 1) * (Real.log ↑n) ^ 2 :=
    (div_lt_iff hlog2_pos).mp h1
  linarith

end Erdos1166
