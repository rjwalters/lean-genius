/-
  Generalizing the Slot-Based Birthday Recurrence to k-Way Coincidences
  Open Question: birthday-problem-oq-03-oq-01-oq-01-oq-02

  The parent (birthday-problem-oq-03-oq-01-oq-01) optimizes the count of valid
  k=3 birthday assignments — functions f : Fin n → Fin d whose fibers all have
  size ≤ 2 (no 3 people share a day) — via a two-state slot recurrence

      R(n+1, e, s) = e·R(n, e−1, s+1) + s·R(n, e, s−1),   R(0, e, s) = 1,

  where e = #empty days, s = #single-occupied days. It poses the open question:

      "Generalize to k-way coincidences: define R_k tracking the multiplicity
       histogram (e_0, e_1, …, e_{k-1})."

  ## This file

  We define the general histogram recurrence `Rk` for an arbitrary maximum
  per-day occupancy `M = k − 1` (avoiding a k-way coincidence ⇔ every day holds
  ≤ M people). The state is a list `c : List ℕ` with `c.getD i 0` = number of
  *live* days currently at occupancy level `i`, for `i = 0,…,M−1`; a day at
  level `M−1` that receives one more person becomes *full* and leaves the state.

      Rk 0 c        = 1
      Rk (n+1) c    = ∑_{i < c.length} c.getD i 0 · Rk n (transition c i)

  where `transition c i` decrements the count at level `i` and (if `i+1 < M`)
  increments the count at level `i+1`.

  ## Results (all verified, 0 sorries)

  * `Rk_eq_Rpar` : for width M=2 the general recurrence is *definitionally the
    parent's k=3 recurrence*: `Rk n [e, s] = Rpar n e s`. So the generalization
    is faithful — it specializes back exactly.
  * `birthdayCountK_eq_Rpar_k3` : `birthdayCountK n d 3 = Rpar n d 0`, recovering
    the parent's `birthdayCount3` from the general formula.
  * `transition_length`, `Rk_nil_succ` : structural invariants (the histogram
    width is preserved; no live slots ⇒ nothing can be placed).
  * Concrete `decide`-checked counts for k=2 (injective placements / descending
    factorial), the parent's k=3 values, and the **new** k=4 counts (max 3 per
    day), plus a cross-k monotonicity check (more permissive k ⇒ larger count).

  Axioms: 0. Sorries: 0. All concrete checks use kernel `decide` (no
  `native_decide`, so no `Lean.ofReduceBool` dependency).
-/

import Mathlib

namespace BirthdayKway

open Finset

-- ============================================================
-- SECTION I: The General Histogram Recurrence
-- ============================================================

/-- One placement step on the multiplicity histogram `c` at occupancy level `i`:
    one day at level `i` receives a person, so the count at level `i` drops by 1
    and (when `i+1` is still a live level, i.e. `i+1 < c.length`) the count at
    level `i+1` rises by 1. A day at the top live level `c.length − 1` becomes
    full and simply leaves (no level gains it). Nat subtraction is safe: the
    recurrence multiplies by `c.getD i 0`, killing the step when level `i` is
    empty. -/
def transition (c : List ℕ) (i : ℕ) : List ℕ :=
  let c' := c.set i (c.getD i 0 - 1)
  if i + 1 < c.length then c'.set (i + 1) (c'.getD (i + 1) 0 + 1) else c'

/-- `Rk n c` = number of ways to place `n` more people into the live day-slots
    described by the histogram `c` (avoiding any day exceeding occupancy
    `c.length`). The `k`-way generalization of the parent's two-state `R`. -/
def Rk : ℕ → List ℕ → ℕ
  | 0, _ => 1
  | n + 1, c => ∑ i ∈ Finset.range c.length, c.getD i 0 * Rk n (transition c i)

@[simp] theorem Rk_zero (c : List ℕ) : Rk 0 c = 1 := rfl

theorem Rk_succ (n : ℕ) (c : List ℕ) :
    Rk (n + 1) c = ∑ i ∈ Finset.range c.length, c.getD i 0 * Rk n (transition c i) :=
  rfl

/-- The histogram width (maximum occupancy `M`) is invariant under a step. -/
theorem transition_length (c : List ℕ) (i : ℕ) :
    (transition c i).length = c.length := by
  unfold transition
  split <;> simp [List.length_set]

/-- With no live slots, no one can be placed. -/
@[simp] theorem Rk_nil_succ (n : ℕ) : Rk (n + 1) [] = 0 := by
  rw [Rk_succ]; simp

-- ============================================================
-- SECTION II: Faithful Specialization to the Parent's k=3 Recurrence
-- ============================================================

/-- The parent's two-state k=3 recurrence (restated; the parent file
    `BirthdayProblemOQ03OQ01OQ01.lean` is imported here only conceptually). -/
def Rpar : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, e, s => e * Rpar n (e - 1) (s + 1) + s * Rpar n e (s - 1)

/-- Step at level 0 of a width-2 histogram: an empty day becomes single. -/
@[simp] theorem transition_pair_zero (e s : ℕ) :
    transition [e, s] 0 = [e - 1, s + 1] := rfl

/-- Step at level 1 of a width-2 histogram: a single day fills and leaves. -/
@[simp] theorem transition_pair_one (e s : ℕ) :
    transition [e, s] 1 = [e, s - 1] := rfl

/-- **Faithful generalization.** On width-2 histograms the general recurrence
    `Rk` is exactly the parent's k=3 recurrence `Rpar`. -/
theorem Rk_eq_Rpar (n e s : ℕ) : Rk n [e, s] = Rpar n e s := by
  induction n generalizing e s with
  | zero => rfl
  | succ n ih =>
    rw [Rk_succ]
    show (∑ i ∈ Finset.range 2, ([e, s].getD i 0) * Rk n (transition [e, s] i))
        = Rpar (n + 1) e s
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [transition_pair_zero, transition_pair_one,
      List.getD_cons_zero, List.getD_cons_succ]
    rw [ih, ih]
    rfl

-- ============================================================
-- SECTION III: The Unified k-Way Birthday Count
-- ============================================================

/-- Number of functions `f : Fin n → Fin d` with every fiber of size `< k`
    (no `k` people share a day), via the general histogram recurrence. The
    start state has all `d` days empty: width `M = k − 1`, list
    `d :: replicate (k−2) 0`. Recovers the injective count for `k = 2`, the
    parent's `birthdayCount3` for `k = 3`, and new counts for `k ≥ 4`. -/
def birthdayCountK (n d k : ℕ) : ℕ := Rk n (d :: List.replicate (k - 2) 0)

/-- For `k = 3`, the unified count is the parent's two-state count `Rpar n d 0`
    (= `birthdayCount3 n d`). -/
theorem birthdayCountK_eq_Rpar_k3 (n d : ℕ) :
    birthdayCountK n d 3 = Rpar n d 0 := by
  show Rk n [d, 0] = Rpar n d 0
  exact Rk_eq_Rpar n d 0

-- ============================================================
-- SECTION IV: k = 2 — Injective Placements (Descending Factorial)
-- ============================================================

/-- For `k = 2` (all birthdays distinct) the count is the descending factorial
    `d·(d−1)···(d−n+1)`: injective functions `Fin n ↪ Fin d`. -/
theorem k2_inj_5_0 : birthdayCountK 0 5 2 = 1 := by decide
theorem k2_inj_5_2 : birthdayCountK 2 5 2 = 20 := by decide       -- 5·4
theorem k2_inj_5_5 : birthdayCountK 5 5 2 = 120 := by decide      -- 5!
theorem k2_inj_5_6 : birthdayCountK 6 5 2 = 0 := by decide        -- > d, none injective

-- ============================================================
-- SECTION V: k = 3 — Recovering the Parent's Counts
-- ============================================================

theorem k3_recovers_24 : birthdayCountK 3 3 3 = 24 := by decide
theorem k3_recovers_90 : birthdayCountK 6 3 3 = 90 := by decide
theorem k3_over_capacity : birthdayCountK 7 3 3 = 0 := by decide

-- ============================================================
-- SECTION VI: k = 4 — New Counts (No Day Holds 4 People, max 3/day)
-- ============================================================

/-- For `d = 2` days with at most 3 people per day: all `2^n` assignments are
    valid while `n ≤ 3`, then the count drops below `2^n`. -/
theorem k4_d2_n3 : birthdayCountK 3 2 4 = 8 := by decide          -- = 2^3, all valid
theorem k4_d2_n4 : birthdayCountK 4 2 4 = 14 := by decide         -- 16 − 2 (the two 4-of-a-kind)
theorem k4_d2_n5 : birthdayCountK 5 2 4 = 20 := by decide
theorem k4_d2_n6 : birthdayCountK 6 2 4 = 20 := by decide         -- = capacity 2·3
theorem k4_d2_over_capacity : birthdayCountK 7 2 4 = 0 := by decide  -- 7 > 2·3

/-- For `d = 3` days, max 3 per day: a genuinely new value (the parent never
    counted 4-way avoidance). -/
theorem k4_d3_n4 : birthdayCountK 4 3 4 = 78 := by decide
theorem k4_d3_n5 : birthdayCountK 5 3 4 = 210 := by decide

-- ============================================================
-- SECTION VII: Monotonicity in k (Permissiveness)
-- ============================================================

/-- Allowing a larger maximum occupancy (larger `k`) never decreases the count:
    for `n = 4`, `d = 3` the counts are `0 ≤ 54 ≤ 78` for `k = 2, 3, 4`. With
    `n = 4 > d = 3`, no injective (k=2) assignment exists, but relaxing to k=3
    and k=4 admits progressively more. -/
theorem k_monotone_4_3 :
    birthdayCountK 4 3 2 ≤ birthdayCountK 4 3 3 ∧
      birthdayCountK 4 3 3 ≤ birthdayCountK 4 3 4 := by
  refine ⟨by decide, by decide⟩

theorem k_values_4_3 :
    birthdayCountK 4 3 2 = 0 ∧ birthdayCountK 4 3 3 = 54 ∧
      birthdayCountK 4 3 4 = 78 := by
  refine ⟨by decide, by decide, by decide⟩

-- ============================================================
-- SECTION VIII: Summary
-- ============================================================

/-- **Summary.** The histogram recurrence `Rk` generalizes the parent's k=3
    slot recurrence to arbitrary maximum occupancy `M = k − 1`:
    it is faithful (`Rk n [e,s] = Rpar n e s`), recovers `birthdayCount3` at
    `k = 3`, the descending factorial at `k = 2`, and yields new verified counts
    for `k = 4`, with the count monotone in `k`. -/
theorem kway_summary :
    (∀ n e s, Rk n [e, s] = Rpar n e s) ∧
      (∀ n d, birthdayCountK n d 3 = Rpar n d 0) ∧
      birthdayCountK 4 3 4 = 78 :=
  ⟨Rk_eq_Rpar, birthdayCountK_eq_Rpar_k3, by decide⟩

#check Rk_eq_Rpar
#check birthdayCountK_eq_Rpar_k3
#check transition_length
#check kway_summary

end BirthdayKway
