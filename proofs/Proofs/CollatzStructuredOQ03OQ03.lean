/-
  Logarithmic Lower Bound for the Collatz Stopping Time

  Parent open question (collatz-structured-oq-03): what is the growth rate of the
  average stopping time S(N) = (1/N) Σ_{n=1}^N σ(n)?  The heuristic predicts
  S(N) ~ c·log N with c = 1/log₂(4/3) ≈ 6.95.  That asymptotic average is open.

  This entry proves a *pointwise* lower bound that anchors the growth-rate question
  from below and is fully verified (0 axioms):

      For every n that reaches 1 under the Collatz iteration,
                          n ≤ 2 ^ σ(n),      i.e.   σ(n) ≥ log₂ n.

  Reason: a single Collatz step decreases the value by at most a factor of two —
  an even step halves, an odd step (3n+1) can only increase — so
      n ≤ 2 · collatz n      and hence      n ≤ 2^s · collatzIter s n.
  Taking s = σ(n) with collatzIter s n = 1 gives n ≤ 2^{σ(n)}.

  The bound is *tight*: powers of two are the fastest trajectories,
      σ(2^k) = k = log₂(2^k),
  so 2^k realises equality.  Thus among all inputs of a given magnitude the powers
  of two have the minimum possible stopping time, exactly log₂ n.

  Tags: number-theory, collatz, stopping-time, lower-bound, powers-of-two
-/

import Mathlib

open Nat Finset

/- `reachesOne n` is the (undecidable) statement that `n`'s orbit reaches `1`; the
   stopping-time definition therefore relies on classical choice.  This introduces
   only the foundational `Classical.choice` axiom, which does not count as a
   mathematical assumption (the file remains 0-axiom in the reported sense). -/
open Classical

namespace CollatzStoppingTimeLowerBound

/-
## Part I: Collatz function, iteration, and stopping time

These mirror the definitions in the parent entry (collatz-structured-oq-03) so the
file is self-contained.
-/

/-- The Collatz function: `n/2` if `n` is even, else `3n+1`. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Iterate the Collatz function `k` times. -/
def collatzIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatzIter k (collatz n)

/-- `n` reaches `1` in exactly-or-fewer `k` steps (the value after `k` steps is `1`). -/
def reachesOneIn (n k : ℕ) : Prop :=
  collatzIter k n = 1

/-- `n` eventually reaches `1`. -/
def reachesOne (n : ℕ) : Prop :=
  ∃ k, reachesOneIn n k

/-- The stopping time: the least number of steps to reach `1` (or `0` if it never does). -/
noncomputable def stoppingTime (n : ℕ) : ℕ :=
  if h : reachesOne n then Nat.find h else 0

/-
## Part II: A single step loses at most a factor of two

The engine of the lower bound: `n ≤ 2 · collatz n` for every `n`.  An even step
halves (`2·(n/2) = n`), an odd step grows (`3n+1 ≥ n`).
-/

/-- One Collatz step decreases the value by at most a factor of two. -/
theorem le_two_mul_collatz (n : ℕ) : n ≤ 2 * collatz n := by
  unfold collatz
  rcases Nat.even_or_odd n with he | ho
  · -- even: collatz n = n / 2 and 2 * (n / 2) = n
    have h2 : n % 2 = 0 := Nat.even_iff.mp he
    simp only [h2, if_pos]
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h2)]
  · -- odd: collatz n = 3n + 1 ≥ n, so 2 * (3n+1) ≥ n
    have h2 : n % 2 = 1 := Nat.odd_iff.mp ho
    simp only [h2, Nat.one_ne_zero, if_neg, not_false_iff]
    nlinarith

/-- After `s` steps the original value is bounded by `2^s` times the current value. -/
theorem le_two_pow_mul_collatzIter (s : ℕ) :
    ∀ n : ℕ, n ≤ 2 ^ s * collatzIter s n := by
  induction s with
  | zero => intro n; simp [collatzIter]
  | succ k ih =>
    intro n
    -- collatzIter (k+1) n = collatzIter k (collatz n)
    have hstep : collatzIter (k + 1) n = collatzIter k (collatz n) := rfl
    rw [hstep, pow_succ]
    -- n ≤ 2 * collatz n ≤ 2 * (2^k * collatzIter k (collatz n)) = 2^k * 2 * collatzIter ...
    have h1 : n ≤ 2 * collatz n := le_two_mul_collatz n
    have h2 : collatz n ≤ 2 ^ k * collatzIter k (collatz n) := ih (collatz n)
    calc n ≤ 2 * collatz n := h1
      _ ≤ 2 * (2 ^ k * collatzIter k (collatz n)) := by
            exact Nat.mul_le_mul_left 2 h2
      _ = 2 ^ k * 2 * collatzIter k (collatz n) := by ring

/-- If `n` reaches `1` in `s` steps then `n ≤ 2^s`. -/
theorem le_two_pow_of_reachesOneIn {n s : ℕ} (h : reachesOneIn n s) : n ≤ 2 ^ s := by
  have := le_two_pow_mul_collatzIter s n
  rw [reachesOneIn] at h
  rw [h, mul_one] at this
  exact this

/-
## Part III: The logarithmic lower bound

`n ≤ 2 ^ σ(n)`, equivalently `σ(n) ≥ log₂ n`, for every convergent `n`.
-/

/-- **Main lower bound.** Any `n` that reaches `1` satisfies `n ≤ 2 ^ σ(n)`. -/
theorem le_two_pow_stoppingTime {n : ℕ} (h : reachesOne n) :
    n ≤ 2 ^ stoppingTime n := by
  unfold stoppingTime
  rw [dif_pos h]
  -- Nat.find h is the least s with reachesOneIn n s; it is a witness
  have hspec : reachesOneIn n (Nat.find h) := Nat.find_spec h
  exact le_two_pow_of_reachesOneIn hspec

/-- Real-valued form: `log₂ n ≤ σ(n)` for every convergent `n ≥ 1`. -/
theorem logb_le_stoppingTime {n : ℕ} (h : reachesOne n) (hn : 1 ≤ n) :
    Real.logb 2 n ≤ (stoppingTime n : ℝ) := by
  have hbound : n ≤ 2 ^ stoppingTime n := le_two_pow_stoppingTime h
  have hcast : (n : ℝ) ≤ (2 : ℝ) ^ stoppingTime n := by
    have : ((n : ℝ)) ≤ ((2 ^ stoppingTime n : ℕ) : ℝ) := by exact_mod_cast hbound
    simpa using this
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  calc Real.logb 2 (n : ℝ)
      ≤ Real.logb 2 ((2 : ℝ) ^ stoppingTime n) :=
        Real.logb_le_logb_of_le (by norm_num) hpos hcast
    _ = (stoppingTime n : ℝ) := by
        rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; ring

/-
## Part IV: Tightness — powers of two attain the bound

`σ(2^k) = k`, so 2^k realises equality `n = 2^{σ(n)}`.  Powers of two are the
fastest-converging inputs of their magnitude.
-/

/-- A power of two `2^(k+1)` steps to `2^k` in one Collatz step. -/
theorem collatz_two_pow_succ (k : ℕ) : collatz (2 ^ (k + 1)) = 2 ^ k := by
  unfold collatz
  have hmod : (2 ^ (k + 1)) % 2 = 0 := by
    rw [pow_succ]; exact Nat.mul_mod_left (2 ^ k) 2
  rw [if_pos hmod, pow_succ, Nat.mul_div_cancel (2 ^ k) (by norm_num)]

/-- `2^k` reaches `1` in exactly `k` steps. -/
theorem collatzIter_two_pow (k : ℕ) : collatzIter k (2 ^ k) = 1 := by
  induction k with
  | zero => simp [collatzIter]
  | succ m ih =>
    have hstep : collatzIter (m + 1) (2 ^ (m + 1)) = collatzIter m (collatz (2 ^ (m + 1))) :=
      rfl
    rw [hstep, collatz_two_pow_succ, ih]

/-- Every power of two reaches `1`. -/
theorem reachesOne_two_pow (k : ℕ) : reachesOne (2 ^ k) :=
  ⟨k, collatzIter_two_pow k⟩

/-- **Tightness.** The stopping time of `2^k` is exactly `k`. -/
theorem stoppingTime_two_pow (k : ℕ) : stoppingTime (2 ^ k) = k := by
  have h : reachesOne (2 ^ k) := reachesOne_two_pow k
  unfold stoppingTime
  rw [dif_pos h]
  apply Nat.find_eq_iff h |>.mpr
  refine ⟨collatzIter_two_pow k, ?_⟩
  intro m hm hcontra
  -- reachesOneIn (2^k) m ⟹ 2^k ≤ 2^m ⟹ k ≤ m, contradicting m < k
  have hle : (2 : ℕ) ^ k ≤ 2 ^ m := le_two_pow_of_reachesOneIn hcontra
  have : k ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
  omega

/-
## Part V: Concrete corollaries

The exact stopping times of small powers of two.
-/

/-- `σ(1) = 0`. -/
theorem stoppingTime_one : stoppingTime 1 = 0 := by
  have := stoppingTime_two_pow 0
  simpa using this

/-- `σ(2) = 1`. -/
theorem stoppingTime_two : stoppingTime 2 = 1 := by
  have := stoppingTime_two_pow 1
  simpa using this

/-- `σ(4) = 2`. -/
theorem stoppingTime_four : stoppingTime 4 = 2 := by
  have := stoppingTime_two_pow 2
  norm_num at this
  exact this

/-- `σ(8) = 3`. -/
theorem stoppingTime_eight : stoppingTime 8 = 3 := by
  have := stoppingTime_two_pow 3
  norm_num at this
  exact this

/-- `σ(16) = 4`. -/
theorem stoppingTime_sixteen : stoppingTime 16 = 4 := by
  have := stoppingTime_two_pow 4
  norm_num at this
  exact this

#check @le_two_pow_stoppingTime
#check @stoppingTime_two_pow
#check @logb_le_stoppingTime

end CollatzStoppingTimeLowerBound

-- TEMP axiom audit
open CollatzStoppingTimeLowerBound in
#print axioms le_two_pow_stoppingTime
open CollatzStoppingTimeLowerBound in
#print axioms stoppingTime_two_pow
open CollatzStoppingTimeLowerBound in
#print axioms logb_le_stoppingTime
open CollatzStoppingTimeLowerBound in
#print axioms le_two_mul_collatz
