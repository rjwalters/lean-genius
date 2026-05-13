/-
# birthday-problem-oq-01-oq-02 — S2 ACT

Helper lemma `one_sub_prod_le_sum`: a real-valued "union bound for products"
that converts a product of probabilities of non-events to a sum of event
probabilities. Specifically, for `f : ℕ → ℝ` with `f i ∈ [0, 1]` for `i < n`,

  `1 - ∏_{i ∈ range n} (1 - f i)  ≤  ∑_{i ∈ range n} f i`.

The intuition: the LHS is the probability of "at least one event among
`{event_0, …, event_{n-1}}` occurs" if `f i` is the probability of `event_i`
(independent events). The union bound replaces it with the sum.

This is the **first** step of S2 in the OQ01–OQ02 coupling roadmap (state.md
§"Next Action"). The next step (S3, separate PR) chains this with the existing
`gauss_sum_div` (OQ02) and `two_mul_choose_two` (OQ01) to derive the Markov
upper bound `probCollision ≤ ↑expectedPairs`.

## Status

- 0 sorries
- 0 axioms (this file introduces none; total parent-tree axioms unchanged)
- 1 new theorem
- Build pending verification via Docker wrapper.

The proof is by induction on `n`. The successor step uses the identity
`1 - P·(1-a) = (1-P) + P·a` together with `(1-P)·(1-a) ≤ (1-P)` once we know
`0 ≤ 1-P` (from `∏ ≤ 1`, by `Finset.prod_le_one`).
-/
import Mathlib

namespace BirthdayProblemOQ01OQ02

open BigOperators

/-- Real-valued union bound for products. If `0 ≤ f i ≤ 1` for every
`i < n`, then `1 - ∏_{i ∈ range n} (1 - f i) ≤ ∑_{i ∈ range n} f i`.

Used downstream (S3, separate PR) to bridge OQ02's product formula
`probCollision` and OQ01's first-moment quantity `expectedPairs`. -/
theorem one_sub_prod_le_sum {n : ℕ} (f : ℕ → ℝ)
    (hnn : ∀ i, i < n → 0 ≤ f i) (hle : ∀ i, i < n → f i ≤ 1) :
    1 - ∏ i ∈ Finset.range n, (1 - f i)
      ≤ ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hnn' : ∀ i, i < k → 0 ≤ f i :=
      fun i hi => hnn i (Nat.lt_succ_of_lt hi)
    have hle' : ∀ i, i < k → f i ≤ 1 :=
      fun i hi => hle i (Nat.lt_succ_of_lt hi)
    have hfk_nn : 0 ≤ f k := hnn k (Nat.lt_succ_self k)
    have hfk_le : f k ≤ 1 := hle k (Nat.lt_succ_self k)
    have hP_le_one : ∏ i ∈ Finset.range k, (1 - f i) ≤ 1 := by
      apply Finset.prod_le_one
      · intro i hi
        rw [Finset.mem_range] at hi
        have h0 : 0 ≤ f i := hnn i (Nat.lt_succ_of_lt hi)
        have h1 : f i ≤ 1 := hle i (Nat.lt_succ_of_lt hi)
        linarith
      · intro i hi
        rw [Finset.mem_range] at hi
        linarith [hnn i (Nat.lt_succ_of_lt hi)]
    have hP_ge_zero : 0 ≤ ∏ i ∈ Finset.range k, (1 - f i) := by
      apply Finset.prod_nonneg
      intro i hi
      rw [Finset.mem_range] at hi
      linarith [hle i (Nat.lt_succ_of_lt hi)]
    have hih : 1 - ∏ i ∈ Finset.range k, (1 - f i) ≤ ∑ i ∈ Finset.range k, f i :=
      ih hnn' hle'
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    -- After the rewrites, with P := ∏ … and S := ∑ …, the goal is
    --   1 - P · (1 - f k) ≤ S + f k.
    -- Expanding, this is (1 - P) + P · f k ≤ S + f k, i.e.
    --   (1 - P) - (1 - P) · f k ≤ S,
    -- closed by the IH `1 - P ≤ S` plus `(1 - P) · f k ≥ 0`.
    nlinarith [hih, hP_le_one, hP_ge_zero, hfk_nn, hfk_le,
      mul_nonneg (sub_nonneg.mpr hP_le_one) hfk_nn,
      mul_nonneg hP_ge_zero hfk_nn]

end BirthdayProblemOQ01OQ02
