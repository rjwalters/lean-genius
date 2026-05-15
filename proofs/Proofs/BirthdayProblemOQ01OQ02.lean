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
import Proofs.BirthdayProblemOQ02

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

/-! ## S3 ACT: Markov coupling — closed-form upper bound

The Markov-style upper bound chains S2's `one_sub_prod_le_sum` with OQ02's
`gauss_sum_div`. We state it in **closed form** `k·(k-1)/(2·d)` rather than
via `BirthdayProblemOQ01.expectedPairs k d`, because the parent OQ01 file
has Mathlib v4.26.0 regressions (`Nat.choose_three_right` removed, plus 5
`native_decide` failures) blocking its import at the time of this session.
Once OQ01 is repaired, the trivial bridge

  `((BirthdayProblemOQ01.expectedPairs k d : ℚ) : ℝ) = k·(k-1)/(2·d)`

(definitionally `expectedPairs k d = (k.choose 2 : ℚ) / d`; closed form via
`Nat.choose_two_right` + cast) lifts this to the `expectedPairs` form.
-/

open BirthdayProblemOQ02

/-- **Markov coupling for the birthday problem (closed form).** The
collision probability is bounded above by the closed-form first-moment
quantity `k·(k-1)/(2·d)`:

  `probCollision k d ≤ k·(k-1)/(2·d)`.

This RHS equals `BirthdayProblemOQ01.expectedPairs k d` (cast to `ℝ`) by
`expectedPairs_eq_rational`; stated in closed form here so the file does
not depend on the OQ01 parent (currently Mathlib-v4.26.0-regressed).

Proof: union bound `1 - ∏(1 - i/d) ≤ ∑ i/d` (via `one_sub_prod_le_sum`
with `f i = i/d`, side conditions `0 ≤ i/d ≤ 1` from `k ≤ d`) plus the
Gauss-sum closed form `∑ i/d = k·(k-1)/(2·d)` (`gauss_sum_div`).

This is the upper half of the OQ02–OQ01 bracket: combined with the
exponential lower bound `probCollision_ge` (OQ02:173), the collision
probability lies in
`[1 - exp(-k(k-1)/(2d)), k·(k-1)/(2d)]`. -/
theorem probCollision_le_choose_two_div (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d) :
    probCollision k d ≤ (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ)) := by
  -- Side conditions: 0 ≤ i/d ≤ 1 for i < k (using k ≤ d).
  have hnn : ∀ i, i < k → 0 ≤ (i : ℝ) / (d : ℝ) := by
    intro i _; positivity
  have hle : ∀ i, i < k → (i : ℝ) / (d : ℝ) ≤ 1 := by
    intro i hi
    rw [div_le_one (Nat.cast_pos.mpr hd)]
    exact_mod_cast (lt_of_lt_of_le hi hkd).le
  -- Apply union bound: 1 - ∏(1 - i/d) ≤ ∑ i/d.
  have hbound :
      1 - ∏ i ∈ Finset.range k, (1 - (i : ℝ) / (d : ℝ))
        ≤ ∑ i ∈ Finset.range k, (i : ℝ) / (d : ℝ) :=
    one_sub_prod_le_sum (fun i => (i : ℝ) / (d : ℝ)) hnn hle
  -- Gauss-sum identity collapses the right-hand side.
  have hsum :
      ∑ i ∈ Finset.range k, (i : ℝ) / (d : ℝ)
        = (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ)) :=
    gauss_sum_div k d hd
  -- Conclude: probCollision k d = 1 - probAllDistinct k d defeq, and
  -- probAllDistinct k d = ∏ i ∈ range k, (1 - i/d) by definition.
  show 1 - probAllDistinct k d ≤ (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ))
  unfold probAllDistinct
  rw [← hsum]
  exact hbound

end BirthdayProblemOQ01OQ02
