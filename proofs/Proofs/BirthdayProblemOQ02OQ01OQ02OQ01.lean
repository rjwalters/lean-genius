import Mathlib

/-
# Collision Probability: a Sharp Upper Bound and the Smoothing Mechanism
  (Birthday OQ-02-OQ-01-OQ-02-OQ-01)

## What This Proves

The parent entry `birthday-problem-oq-02-oq-01-oq-02` (`BirthdayProblemOQ02OQ01OQ02.lean`)
proves one half of the extremal picture for the two-draw **collision probability**

  `C(p) = ∑ᵢ pᵢ²`

of a probability vector `p = (p₀, …, p_{d-1})`: the uniform distribution *minimizes*
`C`, giving the sharp **lower** bound `C(p) ≥ 1/d` with equality iff `p` is uniform.

This file supplies the complementary **upper** half together with the local mechanism
that drives the whole extremal theory:

  1. **Sharp upper bound.**  `C(p) ≤ max_i pᵢ`.  Collision can never exceed the single
     most likely outcome's probability.  More generally `C(p) ≤ M` for *any* upper bound
     `M ≥ pᵢ`.
  2. **Equality characterization.**  `C(p) = M` holds exactly when every `pᵢ ∈ {0, M}`,
     i.e. the mass is spread *uniformly over its support* — the opposite extreme to the
     lower-bound's "uniform over everything".
  3. **Two-sided bound.**  Combining with a self-contained re-derivation of the lower
     bound (via `Finset.sq_sum_le_card_mul_sum_sq`):  `1/d ≤ C(p) ≤ max_i pᵢ`.
  4. **The smoothing atom (Schur-convexity local step).**  Replacing the values at two
     coordinates by their average weakly decreases `C`, strictly unless they were already
     equal.  This is the elementary "Robin Hood"/Muirhead transfer underlying *why*
     equalizing mass lowers collision probability — the mechanism behind the parent's
     minimization result.

Everything is elementary (a single `(a−b)²/2 ≥ 0`), self-contained, and axiom-free.

## Why This Is Not the Parent

The parent bounds `C` from **below** by the uniform value `1/d`. Here we bound it from
**above** by `max pᵢ`, characterize that equality (concentration on equal-mass atoms,
*not* uniformity), and isolate the transfer inequality that makes "spreading mass out"
monotonically decrease collisions. These are genuinely new, complementary statements.
-/

open Finset

namespace BirthdayCollisionBounds

variable {d : ℕ}

/-! ## The smoothing atom (Schur-convexity local step) -/

/-- Algebraic identity behind everything: the gap between `a² + b²` and twice the squared
average is `(a−b)²/2`. -/
theorem sq_add_sq_sub_two_avg_sq (a b : ℝ) :
    a ^ 2 + b ^ 2 - 2 * ((a + b) / 2) ^ 2 = (a - b) ^ 2 / 2 := by ring

/-- **Averaging weakly decreases the sum of squares.** Twice the squared average of two
reals never exceeds the sum of their squares. -/
theorem two_avg_sq_le (a b : ℝ) : 2 * ((a + b) / 2) ^ 2 ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **Strict version.** When the two values differ, averaging *strictly* decreases the
sum of squares. -/
theorem two_avg_sq_lt (a b : ℝ) (h : a ≠ b) :
    2 * ((a + b) / 2) ^ 2 < a ^ 2 + b ^ 2 := by
  have hne : a - b ≠ 0 := sub_ne_zero.mpr h
  have hpos : 0 < (a - b) ^ 2 := by positivity
  nlinarith [hpos]

/-! ## Sharp upper bound on the collision probability -/

variable (p : Fin d → ℝ)

/-- **Upper bound by any dominating value.** For a probability vector `p` with every
`pᵢ ≤ M` (and `pᵢ ≥ 0`), the collision probability is at most `M`:

  `∑ᵢ pᵢ² ≤ M`. -/
theorem collision_le_of_le (M : ℝ) (hnn : ∀ i, 0 ≤ p i) (hM : ∀ i, p i ≤ M)
    (hsum : ∑ i, p i = 1) : ∑ i, p i ^ 2 ≤ M := by
  calc ∑ i, p i ^ 2 ≤ ∑ i, p i * M := by
          apply Finset.sum_le_sum
          intro i _
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left (hM i) (hnn i)
    _ = (∑ i, p i) * M := by rw [← Finset.sum_mul]
    _ = M := by rw [hsum, one_mul]

/-- **Equality characterization for the upper bound.** Collision equals its dominating
value `M` exactly when the distribution is supported on equal-mass atoms, i.e. every
`pᵢ ∈ {0, M}`. This is the *concentration* extreme, opposite to the lower-bound's
uniformity. -/
theorem collision_eq_of_le_iff (M : ℝ) (hnn : ∀ i, 0 ≤ p i) (hM : ∀ i, p i ≤ M)
    (hsum : ∑ i, p i = 1) :
    ∑ i, p i ^ 2 = M ↔ ∀ i, p i = 0 ∨ p i = M := by
  have key : ∑ i, p i * (M - p i) = M - ∑ i, p i ^ 2 := by
    have e : ∀ i, p i * (M - p i) = p i * M - p i ^ 2 := fun i => by ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_sub_distrib, ← Finset.sum_mul,
      hsum, one_mul]
  rw [show (∑ i, p i ^ 2 = M) ↔ (M - ∑ i, p i ^ 2 = 0) from
        ⟨fun h => by rw [h]; ring, fun h => by linarith⟩,
    ← key,
    Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_nonneg (hnn i) (by linarith [hM i]))]
  constructor
  · intro h i
    rcases mul_eq_zero.mp (h i (Finset.mem_univ i)) with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0).symm
  · intro h i _
    rcases h i with h0 | h0
    · rw [h0]; ring
    · rw [h0]; ring

/-- **Sharp upper bound by the maximum.** Collision is bounded by the probability of the
most likely outcome: there is an index `k` with `∑ᵢ pᵢ² ≤ p k`. -/
theorem collision_le_max (hd : 0 < d) (hnn : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    ∃ k, ∑ i, p i ^ 2 ≤ p k := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty) p
  refine ⟨k, collision_le_of_le p (p k) hnn (fun i => ?_) hsum⟩
  rw [← hk]
  exact Finset.le_sup' p (Finset.mem_univ i)

/-! ## Self-contained lower bound and the two-sided picture -/

/-- **Lower bound (uniform minimizes), self-contained.** Re-derived here directly from the
variance identity `∑ pᵢ² − 1/d = ∑ (pᵢ − 1/d)² ≥ 0` so this file stands alone:

  `1/d ≤ ∑ᵢ pᵢ²`. -/
theorem one_div_card_le_collision (hd : 0 < d) (hsum : ∑ i, p i = 1) :
    1 / (d : ℝ) ≤ ∑ i, p i ^ 2 := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have key : (∑ i, p i ^ 2) - 1 / (d : ℝ) = ∑ i, (p i - 1 / (d : ℝ)) ^ 2 := by
    have expand : ∑ i, (p i - 1 / (d : ℝ)) ^ 2
        = ∑ i, (p i ^ 2 - (2 / (d : ℝ)) * p i + (1 / (d : ℝ)) ^ 2) :=
      Finset.sum_congr rfl (fun i _ => by ring)
    rw [expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ ∑ i, (p i - 1 / (d : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith [key, hnn]

/-- **Two-sided collision bound.** For any probability vector with dominating value `M`:

  `1/d ≤ ∑ᵢ pᵢ² ≤ M`.

The lower bound is attained by the uniform distribution; the upper bound by any
distribution concentrated on equal-mass atoms. -/
theorem collision_two_sided (hd : 0 < d) (M : ℝ) (hnn : ∀ i, 0 ≤ p i)
    (hM : ∀ i, p i ≤ M) (hsum : ∑ i, p i = 1) :
    1 / (d : ℝ) ≤ ∑ i, p i ^ 2 ∧ ∑ i, p i ^ 2 ≤ M :=
  ⟨one_div_card_le_collision p hd hsum, collision_le_of_le p M hnn hM hsum⟩

/-! ## The smoothing operator: equalizing two coordinates lowers collision -/

/-- **Smoothing decreases collision.** Replacing the values at two distinct coordinates
`i ≠ j` by their common average weakly decreases the sum of squares `∑ f²` — the
"Robin Hood"/Muirhead transfer that, iterated, drives the distribution toward uniform and
the collision probability toward its minimum. -/
theorem smoothing_sum_sq_le (f : Fin d → ℝ) {i j : Fin d} (hij : i ≠ j) :
    (∑ k, (Function.update (Function.update f i ((f i + f j) / 2)) j
            ((f i + f j) / 2) k) ^ 2)
      ≤ ∑ k, (f k) ^ 2 := by
  set g : Fin d → ℝ :=
    Function.update (Function.update f i ((f i + f j) / 2)) j ((f i + f j) / 2) with hg
  -- values of `g` at the two touched coordinates and elsewhere
  have hgj : g j = (f i + f j) / 2 := by rw [hg, Function.update_self]
  have hgi : g i = (f i + f j) / 2 := by
    rw [hg, Function.update_of_ne hij, Function.update_self]
  have hgk : ∀ k, k ≠ i → k ≠ j → g k = f k := by
    intro k hki hkj
    rw [hg, Function.update_of_ne hkj, Function.update_of_ne hki]
  -- off `{i, j}` the squared difference vanishes
  have hzero : ∀ k ∈ (Finset.univ : Finset (Fin d)), k ≠ i ∧ k ≠ j →
      (g k) ^ 2 - (f k) ^ 2 = 0 := by
    intro k _ hk
    rw [hgk k hk.1 hk.2]; ring
  have hsplit : (∑ k, (g k) ^ 2) - ∑ k, (f k) ^ 2
      = ((g i) ^ 2 - (f i) ^ 2) + ((g j) ^ 2 - (f j) ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_eq_add_of_mem i j (Finset.mem_univ i) (Finset.mem_univ j) hij hzero
  have hbound : ((g i) ^ 2 - (f i) ^ 2) + ((g j) ^ 2 - (f j) ^ 2) ≤ 0 := by
    rw [hgi, hgj]
    nlinarith [two_avg_sq_le (f i) (f j)]
  linarith [hsplit, hbound]

end BirthdayCollisionBounds
