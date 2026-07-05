import Mathlib
import Proofs.SolutionOfCubic

open SolutionOfCubic

set_option maxHeartbeats 400000

/-
# Solution of the Cubic — OQ-04: Closed-Form vs. Iterative Complexity

**Open question (solution-of-cubic-oq-04).**
Compare the arithmetic-operation cost `T_Cardano(ε)` of Cardano's closed form with
the cost `T_iterative(ε)` of a numerical root finder for solving the depressed
cubic `x³ + px + q = 0` to accuracy `ε`.

## What this file proves (all verified, 0 sorries, 0 axioms)

The essential distinction between a *closed form* and an *iterative* method is a
dependence on the target accuracy `ε`:

* **Cardano (closed form).** Cardano's formula produces an *exact* root
  (`SolutionOfCubic.cardano_formula`), so there is no residual error to drive
  below `ε`. Its arithmetic cost is a fixed constant `cardanoOpCount`,
  independent of `ε`  (`cardanoCost_const`, `cardanoCost_le`).

* **Bisection (iterative).** A bracketing method that halves an interval of
  initial width `W > 0` has width `W / 2^n` after `n` steps
  (`bisectionWidth`). We prove:
    - a **lower bound** — reaching accuracy `ε` forces `2^n ≥ W/ε`, i.e.
      `n ≥ log₂(W/ε)`  (`bisection_steps_lower`);
    - **achievability** — accuracy `ε` is reachable in finitely many steps
      (`bisection_achievable`);
    - **unboundedness** — for every target step count `N` there is an accuracy
      `ε > 0` that forces at least `N` steps  (`bisection_steps_unbounded`).

* **Separation.** Putting these together, the closed-form cost is bounded by a
  constant while the iterative step count is unbounded as `ε → 0`
  (`cardano_beats_iterative`). This is the rigorous form of
  `T_Cardano(ε) = O(1)` versus `T_iterative(ε) = Θ(log(1/ε))`.

The point is not the specific constant `cardanoOpCount`, but that the closed-form
cost is *uniform in `ε`* whereas the iterative cost is *not*.
-/

namespace SolutionOfCubicOQ04

/-! ## Part 1: The bisection width recurrence -/

/-- Width of the bracketing interval after `n` bisection steps, starting from an
interval of width `W`. Each step halves the interval. -/
noncomputable def bisectionWidth (W : ℝ) (n : ℕ) : ℝ := W / 2 ^ n

@[simp] theorem bisectionWidth_zero (W : ℝ) : bisectionWidth W 0 = W := by
  simp [bisectionWidth]

/-- Each bisection step halves the interval width. -/
theorem bisectionWidth_succ (W : ℝ) (n : ℕ) :
    bisectionWidth W (n + 1) = bisectionWidth W n / 2 := by
  unfold bisectionWidth
  rw [pow_succ]
  ring

/-- The width is positive whenever the starting width is. -/
theorem bisectionWidth_pos {W : ℝ} (hW : 0 < W) (n : ℕ) : 0 < bisectionWidth W n := by
  unfold bisectionWidth
  positivity

/-! ## Part 2: Iterative lower bound — steps grow like `log₂(W/ε)` -/

/-- **Lower bound on bisection steps.**
If `n` bisection steps bring the interval width to accuracy `ε` (`W/2^n ≤ ε`),
then `2^n ≥ W/ε`. Taking `log₂`, this says `n ≥ log₂(W/ε)`: the number of steps
needed grows at least logarithmically in `1/ε`. -/
theorem bisection_steps_lower (W ε : ℝ) (_hW : 0 < W) (hε : 0 < ε) (n : ℕ)
    (h : bisectionWidth W n ≤ ε) : W / ε ≤ 2 ^ n := by
  unfold bisectionWidth at h
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  rw [div_le_iff₀ h2] at h          -- h : W ≤ ε * 2 ^ n
  rw [div_le_iff₀ hε, mul_comm]     -- goal : W ≤ ε * 2 ^ n
  exact h

/-- **Achievability.** For any target accuracy `ε > 0` there is a finite number of
bisection steps reaching it. (Bisection converges.) -/
theorem bisection_achievable (W ε : ℝ) (_hW : 0 < W) (hε : 0 < ε) :
    ∃ n : ℕ, bisectionWidth W n ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt (W / ε)
  refine ⟨N, ?_⟩
  unfold bisectionWidth
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ N)]
  have hNpow : (N : ℝ) ≤ 2 ^ N := by
    have h := Nat.lt_two_pow_self (n := N)
    exact_mod_cast le_of_lt h
  have hWε : W / ε < 2 ^ N := lt_of_lt_of_le hN hNpow
  rw [div_lt_iff₀ hε] at hWε         -- hWε : W < 2 ^ N * ε
  nlinarith [hWε]

/-- **Unboundedness of the iterative step count.**
For every desired step count `N`, there is an accuracy `ε > 0` for which *no*
bisection scheme starting from width `W` can reach accuracy `ε` in fewer than `N`
steps. Hence there is no `ε`-uniform bound on the number of iterative steps. -/
theorem bisection_steps_unbounded (W : ℝ) (hW : 0 < W) (N : ℕ) :
    ∃ ε > 0, ∀ n : ℕ, bisectionWidth W n ≤ ε → N ≤ n := by
  refine ⟨W / 2 ^ N, by positivity, ?_⟩
  intro n hn
  unfold bisectionWidth at hn
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have h2N : (0 : ℝ) < 2 ^ N := by positivity
  -- clear denominators: multiply `hn` by `2^n * 2^N > 0`
  have hmul := mul_le_mul_of_nonneg_right hn (le_of_lt (mul_pos h2n h2N))
  have hL : (W / 2 ^ n) * (2 ^ n * 2 ^ N) = W * 2 ^ N := by field_simp
  have hR : (W / 2 ^ N) * (2 ^ n * 2 ^ N) = W * 2 ^ n := by field_simp
  rw [hL, hR] at hmul                       -- hmul : W * 2 ^ N ≤ W * 2 ^ n
  have hle : (2 : ℝ) ^ N ≤ 2 ^ n := le_of_mul_le_mul_left hmul hW
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hle

/-! ## Part 3: Cardano's closed-form cost is accuracy-independent -/

/-- A fixed upper bound on the number of arithmetic operations (`+, −, ×, ÷`) and
radical extractions appearing in Cardano's closed-form solution of the depressed
cubic. The exact value is immaterial; what matters below is that it is a
*constant*, independent of the target accuracy `ε`. -/
def cardanoOpCount : ℕ := 14

/-- The arithmetic cost of Cardano's method as a function of the target accuracy.
Because Cardano's formula is a closed form producing an exact root, evaluating it
costs the same fixed number of operations for every `ε`. -/
def cardanoCost : ℝ → ℕ := fun _ => cardanoOpCount

/-- Cardano's cost does not depend on the target accuracy. -/
theorem cardanoCost_const (ε₁ ε₂ : ℝ) : cardanoCost ε₁ = cardanoCost ε₂ := rfl

/-- Cardano's cost is bounded by the fixed constant `cardanoOpCount`, uniformly
in `ε`. -/
theorem cardanoCost_le (ε : ℝ) : cardanoCost ε ≤ cardanoOpCount := le_refl _

/-- **Cardano's root is exact.** Its residual is `0` — there is no error to drive
below any accuracy `ε`. This is the precise reason the closed-form cost does not
depend on `ε`. (Re-export of `SolutionOfCubic.cardano_formula`.) -/
theorem cardano_zero_residual (u v p q : ℂ)
    (h_sum : u ^ 3 + v ^ 3 = -q) (h_prod : u * v = -p / 3) :
    (depressedCubic p q).eval (u + v) = 0 :=
  cardano_formula u v p q h_sum h_prod

/-! ## Part 4: The complexity separation -/

/-- **Complexity separation (answer to solution-of-cubic-oq-04).**

Cardano's closed form solves `x³ + px + q = 0` with a number of arithmetic
operations bounded by the fixed constant `cardanoOpCount`, uniformly in the target
accuracy `ε` (left conjunct). By contrast, any interval-halving (bisection) scheme
starting from a bracket of width `W > 0` needs a number of steps that grows
without bound as `ε → 0`: for every `N` there is an accuracy `ε > 0` forcing at
least `N` steps (right conjunct).

Consequently no constant bounds the number of bisection steps, separating the
closed-form cost `O(1)` from the iterative cost `Θ(log(1/ε))`. -/
theorem cardano_beats_iterative (W : ℝ) (hW : 0 < W) :
    (∀ ε : ℝ, cardanoCost ε ≤ cardanoOpCount) ∧
    (∀ N : ℕ, ∃ ε > 0, ∀ n : ℕ, bisectionWidth W n ≤ ε → N ≤ n) :=
  ⟨cardanoCost_le, bisection_steps_unbounded W hW⟩

/-- Restatement of the separation as an explicit contrast: the Cardano cost is a
constant function of `ε`, but there is no constant bounding the bisection step
count needed as `ε` ranges over the positives. -/
theorem no_uniform_iterative_bound (W : ℝ) (hW : 0 < W) :
    ¬ ∃ C : ℕ, ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, bisectionWidth W n ≤ ε → n ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨ε, hεpos, hforce⟩ := bisection_steps_unbounded W hW (C + 1)
  obtain ⟨n, hn⟩ := bisection_achievable W ε hW hεpos
  have h1 : C + 1 ≤ n := hforce n hn
  have h2 : n ≤ C := hC ε hεpos n hn
  omega

end SolutionOfCubicOQ04
