/-
  Fair Games Theorem OQ-02-OQ-03: Variance of Gambler's Ruin Stopping Time

  This file scaffolds the variance computation for the simple symmetric
  random walk Gambler's Ruin stopping time τ. The expected value
  E[τ] = k(N-k) is proven in `FairGamesTheoremOQ02` via the quadratic
  martingale `S_n^2 - n`. The variance requires the **quartic martingale**

      M_n = S_n^4 - 6 n S_n^2 + 3 n^2 + 2 n.

  This first iteration (OBSERVE phase) establishes the algebraic
  prerequisite: the polynomial `Q(n, s) = s^4 - 6 n s^2 + 3 n^2 + 2 n`
  satisfies the symmetric step-mean equality

      ½ · Q(n+1, s+1) + ½ · Q(n+1, s-1) = Q(n, s),

  which is exactly the pointwise form of the martingale identity
  `E[M_{n+1} | S_n = s] = M_n` for the simple symmetric random walk
  (the increment `X_{n+1}` is uniform on `{+1, -1}`).

  Strategy for E[τ²]:
  By Doob's optional stopping at τ, `E[M_τ] = M_0 = k^4`. Expanding,
      k^4 = E[S_τ^4] - 6 E[τ · S_τ^2] + 3 E[τ^2] + 2 E[τ].
  Since `S_τ ∈ {0, N}` with `P(S_τ = N) = k/N`,
      E[S_τ^4] = N^3 · k,   E[τ · S_τ^2] = N^2 · W,
  where `W = E[τ · 𝟙_{S_τ = N}]` is the expected hitting time of the
  upper barrier weighted by winning.

  The bottleneck `W` is itself pinned down by a **cubic martingale**:
  `Y_n = S_n^3 - 3 n S_n` is a martingale for the simple symmetric walk
  (same `½`-average identity, proved below), so optional stopping gives
      k^3 = E[S_τ^3] - 3 E[τ · S_τ] = N^2 · k - 3 N · W,
  hence `3 N W = k (N^2 - k^2)`, i.e. `W = k (N-k)(N+k) / (3 N)`.

  Substituting the cubic relation into the quartic OST equation
  eliminates `W` entirely and yields the closed form
      Var(τ) = E[τ²] - E[τ]² = (1/3) · k (N-k) (N^2 - 2 N k + 2 k^2 - 2).
  (Sanity check: `k = 1, N = 2` gives `τ ≡ 1` and `Var = 0`; the formula
  returns `(1/3)·1·1·(4 - 4 + 2 - 2) = 0`.)

  The two optional-stopping equations `k^3 = N^2 k - 3 N W` and
  `k^4 = N^3 k - 6 N^2 W + 3 E[τ²] + 2 E[τ]` are the only inputs still
  awaiting a measure-theoretic derivation (lifting `Q` and `Y` into the
  random-walk filtration); given them, the algebra below is complete and
  machine-checked.

  Reference: Feller, *An Introduction to Probability Theory and Its
  Applications*, Vol. 1, §XIV.2.
-/

import Mathlib

namespace FairGamesOQ02OQ03

/-- The quartic martingale value for the simple symmetric random walk:
    `Q(n, s) = s^4 - 6 n s^2 + 3 n^2 + 2 n`.

    The process `n ↦ Q(n, S_n)` is a martingale for `S_n` taking
    independent steps uniformly in `{+1, -1}`. -/
def quarticMartingaleValue (n s : ℝ) : ℝ :=
  s ^ 4 - 6 * n * s ^ 2 + 3 * n ^ 2 + 2 * n

/-- **Step-mean identity (martingale property).** The average of
    `Q(n+1, s+1)` and `Q(n+1, s-1)` equals `Q(n, s)`. This is the
    algebraic backbone of `E[M_{n+1} | S_n = s] = M_n`. -/
theorem quarticMartingaleValue_step_mean (n s : ℝ) :
    (quarticMartingaleValue (n + 1) (s + 1) +
     quarticMartingaleValue (n + 1) (s - 1)) / 2 =
    quarticMartingaleValue n s := by
  simp only [quarticMartingaleValue]
  ring

/-- The quartic martingale at time 0: `Q(0, s) = s^4`. Combined with
    `S_0 = k`, this gives `M_0 = k^4`, the right-hand side of OST. -/
theorem quarticMartingaleValue_zero (s : ℝ) :
    quarticMartingaleValue 0 s = s ^ 4 := by
  simp [quarticMartingaleValue]

/-- The quartic martingale at the lower absorbing barrier `s = 0`:
    `Q(n, 0) = 3 n^2 + 2 n`. -/
theorem quarticMartingaleValue_at_lower (n : ℝ) :
    quarticMartingaleValue n 0 = 3 * n ^ 2 + 2 * n := by
  simp [quarticMartingaleValue]

/-- The quartic martingale at the upper absorbing barrier `s = N`:
    `Q(n, N) = N^4 - 6 n N^2 + 3 n^2 + 2 n`. -/
theorem quarticMartingaleValue_at_upper (n N : ℝ) :
    quarticMartingaleValue n N = N ^ 4 - 6 * n * N ^ 2 + 3 * n ^ 2 + 2 * n := by
  simp [quarticMartingaleValue]

/-- A direct corollary of the step-mean identity in a form that mirrors
    `E[M_{n+1}] = E[M_n]` under the symmetric step distribution. -/
theorem quarticMartingaleValue_increment_eq_zero (n s : ℝ) :
    quarticMartingaleValue (n + 1) (s + 1) +
      quarticMartingaleValue (n + 1) (s - 1) =
        2 * quarticMartingaleValue n s := by
  have h := quarticMartingaleValue_step_mean n s
  linarith

/-- The cubic martingale value for the simple symmetric random walk:
    `Y(n, s) = s^3 - 3 n s`. The process `n ↦ Y(n, S_n)` is a martingale;
    its optional-stopping equation pins down the hitting weight
    `W = E[τ · 𝟙_{S_τ = N}]`. -/
def cubicMartingaleValue (n s : ℝ) : ℝ :=
  s ^ 3 - 3 * n * s

/-- **Step-mean identity for the cubic martingale.** The average of
    `Y(n+1, s+1)` and `Y(n+1, s-1)` equals `Y(n, s)`, the pointwise form
    of `E[Y_{n+1} | S_n = s] = Y_n`. -/
theorem cubicMartingaleValue_step_mean (n s : ℝ) :
    (cubicMartingaleValue (n + 1) (s + 1) +
     cubicMartingaleValue (n + 1) (s - 1)) / 2 =
    cubicMartingaleValue n s := by
  simp only [cubicMartingaleValue]
  ring

/-- The cubic martingale at time 0: `Y(0, s) = s^3`, so `Y_0 = k^3`. -/
theorem cubicMartingaleValue_zero (s : ℝ) :
    cubicMartingaleValue 0 s = s ^ 3 := by
  simp [cubicMartingaleValue]

/-- **Hitting weight from the cubic OST equation.** If optional stopping
    of the cubic martingale `Y` at `τ` yields
    `k^3 = N^2 k - 3 N W` (using `E[S_τ^3] = N^2 k` and
    `E[τ S_τ] = N W` for `S_τ ∈ {0, N}`, `P(S_τ = N) = k/N`), then
    `3 N W = k (N - k)(N + k)`, i.e. `W = k(N^2 - k^2)/(3N)`. -/
theorem hitting_weight (N k W : ℝ)
    (hcubic : k ^ 3 = N ^ 2 * k - 3 * (N * W)) :
    3 * (N * W) = k * (N - k) * (N + k) := by
  linear_combination hcubic

/-- **Closed-form variance of the Gambler's Ruin stopping time.**
    Combining the quartic optional-stopping equation
    `k^4 = N^3 k - 6 N^2 W + 3 E[τ²] + 2 E[τ]` (with `E[τ] = k(N-k)`,
    `E[S_τ^4] = N^3 k`, `E[τ S_τ^2] = N^2 W`) and the cubic relation
    `k^3 = N^2 k - 3 N W`, the unknown `W` cancels and

        Var(τ) = E[τ²] - E[τ]² = (1/3) · k (N-k) (N^2 - 2 N k + 2 k^2 - 2).

    Here `Eτ2` denotes `E[τ²]`; the variance is `Eτ2 - (k(N-k))^2`. -/
theorem variance_closed_form (N k Eτ2 W : ℝ)
    (hcubic : k ^ 3 = N ^ 2 * k - 3 * (N * W))
    (hquartic : k ^ 4 =
      N ^ 3 * k - 6 * (N ^ 2 * W) + 3 * Eτ2 + 2 * (k * (N - k))) :
    3 * (Eτ2 - (k * (N - k)) ^ 2) =
      k * (N - k) * (N ^ 2 - 2 * N * k + 2 * k ^ 2 - 2) := by
  linear_combination -hquartic + 2 * N * hcubic

/-- The degenerate single-step case `k = 1, N = 2`: the walk is absorbed
    after exactly one step, so `τ ≡ 1` and `Var(τ) = 0`. The closed form
    returns `0`, a consistency check on `variance_closed_form`. -/
theorem variance_closed_form_degenerate :
    (1 : ℝ) * (2 - 1) * (2 ^ 2 - 2 * 2 * 1 + 2 * 1 ^ 2 - 2) / 3 = 0 := by
  norm_num

end FairGamesOQ02OQ03
