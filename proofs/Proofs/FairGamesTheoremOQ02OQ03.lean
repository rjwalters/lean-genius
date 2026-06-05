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

  Strategy for E[τ²] (next iteration):
  By Doob's optional stopping at τ, `E[M_τ] = M_0 = k^4`. Expanding,
      k^4 = E[S_τ^4] - 6 E[τ · S_τ^2] + 3 E[τ^2] + 2 E[τ].
  Since `S_τ ∈ {0, N}` with `P(S_τ = N) = k/N`,
      E[S_τ^4] = N^3 · k,   E[τ · S_τ^2] = N^2 · E[τ · 𝟙_{S_τ = N}].
  This reduces the problem to computing `E[τ · 𝟙_{S_τ = N}]`, the
  expected hitting time of the upper barrier (weighted by winning).

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

end FairGamesOQ02OQ03
