/-
Stirling Numbers of the Second Kind: the four-block column
        S(n,4) = (4^(n-1) − 3^n + 3·2^(n-1) − 1)/6   for n ≥ 4.

Source: Open question from the stirling-second-kind gallery family
        (parent `stirling-second-kind-oq-01-oq-01`, open question #1)
Status: VERIFIED (0 axioms, 0 sorries)

The grandparent entry solves the two-block column S(n,2) = 2^(n-1) − 1 and the
parent `stirling-second-kind-oq-01-oq-01` solves the three-block column

      S(n, 3) = (3^(n-1) + 1)/2 − 2^(n-1)     for n ≥ 3,

both by the *recurrence-to-geometric-sum method*: Pascal's rule specialised to a
fixed column `k` gives the inhomogeneous geometric recursion

      S(m+1, k) = k·S(m, k) + S(m, k−1),

whose forcing term is the previously-solved column `k−1`. This entry closes the
next open question: does the **fourth** column admit a comparably clean closed
form obtained by the *same* method? It does. The recurrence is

      S(m+1, 4) = 4·S(m, 4) + S(m, 3),

geometric with ratio 4 and forcing term the three-block column. Solving it gives

      S(n, 4) = (4^(n-1) − 3^n + 3·2^(n-1) − 1)/6     for n ≥ 4.

To stay inside `ℕ` (truncated subtraction) we work with the subtraction-free
invariant

      6·S(n, 4) + 3^n + 1 = 4^(n-1) + 3·2^(n-1),

established by induction using the parent's three-block invariant
`2·S(n,3) + 2^n = 3^(n-1) + 1` as the forcing term. The closed (division) form
follows because the right-hand side minus `3^n + 1` is exactly `6·S(n,4)`.

We prove:
1. `four_pow_gt`                       — 3·2^(m+3) ≤ 4^(m+3) (positivity helper)
2. `three_pow_add_two_le_four_col`     — 3^(m+4) + 2 ≤ 4^(m+3) + 3·2^(m+3) (positivity)
3. `six_mul_stirlingSecond_four_add`   — 6·S(m+4,4) + 3^(m+4) + 1 = 4^(m+3) + 3·2^(m+3) (invariant, by induction)
4. `six_mul_stirlingSecond_four`       — 6·S(n,4) + 3^n + 1 = 4^(n-1) + 3·2^(n-1) for n ≥ 4 (subtraction-free form)
5. `stirlingSecond_four_closed`        — S(n,4) = (4^(n-1) + 3·2^(n-1) − 3^n − 1)/6 for n ≥ 4 (textbook form)
6. `stirlingSecond_four_pos`           — there is always a four-block partition (n ≥ 4)
-/

import Mathlib
import Proofs.StirlingSecondKindOQ01OQ01

open Nat

namespace StirlingSecondKindOQ01OQ01OQ01

/-- **Power comparison** `3·2^(m+3) ≤ 4^(m+3)`. Since `4^(m+3) = 2^(m+3)·2^(m+3)`
and `2^(m+3) ≥ 8 ≥ 3`, the factor `2^(m+3)` dominates the constant `3`. Proved by
induction; the step multiplies both sides by `2`. -/
theorem four_pow_gt (m : ℕ) : 3 * 2 ^ (m + 3) ≤ 4 ^ (m + 3) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have e1 : 2 ^ (m + 1 + 3) = 2 * 2 ^ (m + 3) := by ring
    have e2 : 4 ^ (m + 1 + 3) = 4 * 4 ^ (m + 3) := by ring
    rw [e1, e2]
    omega

/-- **Column comparison with margin** `3^(m+4) + 2 ≤ 4^(m+3) + 3·2^(m+3)`, i.e.
`3^n + 2 ≤ 4^(n-1) + 3·2^(n-1)` for `n ≥ 4`. In particular `3^n < 4^(n-1) + 3·2^(n-1)`:
the four-block invariant's right-hand side strictly exceeds `3^n + 1`, forcing
`6·S(n,4) ≥ 1` and hence `S(n,4) > 0`. The small margin `+2` is all positivity needs;
the true gap is `≥ 7` at `n = 4` and grows. Proved by induction, using `four_pow_gt`
in the step. Note `4^(n-1)` alone does *not* dominate `3^n` (at `n = 4`, `64 < 81`),
so the second geometric mode `3·2^(n-1)` is essential. -/
theorem three_pow_add_two_le_four_col (m : ℕ) :
    3 ^ (m + 4) + 2 ≤ 4 ^ (m + 3) + 3 * 2 ^ (m + 3) := by
  induction m with
  | zero => decide
  | succ m ih =>
    have h := four_pow_gt m
    have e1 : 3 ^ (m + 1 + 4) = 3 * 3 ^ (m + 4) := by ring
    have e2 : 4 ^ (m + 1 + 3) = 4 * 4 ^ (m + 3) := by ring
    have e3 : 2 ^ (m + 1 + 3) = 2 * 2 ^ (m + 3) := by ring
    rw [e1, e2, e3]
    omega

/-- **Four-block invariant, shifted form.** For every `n`,

      6·S(n+4, 4) + 3^(n+4) + 1 = 4^(n+3) + 3·2^(n+3).

Proof by induction using the Pascal recurrence `S(m+1,4) = 4·S(m,4) + S(m,3)`
with the three-block forcing term `2·S(m,3) + 2^m = 3^(m-1) + 1` imported from the
parent entry. The recursion `a(n+1) = 4·a(n) + S(n+4,3)` on `a(n) = S(n+4,4)` is the
geometric recursion whose invariant is displayed above. -/
theorem six_mul_stirlingSecond_four_add (n : ℕ) :
    6 * Nat.stirlingSecond (n + 4) 4 + 3 ^ (n + 4) + 1
      = 4 ^ (n + 3) + 3 * 2 ^ (n + 3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    -- Pascal recurrence specialised to the fourth column.
    have key : Nat.stirlingSecond (n + 1 + 4) 4
        = 4 * Nat.stirlingSecond (n + 4) 4 + Nat.stirlingSecond (n + 4) 3 :=
      Nat.stirlingSecond_succ_succ (n + 4) 3
    -- Forcing term: the three-block invariant `2·S(n+4,3) + 2^(n+4) = 3^(n+3) + 1`.
    have h3 : 2 * Nat.stirlingSecond (n + 4) 3 + 2 ^ (n + 4) = 3 ^ (n + 3) + 1 :=
      StirlingSecondKindOQ01OQ01.two_mul_stirlingSecond_three_add (n + 1)
    -- Exponential doubling/tripling relations so `omega` can reason linearly.
    have e4  : 4 ^ (n + 1 + 3) = 4 * 4 ^ (n + 3) := by ring
    have e3a : 3 ^ (n + 1 + 4) = 3 * 3 ^ (n + 4) := by ring
    have e3b : 3 ^ (n + 4) = 3 * 3 ^ (n + 3) := by ring
    have e2a : 2 ^ (n + 1 + 3) = 2 * 2 ^ (n + 3) := by ring
    have e2b : 2 ^ (n + 4) = 2 * 2 ^ (n + 3) := by ring
    rw [key]
    omega

/-- **Four-block invariant, textbook range.** For `n ≥ 4`,

      6·S(n, 4) + 3^n + 1 = 4^(n-1) + 3·2^(n-1).

This subtraction-free identity packages the closed form; it specialises the
shifted invariant `six_mul_stirlingSecond_four_add` via `n = m + 4`. -/
theorem six_mul_stirlingSecond_four {n : ℕ} (hn : 4 ≤ n) :
    6 * Nat.stirlingSecond n 4 + 3 ^ n + 1 = 4 ^ (n - 1) + 3 * 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  -- `m + 4 - 1` is definitionally `m + 3`.
  show 6 * Nat.stirlingSecond (m + 4) 4 + 3 ^ (m + 4) + 1
      = 4 ^ (m + 3) + 3 * 2 ^ (m + 3)
  exact six_mul_stirlingSecond_four_add m

/-- **Four-block column, closed form.** For `n ≥ 4` the number of partitions of an
`n`-element set into exactly four nonempty blocks is

      S(n, 4) = (4^(n-1) + 3·2^(n-1) − 3^n − 1)/6

(the textbook `(4^(n-1) − 3^n + 3·2^(n-1) − 1)/6`, written with the additions first
so every truncated subtraction stays non-negative). The `ℕ`-division is exact:
`4^(n-1) + 3·2^(n-1) − 3^n − 1 = 6·S(n,4)` by the invariant. -/
theorem stirlingSecond_four_closed {n : ℕ} (hn : 4 ≤ n) :
    Nat.stirlingSecond n 4 = (4 ^ (n - 1) + 3 * 2 ^ (n - 1) - 3 ^ n - 1) / 6 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h := six_mul_stirlingSecond_four_add m
  show Nat.stirlingSecond (m + 4) 4
      = (4 ^ (m + 3) + 3 * 2 ^ (m + 3) - 3 ^ (m + 4) - 1) / 6
  omega

/-- **Existence of a four-block partition.** Any set with at least four elements
can be split into four nonempty blocks, i.e. `S(n,4) > 0` for `n ≥ 4`. Positivity
comes from `three_pow_add_two_le_four_col` (`3^n + 2 ≤ 4^(n-1) + 3·2^(n-1)`), which
forces `6·S(n,4) ≥ 1` and hence `S(n,4) ≥ 1`. -/
theorem stirlingSecond_four_pos {n : ℕ} (hn : 4 ≤ n) :
    0 < Nat.stirlingSecond n 4 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  have h := six_mul_stirlingSecond_four_add m
  have hlt := three_pow_add_two_le_four_col m
  omega

end StirlingSecondKindOQ01OQ01OQ01
