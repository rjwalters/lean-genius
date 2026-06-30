/-
Stirling Numbers of the Second Kind: the three-block column  S(n,3) = (3^(n-1) + 1)/2 − 2^(n-1)

Source: Open question from the stirling-second-kind gallery family
        (parent `stirling-second-kind-oq-01`, open question #1)
Status: VERIFIED (0 axioms, 0 sorries)

The parent entry derives the textbook closed form for the two-block column,

      S(n, 2) = 2^(n-1) − 1     for n ≥ 2,

purely from the inhomogeneous geometric recurrence
`S(m+1,2) = 2·S(m,2) + S(m,1) = 2·S(m,2) + 1`, and asks (open question #1)
whether the *third* column admits a comparably clean closed form obtainable by
the **same recurrence-to-geometric-sum method**. It does:

      S(n, 3) = (3^(n-1) + 1)/2 − 2^(n-1)     for n ≥ 3.

The driving recurrence is again Pascal specialised to a fixed column,

      S(m+1, 3) = 3·S(m, 3) + S(m, 2) = 3·S(m, 3) + (2^(m-1) − 1),

an inhomogeneous geometric recursion with ratio 3 and the previous column as
forcing term. Solving it gives the stated closed form. To stay inside `ℕ` we work
with the subtraction-free invariant

      2·S(n, 3) + 2^n = 3^(n-1) + 1,

which we establish by induction and from which the division form follows (the
right-hand side is always even, being `2·(S(n,3) + 2^(n-1))`).

We prove:
1. `stirlingSecond_two_add`            — S(n+2,2) = 2^(n+1) − 1 (re-derived inline, forcing term)
2. `two_pow_le_three_pow`              — 2^(n+3) ≤ 3^(n+2) (used for positivity)
3. `two_mul_stirlingSecond_three_add`  — 2·S(n+3,3) + 2^(n+3) = 3^(n+2) + 1 (the invariant, by induction)
4. `two_mul_stirlingSecond_three`      — 2·S(n,3) + 2^n = 3^(n-1) + 1 for n ≥ 3 (subtraction-free form)
5. `stirlingSecond_three_closed`       — S(n,3) = (3^(n-1)+1)/2 − 2^(n-1) for n ≥ 3 (textbook form)
6. `stirlingSecond_three_pos`          — there is always a three-block partition (n ≥ 3)
-/

import Mathlib

open Nat

namespace StirlingSecondKindOQ01OQ01

/-- **Two-block column, shifted form** (the forcing term of the three-block
recurrence). The number of partitions of an `(n+2)`-element set into two nonempty
blocks is `2^(n+1) − 1`. Re-derived inline from the Pascal recurrence
`S(m+1,2) = 2·S(m,2) + S(m,1)` with `S(m,1) = 1`, keeping the file self-contained. -/
theorem stirlingSecond_two_add (n : ℕ) :
    Nat.stirlingSecond (n + 2) 2 = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have key : Nat.stirlingSecond (n + 1 + 2) 2
        = 2 * Nat.stirlingSecond (n + 2) 2 + Nat.stirlingSecond (n + 2) 1 :=
      Nat.stirlingSecond_succ_succ (n + 2) 1
    have hone : Nat.stirlingSecond (n + 2) 1 = 1 := Nat.stirlingSecond_one_right (n + 1)
    rw [key, ih, hone]
    have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
    omega

/-- **Exponential dominance** `2^(n+3) ≤ 3^(n+2)`, the comparison that makes the
three-block count positive (equivalently `3^(n-1) ≥ 2^n` for `n ≥ 3`). Proved by
induction: the inductive step multiplies `2^(n+3) ≤ 3^(n+2)` by `2 ≤ 3`. -/
theorem two_pow_le_three_pow (n : ℕ) : 2 ^ (n + 3) ≤ 3 ^ (n + 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have e1 : 2 ^ (n + 1 + 3) = 2 * 2 ^ (n + 3) := by ring
    have e2 : 3 ^ (n + 1 + 2) = 3 * 3 ^ (n + 2) := by ring
    rw [e1, e2]
    nlinarith [ih, Nat.one_le_pow (n + 2) 3 (by norm_num)]

/-- **Three-block invariant, shifted form.** For every `n`,

      2·S(n+3, 3) + 2^(n+3) = 3^(n+2) + 1.

Proof by induction using the Pascal recurrence
`S(m+1,3) = 3·S(m,3) + S(m,2)` with the two-block forcing term
`S(m,2) = 2^(m-1) − 1`. The recursion `a(n+1) = 3·a(n) + (2^(n+2) − 1)` on
`a(n) = S(n+3,3)` is the geometric recursion whose invariant is displayed above. -/
theorem two_mul_stirlingSecond_three_add (n : ℕ) :
    2 * Nat.stirlingSecond (n + 3) 3 + 2 ^ (n + 3) = 3 ^ (n + 2) + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    -- Pascal recurrence specialised to the third column.
    have key : Nat.stirlingSecond (n + 1 + 3) 3
        = 3 * Nat.stirlingSecond (n + 3) 3 + Nat.stirlingSecond (n + 3) 2 :=
      Nat.stirlingSecond_succ_succ (n + 3) 2
    -- Forcing term: the two-block column value S(n+3,2) = 2^(n+2) − 1.
    have h2col : Nat.stirlingSecond (n + 3) 2 = 2 ^ (n + 2) - 1 :=
      stirlingSecond_two_add (n + 1)
    have e1 : 2 ^ (n + 1 + 3) = 2 * 2 ^ (n + 3) := by ring
    have e2 : 2 ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
    have e3 : 3 ^ (n + 1 + 2) = 3 * 3 ^ (n + 2) := by ring
    have hp : 1 ≤ 2 ^ (n + 2) := Nat.one_le_two_pow
    rw [key]
    omega

/-- **Three-block invariant, textbook range.** For `n ≥ 3`,

      2·S(n, 3) + 2^n = 3^(n-1) + 1.

This subtraction-free identity packages the closed form; it specialises the
shifted invariant `two_mul_stirlingSecond_three_add` via `n = m + 3`. -/
theorem two_mul_stirlingSecond_three {n : ℕ} (hn : 3 ≤ n) :
    2 * Nat.stirlingSecond n 3 + 2 ^ n = 3 ^ (n - 1) + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact two_mul_stirlingSecond_three_add m

/-- **Three-block column, closed form.** For `n ≥ 3` the number of partitions of an
`n`-element set into exactly three nonempty blocks is

      S(n, 3) = (3^(n-1) + 1)/2 − 2^(n-1).

The `ℕ`-division is exact: `3^(n-1) + 1 = 2·(S(n,3) + 2^(n-1))` is even, so halving
recovers `S(n,3) + 2^(n-1)` on the nose. -/
theorem stirlingSecond_three_closed {n : ℕ} (hn : 3 ≤ n) :
    Nat.stirlingSecond n 3 = (3 ^ (n - 1) + 1) / 2 - 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := two_mul_stirlingSecond_three_add m
  have e : (2 : ℕ) ^ (m + 3) = 2 * 2 ^ (m + 2) := by ring
  -- `m + 3 - 1` is definitionally `m + 2`.
  show Nat.stirlingSecond (m + 3) 3 = (3 ^ (m + 2) + 1) / 2 - 2 ^ (m + 2)
  omega

/-- **Existence of a three-block partition.** Any set with at least three elements
can be split into three nonempty blocks, i.e. `S(n,3) > 0` for `n ≥ 3`. Positivity
comes from `2^n ≤ 3^(n-1)` (`two_pow_le_three_pow`), which forces the invariant's
right-hand side strictly above `2^n`. -/
theorem stirlingSecond_three_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < Nat.stirlingSecond n 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := two_mul_stirlingSecond_three_add m
  have hge := two_pow_le_three_pow m
  omega

end StirlingSecondKindOQ01OQ01
