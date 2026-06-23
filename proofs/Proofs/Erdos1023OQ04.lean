/-
# Erdős Problem #1023 — Elementary growth brackets for the union-free maximum

## Background

Let `F(n)` be the maximum size of a family of subsets of `{1, …, n}` in which no set
is the union of (two or more distinct) other members of the family ("union-free").
Erdős asked whether `F(n) ~ c · 2ⁿ / √n`.  The answer is **yes**: the middle layer
(all subsets of size `⌊n/2⌋`) is union-free and, by a theorem of Erdős–Kleitman, optimal,
so
                    F(n) = C(n, ⌊n/2⌋),
the central binomial coefficient.  This identity is recorded in the parent gallery entry
`erdos-1023` (`Erdos1023Problem.lean`).

The parent entry establishes the asymptotic `F(n) ~ √(2/π) · 2ⁿ / √n` only through an
**axiom** (`stirling_central` / `unionFreeMax_asymptotic`), because the precise constant
requires Stirling's formula.  The qualitative growth, however, does **not** need Stirling.

## What this file adds (0 axioms, fully verified)

Taking the established value `F(n) = C(n, ⌊n/2⌋)` as the *definition* of `unionFreeMax`,
we prove rigorous, completely elementary growth brackets:

* `central_le_pow`            : `F(n) ≤ 2ⁿ`                       (trivial upper bound)
* `pow_le_succ_mul_central`   : `2ⁿ ≤ (n+1) · F(n)`              ⟶  `F(n) ≥ 2ⁿ / (n+1)`
* `unionFreeMax_bracket`      : both bounds together
* `unionFreeMax_unbounded`    : `F(n) → ∞`  (∀ M, ∃ n, M ≤ F(n))

The lower bound is the interesting direction: averaging the binomial identity
`∑_{m≤n} C(n,m) = 2ⁿ` against the maximality of the central column
(`Nat.choose_le_middle`) gives `2ⁿ ≤ (n+1)·C(n,⌊n/2⌋)` in one line.  Hence
`2ⁿ/(n+1) ≤ F(n) ≤ 2ⁿ`, pinning down the growth of `F` up to a polynomial factor
**without any appeal to Stirling's formula** — replacing the qualitative content of the
parent's asymptotic axiom by a machine-checked elementary statement.

The divergence `F(n) → ∞` is proved purely over `ℕ` using `choose_le_centralBinom`:
`F(2n) = C(2n,n) = centralBinom n ≥ C(2n,1) = 2n`.

We do **not** reprove the Erdős–Kleitman optimality (the hard, axiomatized direction in
the parent); this file is solely about the elementary growth of the central column.
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

namespace Erdos1023OQ04

open Finset

/-- The maximum size of a union-free family of subsets of `{1, …, n}`.
By Erdős–Kleitman this equals the size of the middle layer, the central binomial
coefficient `C(n, ⌊n/2⌋)` (see the parent entry `erdos-1023`). We take that value
as the definition here and study its elementary growth. -/
def unionFreeMax (n : ℕ) : ℕ := Nat.choose n (n / 2)

@[simp] theorem unionFreeMax_def (n : ℕ) : unionFreeMax n = Nat.choose n (n / 2) := rfl

/-- The union-free maximum is positive: the empty set is always available. -/
theorem unionFreeMax_pos (n : ℕ) : 0 < unionFreeMax n :=
  Nat.choose_pos (Nat.div_le_self n 2)

/-- Trivial upper bound: a union-free family is a family of subsets, so its size is at
most `2ⁿ`. Concretely, the central column is one term of the binomial sum. -/
theorem central_le_pow (n : ℕ) : unionFreeMax n ≤ 2 ^ n :=
  Nat.choose_le_two_pow n (n / 2)

/-- **Key elementary lower bound.** Summing the binomial identity
`∑_{m ≤ n} C(n,m) = 2ⁿ` and bounding every term by the maximal central column
`C(n, ⌊n/2⌋)` gives `2ⁿ ≤ (n+1) · F(n)`. Equivalently `F(n) ≥ 2ⁿ / (n+1)`, an
exponential lower bound that needs no Stirling estimate. -/
theorem pow_le_succ_mul_central (n : ℕ) : 2 ^ n ≤ (n + 1) * unionFreeMax n := by
  have h : (∑ m ∈ range (n + 1), n.choose m) ≤ ∑ _m ∈ range (n + 1), n.choose (n / 2) :=
    Finset.sum_le_sum (fun m _ => Nat.choose_le_middle m n)
  calc 2 ^ n = ∑ m ∈ range (n + 1), n.choose m := (Nat.sum_range_choose n).symm
    _ ≤ ∑ _m ∈ range (n + 1), n.choose (n / 2) := h
    _ = (n + 1) * unionFreeMax n := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, unionFreeMax_def]

/-- The two elementary brackets together:
`2ⁿ ≤ (n+1)·F(n)` and `F(n) ≤ 2ⁿ`. These pin down the growth of `F` up to a
polynomial factor, with no use of Stirling's formula. -/
theorem unionFreeMax_bracket (n : ℕ) :
    2 ^ n ≤ (n + 1) * unionFreeMax n ∧ unionFreeMax n ≤ 2 ^ n :=
  ⟨pow_le_succ_mul_central n, central_le_pow n⟩

/-- Real-valued form of the lower bracket: `2ⁿ / (n+1) ≤ F(n)`. -/
theorem pow_div_succ_le_central (n : ℕ) :
    (2 : ℝ) ^ n / (n + 1) ≤ (unionFreeMax n : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hpos]
  have := pow_le_succ_mul_central n
  have hcast : ((2 ^ n : ℕ) : ℝ) ≤ (((n + 1) * unionFreeMax n : ℕ) : ℝ) := by
    exact_mod_cast this
  push_cast at hcast
  linarith [hcast]

/-- `F(2n) = C(2n, n) = centralBinom n`, the central binomial coefficient. -/
theorem unionFreeMax_two_mul (n : ℕ) : unionFreeMax (2 * n) = Nat.centralBinom n := by
  unfold unionFreeMax Nat.centralBinom
  rw [Nat.mul_div_cancel_left n (by norm_num : 0 < 2)]

/-- A clean elementary linear lower bound on the even-index subsequence:
`2n ≤ F(2n)`. (`F(2n) = C(2n,n) ≥ C(2n,1) = 2n`.) -/
theorem two_mul_le_unionFreeMax_two_mul (n : ℕ) : 2 * n ≤ unionFreeMax (2 * n) := by
  rw [unionFreeMax_two_mul]
  have h : Nat.choose (2 * n) 1 ≤ Nat.centralBinom n := Nat.choose_le_centralBinom 1 n
  rwa [Nat.choose_one_right] at h

/-- **Divergence.** The union-free maximum is unbounded: `F(n) → ∞`.
Proved purely over `ℕ` via the even subsequence `F(2M) ≥ 2M ≥ M`. -/
theorem unionFreeMax_unbounded : ∀ M : ℕ, ∃ n, M ≤ unionFreeMax n := by
  intro M
  refine ⟨2 * M, ?_⟩
  calc M ≤ 2 * M := by omega
    _ ≤ unionFreeMax (2 * M) := two_mul_le_unionFreeMax_two_mul M

/-! ### Concrete values

`F(n) = C(n, ⌊n/2⌋)`: `1, 1, 2, 3, 6, 10, 20, …` for `n = 0, 1, 2, 3, 4, 5, 6`. -/

example : unionFreeMax 0 = 1 := by decide
example : unionFreeMax 1 = 1 := by decide
example : unionFreeMax 2 = 2 := by decide
example : unionFreeMax 3 = 3 := by decide
example : unionFreeMax 4 = 6 := by decide
example : unionFreeMax 5 = 10 := by decide
example : unionFreeMax 6 = 20 := by decide

/-- Sanity check of the lower bracket at `n = 6`: `2⁶ = 64 ≤ 7 · 20 = 140`. -/
example : 2 ^ 6 ≤ (6 + 1) * unionFreeMax 6 := pow_le_succ_mul_central 6

end Erdos1023OQ04
