/-
# Markov Equation — the Vieta ascent grows at least geometrically (OQ-06-OQ-01)

The parent leaf `Proofs.MarkovEquationOQ06` builds the canonical **ascent
sequence** of Markov triples rooted at `(1,1,1)`,

  `(1,1,1) → (1,1,2) → (1,2,5) → (2,5,29) → ⋯`,

by Vieta-jumping the smallest coordinate of a sorted triple
(`ascent (a,b,c) = (b, c, 3bc − a)`), and proves the top coordinate is *strictly*
increasing (`seq_top_strictMono`), whence the Markov solution set is infinite
(`markov_infinite`).

Strict monotonicity alone is only a `+1`-per-step bound. This file supplies the
**quantitative** refinement flagged as an open question on the parent entry: the
ascent does not merely increase the top coordinate, it **at least doubles** it,
so the top coordinate of `seq n` is at least `2 ^ n`.

## The doubling step

On a sorted Markov triple `1 ≤ a ≤ b ≤ c` the new top coordinate is `3bc − a`,
and

  `3bc − a  ≥  3bc − c  =  3c(b − 1) + 2c  ≥  2c`,

using `a ≤ c`, `b ≥ 1`, `c ≥ 1`.  Hence each step multiplies the maximum by at
least `2` (`two_mul_top_le_succ`), and an easy induction from `(seq 0).2.2 = 1`
gives the geometric lower bound

  `2 ^ n ≤ (seq n).2.2`        (`seq_top_ge_two_pow`).

As an immediate consequence the top coordinates are **unbounded**
(`seq_top_unbounded`): for every bound `B` some Markov triple in the ascent
sequence has top coordinate exceeding `B`.  This is the elementary growth input
underlying quantitative statements about Markov numbers (e.g. that there are only
finitely many below any bound, the starting point of Zagier's asymptotic count).

Everything is axiom-free over `ℤ` and reuses the parent's `seq`/`seq_spec`.
-/
import Mathlib
import Proofs.MarkovEquationOQ06

namespace MarkovEquationOQ06OQ01

open MarkovEquationOQ06 MarkovEquation

/-- **The ascent at least doubles the top coordinate.** For every `n`,

  `2 · (seq n).2.2 ≤ (seq (n+1)).2.2`.

On the sorted Markov triple `(seq n) = (a,b,c)` the successor's top coordinate is
`3bc − a`, and `3bc − a ≥ 2c` because `a ≤ c`, `b ≥ 1`, `c ≥ 1`
(`3bc − a − 2c ≥ 3c(b−1) ≥ 0`). -/
theorem two_mul_top_le_succ (n : ℕ) :
    2 * (seq n).2.2 ≤ (seq (n + 1)).2.2 := by
  obtain ⟨_, h1, hab, hbc⟩ := seq_spec n
  -- abbreviations for the three coordinates of `seq n`
  have hb1 : (1 : ℤ) ≤ (seq n).2.1 := le_trans h1 hab
  have hac : (seq n).1 ≤ (seq n).2.2 := le_trans hab hbc
  have hc0 : (0 : ℤ) ≤ (seq n).2.2 := le_trans (by norm_num) (le_trans hb1 hbc)
  -- the successor's top coordinate is `3·b·c − a`, definitionally
  have hval : (seq (n + 1)).2.2
      = 3 * (seq n).2.1 * (seq n).2.2 - (seq n).1 := rfl
  rw [hval]
  -- `3bc − a − 2c ≥ 3c(b−1) ≥ 0`
  nlinarith [mul_nonneg hc0 (by linarith : (0 : ℤ) ≤ (seq n).2.1 - 1), hac]

/-- **Geometric lower bound.** The top coordinate of the `n`-th ascent triple is
at least `2 ^ n`:

  `(2 : ℤ) ^ n ≤ (seq n).2.2`.

Immediate induction from `(seq 0).2.2 = 1` using the doubling step
`two_mul_top_le_succ`. -/
theorem seq_top_ge_two_pow (n : ℕ) : (2 : ℤ) ^ n ≤ (seq n).2.2 := by
  induction n with
  | zero => rw [seq_zero]; norm_num
  | succ n ih =>
    have hstep := two_mul_top_le_succ n
    have hdouble : (2 : ℤ) * 2 ^ n ≤ 2 * (seq n).2.2 :=
      mul_le_mul_of_nonneg_left ih (by norm_num)
    calc (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
      _ ≤ 2 * (seq n).2.2 := hdouble
      _ ≤ (seq (n + 1)).2.2 := hstep

/-- **The top coordinates are unbounded.** For every bound `B` there is an ascent
triple whose top coordinate exceeds `B`.  (Consequence of the geometric bound and
archimedeanity of `ℤ`.) -/
theorem seq_top_unbounded (B : ℤ) : ∃ n, B < (seq n).2.2 := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B (by norm_num : (1 : ℤ) < 2)
  exact ⟨n, lt_of_lt_of_le hn (seq_top_ge_two_pow n)⟩

end MarkovEquationOQ06OQ01
