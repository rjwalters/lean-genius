/-
Uniform Osculator Function for Truncation Divisibility
(Open Question: divisibility-by-3-oq-01-oq-02)
Date: 2026-07-01
Research: divisibility-by-3-oq-01-oq-02

The parent entry `DivisibilityTruncationGeneral.lean` proves two parametric
osculator theorems (`truncation_pos`, `truncation_neg`) and instantiates them
by hand for each divisor coprime to 10 (7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
43, …). Each instance requires the human to SUPPLY the osculator constant `c`
and a witness `d ∣ 10c ± 1`.

This file removes that per-divisor hand-work. We give a single **computable**
osculator function

    osculator d := Int.gcdA 10 d      -- a Bézout coefficient of 10 modulo d

and prove, once and for all, that it satisfies the positive-osculator relation
`d ∣ 10 · osculator d − 1` for every `d` coprime to 10. Consequently

    truncation_uniform : IsCoprime (d:ℤ) 10 →
      (d ∣ n ↔ d ∣ (n/10 + osculator d · (n%10)))

covers EVERY divisor coprime to 10 with no supplied constant — the only side
goal at a concrete divisor is `IsCoprime (d:ℤ) 10`, discharged by `decide`.

This subsumes the hand-written coverage extension (23, 29, 31, 37, 41, 43) of
the parent OQ: those primes, and all others, are now instances of one theorem
whose osculator is produced automatically from Bézout's identity.
-/

import Proofs.DivisibilityTruncationGeneral
import Mathlib.Tactic

open Nat

namespace DivisibilityBy3OQ01OQ02

open DivisibilityTruncationGeneral

/-
## The Computable Osculator
-/

/-- The (positive) **osculator** of `d`: a Bézout coefficient of `10` modulo `d`.
    For any `d` coprime to `10` this is an inverse of `10` mod `d`, so it
    satisfies `d ∣ 10 · osculator d − 1` (see `osculator_spec`). Unlike the
    hand-supplied constants in the parent file, this is a total computable
    function of `d`. -/
def osculator (d : ℕ) : ℤ := Int.gcdA 10 (d : ℤ)

/-- **Correctness of the osculator.** For every `d` coprime to `10`, the
    computed osculator satisfies the positive-osculator relation
    `d ∣ 10 · osculator d − 1`. This is exactly the hypothesis that the
    parametric `truncation_pos` theorem needs, now discharged automatically
    from Bézout's identity rather than by a supplied witness. -/
theorem osculator_spec (d : ℕ) (hcop : IsCoprime (d : ℤ) 10) :
    (d : ℤ) ∣ 10 * osculator d - 1 := by
  -- Bézout: (gcd 10 d : ℤ) = 10 * gcdA 10 d + d * gcdB 10 d
  have hbez := Int.gcd_eq_gcd_ab (10 : ℤ) (d : ℤ)
  -- Coprimality collapses the gcd to 1.
  have hg : Int.gcd (10 : ℤ) (d : ℤ) = 1 := by
    rw [Int.gcd_comm]
    exact (Int.isCoprime_iff_gcd_eq_one).mp hcop
  rw [hg] at hbez
  -- Now  1 = 10 * osculator d + d * gcdB 10 d, so 10 * osculator d - 1 = d * (-gcdB).
  refine ⟨-Int.gcdB (10 : ℤ) (d : ℤ), ?_⟩
  simp only [osculator]
  push_cast at hbez
  linear_combination -hbez

/-
## The Uniform Truncation Rule
-/

/-- **Uniform Truncation Rule.** For *every* `d` coprime to `10`, the truncation
    test holds with the automatically computed osculator:

      d ∣ n  ↔  d ∣ (n/10 + osculator d · (n%10)).

    No osculator constant needs to be supplied: the only hypothesis is
    `IsCoprime (d:ℤ) 10`, which at any concrete divisor is decidable. -/
theorem truncation_uniform (d : ℕ) (n : ℕ) (hcop : IsCoprime (d : ℤ) 10) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / 10) + osculator d * ↑(n % 10)) :=
  truncation_pos d (osculator d) n hcop (osculator_spec d hcop)

/-
## Coverage With Zero Supplied Constants

Every divisor coprime to 10 is now a one-liner: the osculator is produced by
`osculator`, and the sole side goal `IsCoprime (d:ℤ) 10` is closed by `decide`.
Contrast with the parent file, where each of these required a hand-computed
constant and a `⟨k, by norm_num⟩` divisibility witness.
-/

theorem seven_uniform (n : ℕ) :
    (7 : ℤ) ∣ n ↔ (7 : ℤ) ∣ (↑(n / 10) + osculator 7 * ↑(n % 10)) :=
  truncation_uniform 7 n (by decide)

theorem thirteen_uniform (n : ℕ) :
    (13 : ℤ) ∣ n ↔ (13 : ℤ) ∣ (↑(n / 10) + osculator 13 * ↑(n % 10)) :=
  truncation_uniform 13 n (by decide)

theorem nineteen_uniform (n : ℕ) :
    (19 : ℤ) ∣ n ↔ (19 : ℤ) ∣ (↑(n / 10) + osculator 19 * ↑(n % 10)) :=
  truncation_uniform 19 n (by decide)

/-- **Extended coverage, uniformly.** The six primes of the parent OQ
    (23, 29, 31, 37, 41, 43) — and indeed every divisor coprime to 10 — are
    covered by a single theorem, with the osculator computed rather than
    supplied. This is the structural upgrade of `extended_truncation_coverage`:
    the parent bundled six hand-crafted instances; here they are six evaluations
    of one uniform rule. -/
theorem extended_coverage_uniform :
    (∀ n : ℕ, (23 : ℤ) ∣ n ↔ (23 : ℤ) ∣ (↑(n / 10) + osculator 23 * ↑(n % 10))) ∧
    (∀ n : ℕ, (29 : ℤ) ∣ n ↔ (29 : ℤ) ∣ (↑(n / 10) + osculator 29 * ↑(n % 10))) ∧
    (∀ n : ℕ, (31 : ℤ) ∣ n ↔ (31 : ℤ) ∣ (↑(n / 10) + osculator 31 * ↑(n % 10))) ∧
    (∀ n : ℕ, (37 : ℤ) ∣ n ↔ (37 : ℤ) ∣ (↑(n / 10) + osculator 37 * ↑(n % 10))) ∧
    (∀ n : ℕ, (41 : ℤ) ∣ n ↔ (41 : ℤ) ∣ (↑(n / 10) + osculator 41 * ↑(n % 10))) ∧
    (∀ n : ℕ, (43 : ℤ) ∣ n ↔ (43 : ℤ) ∣ (↑(n / 10) + osculator 43 * ↑(n % 10))) :=
  ⟨fun n => truncation_uniform 23 n (by decide),
   fun n => truncation_uniform 29 n (by decide),
   fun n => truncation_uniform 31 n (by decide),
   fun n => truncation_uniform 37 n (by decide),
   fun n => truncation_uniform 41 n (by decide),
   fun n => truncation_uniform 43 n (by decide)⟩

/-
## Sanity Checks: the computed osculator gives a correct test

We verify on concrete numbers that reducing `n` via the *computed* osculator
preserves divisibility. `osculator 7 = Int.gcdA 10 7`; whatever value it takes,
`truncation_uniform` guarantees the equivalence, and these examples confirm the
end-to-end computation is sound.
-/

-- 7 ∣ 91:  the uniform rule reduces the test to 7 ∣ (9 + osculator 7 · 1).
example : (7 : ℤ) ∣ 91 ↔ (7 : ℤ) ∣ (↑(91 / 10) + osculator 7 * ↑(91 % 10)) :=
  seven_uniform 91

-- 13 ∣ 169 via the computed osculator.
example : (13 : ℤ) ∣ 169 ↔ (13 : ℤ) ∣ (↑(169 / 10) + osculator 13 * ↑(169 % 10)) :=
  thirteen_uniform 169

end DivisibilityBy3OQ01OQ02
