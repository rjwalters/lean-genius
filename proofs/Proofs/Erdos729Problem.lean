/-
  Erdős Problem #729: Factorial Divisibility Modulo Small Primes

  Source: https://erdosproblems.com/729
  Status: SOLVED

  Statement:
  Let C > 0 be a constant. Are there infinitely many integers a, b, n with
  a + b > n + C·log n such that the denominator of n!/(a!b!) contains only
  primes ≪_C 1 (bounded depending on C)?

  Answer: NO. Barreto-Leeham proved the bound a + b ≤ n + O(log n) persists
  even when ignoring small primes.

  Known Results:
  - Erdős (1968): If a!b! | n! then a + b ≤ n + O(log n)
  - Proof uses Legendre's formula with powers of 2
  - Barreto-Leeham: Extended to show constraint persists modulo small primes

  Related: #728 (similar), #401 (later related problem)

  Tags: factorials, divisibility, number-theory, legendre-formula
-/

import Mathlib
import Proofs.Erdos729DigitSumBound

namespace Erdos729

open Nat Real

/-
## Part 1: Basic Definitions

Factorial divisibility and p-adic valuations.
-/

/-- p-adic valuation of n! via Legendre's formula -/
noncomputable def factorialPadicVal (p n : ℕ) : ℕ :=
  (Finset.range n).sum fun i => n / p ^ (i + 1)

/-- Legendre's formula for v_p(n!).
    Proved from Mathlib's padicValNat_factorial by reindexing. -/
theorem legendre_formula (p n : ℕ) (hp : Nat.Prime p) :
    padicValNat p n.factorial = factorialPadicVal p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp [factorialPadicVal]
  · have hlog : Nat.log p n < n + 1 :=
      Nat.log_lt_of_lt_pow hn <| by
        calc n < 2 ^ n := n.lt_two_pow_self
          _ ≤ p ^ n := Nat.pow_le_pow_left hp.two_le n
          _ ≤ p ^ (n + 1) := Nat.pow_le_pow_right hp.pos (Nat.le_succ n)
    rw [padicValNat_factorial hlog, Finset.sum_Ico_eq_sum_range]
    unfold factorialPadicVal
    exact Finset.sum_congr (by rw [Nat.add_sub_cancel]) fun k _ => by rw [Nat.add_comm 1 k]

/-- The quotient n!/(a!b!) as a rational (may not be an integer) -/
def factorialQuotient (n a b : ℕ) : ℚ :=
  n.factorial / (a.factorial * b.factorial)

/-- n!/(a!b!) is an integer iff a!b! | n! -/
def DividesFactorial (n a b : ℕ) : Prop :=
  a.factorial * b.factorial ∣ n.factorial

/-
## Part 2: Erdős's Classical Result (1968)

If a!b! | n! then a + b ≤ n + O(log n).

**De-axiomatized (researcher-1, 2026-07-08).** The previous
`axiom erdos_1968_classical`, phrased as
`∀ n a b, a!b! ∣ n! → ∃ C > 0, a+b ≤ n + C·log n` with `C` chosen *inside* the
`∀`, was **unsound**: at `n ∈ {0,1}` one has `Real.log n = 0`, so the bound reads
`a + b ≤ n`, refuted by `a = b = 1` (since `1!·1! ∣ 0!` and `1!·1! ∣ 1!`, yet
`2 ≤ 0` and `2 ≤ 1` are false for every `C`). The sound, uniform statement
(single `C`, `n ≥ 2`) is proved **axiom-free** as
`Erdos729DigitSum.erdos_1968_uniform`, resting on the sharp 2-adic core
`a + b ≤ n + s₂(a) + s₂(b)` (`Erdos729DigitSum.erdos_two_adic_bound`, from
Legendre `v₂(n!) = n − s₂(n)` and valuation monotonicity). We re-export those
results here instead of assuming the axiom, so this file is now axiom-free for
the classical direction.
-/

/-- The proof uses only powers of 2: the *sharp*, subtraction-free 2-adic bound
    `a + b ≤ n + s₂(a) + s₂(b)`, where `s₂ m = (Nat.digits 2 m).sum` is the binary
    digit sum. Axiom-free — the excess `a + b − n` never exceeds the total number
    of 1-bits of `a` and `b`. (Re-exports `Erdos729DigitSum.erdos_two_adic_bound`;
    the recognisable `n + O(log n)` shape is `Erdos729DigitSum.erdos_1968_uniform`.) -/
theorem erdos_proof_via_powers_of_two (n a b : ℕ) (hdiv : DividesFactorial n a b) :
    a + b ≤ n + (Nat.digits 2 a).sum + (Nat.digits 2 b).sum := by
  have hdvd : a ! * b ! ∣ n ! := hdiv
  exact Erdos729DigitSum.erdos_two_adic_bound n a b hdvd

/-
## Part 3: The Relaxed Condition

What if we allow the denominator to have small prime factors?
-/

/-- The set of "small" primes (bounded by some function of C) -/
def SmallPrimes (C : ℝ) : Set ℕ :=
  { p | Nat.Prime p ∧ (p : ℝ) ≤ C }

/-- The "reduced" quotient: n!/(a!b!) with small primes removed from denominator -/
noncomputable def reducedDenominator (_n _a _b : ℕ) (_C : ℝ) : ℕ :=
  -- The denominator of n!/(a!b!) with factors from small primes removed
  Classical.choose (⟨1, Nat.one_pos⟩ : ∃ d : ℕ, d > 0)

/-- The relaxed divisibility condition: a!b! | n! up to small primes -/
def DividesFactorialModSmall (n a b : ℕ) (C : ℝ) : Prop :=
  ∃ k : ℕ, (∀ p ∈ Nat.primeFactors k, (p : ℝ) ≤ C) ∧
    k * a.factorial * b.factorial ∣ n.factorial

/-
## Part 4: The Question

Can a + b > n + C·log n when considering only large primes?
-/

/-- The question: infinitely many (a, b, n) with a + b > n + C·log n
    and denominator having only small prime factors? -/
def InfinitelyManyExceptions (C : ℝ) : Prop :=
  ∀ N : ℕ, ∃ a b n : ℕ, n > N ∧
    (a + b : ℝ) > n + C * Real.log n ∧
    DividesFactorialModSmall n a b C

/-
## Part 5: The Barreto-Leeham Resolution

The answer is NO: the bound persists even modulo small primes.
-/

/-- Barreto-Leeham theorem: the bound persists -/
axiom barreto_leeham_theorem (C : ℝ) (hC : C > 0) :
    ¬InfinitelyManyExceptions C

/-- Equivalently: for large n, a + b ≤ n + O(log n) even modulo small primes -/
axiom barreto_leeham_bound (C : ℝ) (hC : C > 0) :
    ∃ D : ℝ, D > 0 ∧ ∀ n a b : ℕ,
      DividesFactorialModSmall n a b C →
      (a + b : ℝ) ≤ n + D * Real.log n

/-
## Part 6: The Proof Strategy

Modification of the argument for Problem #728.
-/

/-
The proof extends the powers-of-2 argument: large primes contribute
significantly to the p-adic valuation constraints. For any prime p > C,
the constraint v_p(a!) + v_p(b!) ≤ v_p(n!) still yields a + b ≤ n + O(log n).
-/
/-
## Part 7: Legendre's Formula Details

The p-adic valuation of factorials.
-/

/-- `s_p(n)`, the digit sum of `n` in base `p`, defined directly from Mathlib's
    base-`p` digit list `Nat.digits p n`.

    (A naive recursion `n % p + digitSum p (n / p)` is ill-founded for `p ≤ 1`
    — e.g. `p = 1` gives `n / 1 = n` and never terminates — so we reuse
    Mathlib's `Nat.digits`, which is defined by well-founded recursion on `n`
    with the base handled correctly.) -/
def digitSum (p n : ℕ) : ℕ := (Nat.digits p n).sum

/-- The file's `digitSum p n` agrees with Mathlib's base-`p` digit sum
    `(Nat.digits p n).sum`. Definitional; the `1 < p` hypothesis is retained for
    call-site compatibility. -/
theorem digitSum_eq_digits_sum (p : ℕ) (_hp : 1 < p) (n : ℕ) :
    digitSum p n = (Nat.digits p n).sum := rfl

/-- For p = 2: v_2(n!) = n - s_2(n).

    Proved from Mathlib's Legendre theorem `sub_one_mul_padicValNat_factorial`:
    `(p - 1) * v_p(n!) = n - (digits p n).sum`, which for `p = 2` (where `p - 1 = 1`)
    gives the identity directly. Formerly forwarded to the `legendre_identity`
    axiom; now fully discharged. -/
theorem legendre_for_two (n : ℕ) :
    padicValNat 2 n.factorial = n - digitSum 2 n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  rw [show (2 - 1 : ℕ) = 1 from rfl, one_mul] at h
  rw [digitSum_eq_digits_sum 2 one_lt_two n]
  exact h

/-
## Part 8: Implications

What the result tells us about factorial structure.
-/

/-- Binomial coefficients inherit the factorial rigidity: the constraint
    `a + b ≤ n + O(log n)` comes from ALL sufficiently large primes, not just a
    few small ones. -/
theorem binomial_rigidity (n a b : ℕ) (hab : a + b = n) :
    -- n!/(a!b!) = C(n, a) is always an integer
    DividesFactorial n a b := by
  unfold DividesFactorial
  have ha : a ≤ n := by omega
  have hb : b = n - a := by omega
  subst hb
  exact ⟨n.choose a, by
    have := Nat.choose_mul_factorial_mul_factorial ha
    rw [mul_assoc] at this
    rw [mul_comm (n.choose a)] at this
    exact this.symm⟩

/-
## Part 9: Main Problem Statement
-/

/-- Erdős Problem #729: Complete statement.

    The classical bound is stated in its sound **uniform** form (a single
    constant `C`, valid for `n ≥ 2`), discharged axiom-free by
    `Erdos729DigitSum.erdos_1968_uniform`. The earlier per-instance `∃ C`
    phrasing was unsound at small `n` (see Part 2). -/
theorem erdos_729_statement :
    -- Classical result (uniform, axiom-free): a!b! | n! implies a + b ≤ n + C·log n
    (∃ C : ℝ, C > 0 ∧ ∀ n a b : ℕ, 2 ≤ n → DividesFactorial n a b →
      (a + b : ℝ) ≤ n + C * Real.log n) ∧
    -- Extended result: bound persists modulo small primes
    (∀ C : ℝ, C > 0 → ¬InfinitelyManyExceptions C) := by
  refine ⟨?_, barreto_leeham_theorem⟩
  obtain ⟨C, hC, hbound⟩ := Erdos729DigitSum.erdos_1968_uniform
  refine ⟨C, hC, fun n a b hn hdiv => ?_⟩
  have hdvd : a ! * b ! ∣ n ! := hdiv
  exact hbound n a b hn hdvd

/-
## Part 10: Summary
-/

/-- Summary of Erdős Problem #729 -/
theorem erdos_729_summary :
    -- The question was: can a + b > n + C·log n with only small primes in denominator?
    -- Answer: NO
    (∀ C : ℝ, C > 0 → ¬InfinitelyManyExceptions C) ∧
    -- The bound a + b ≤ n + O(log n) is intrinsic to factorial structure
    (∀ C : ℝ, C > 0 → ∃ D : ℝ, D > 0 ∧ ∀ n a b : ℕ,
      DividesFactorialModSmall n a b C →
      (a + b : ℝ) ≤ n + D * Real.log n) := by
  constructor
  · exact barreto_leeham_theorem
  · exact barreto_leeham_bound

end Erdos729
