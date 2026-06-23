import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

/-!
# Divergence of the Sum of Prime Reciprocals (Wiedijk #81)

## What This Proves
The sum of reciprocals of all prime numbers diverges—its partial sums grow
without bound:
$$\sum_{p \text{ prime}} \frac{1}{p} = \frac{1}{2} + \frac{1}{3} + \frac{1}{5} + \frac{1}{7} + \frac{1}{11} + \cdots = \infty$$

This is a remarkable strengthening of Euclid's theorem on the infinitude of primes.
Not only are there infinitely many primes, but they are "dense enough" for their
reciprocals to form a divergent series—even though the primes grow sparser among
the integers.

## Historical Context
Leonhard Euler proved this result in 1737. He used the connection between the
harmonic series and the product over primes (Euler's product formula) to show
that if there were only finitely many primes, the product would converge, but
we know the harmonic series diverges.

## Approach
- **Foundation (from Mathlib):** We use `Nat.Primes.not_summable_one_div` which
  directly proves the series is not summable, and `not_summable_one_div_on_primes`
  which expresses this as a sub-sum of the harmonic series.
- **Historical Proof (Euler, 1737):** Uses the product representation
  ∏_p 1/(1-1/p) = ∑_n 1/n and takes logarithms.
- **Elementary Proof (Erdős):** The proof in Mathlib follows Erdős's elementary
  argument from "Proofs from THE BOOK."

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Nat.Primes.not_summable_one_div` : The prime reciprocal sum is not summable
- `not_summable_one_div_on_primes` : As a sub-sum of the harmonic series
- `Nat.Primes.summable_rpow` : Convergence criterion for ∑ p^r

## Comparison with Harmonic Series
While both the harmonic series (∑ 1/n) and the prime reciprocal series diverge,
the prime series diverges *much* more slowly. The partial sums satisfy:
- Harmonic series: H_n ~ ln(n)
- Prime reciprocals: ∑_{p≤n} 1/p ~ ln(ln(n))

The "log log" growth is so slow that it takes astronomically large numbers
to see significant growth.
-/

namespace PrimeReciprocalDivergence

/-! ## The Main Theorem: Prime Reciprocal Series Diverges

The sum ∑_{p prime} 1/p is not summable—equivalently, its partial sums
grow without bound. -/

/-- **Prime Reciprocal Divergence (Wiedijk #81)**

The sum of reciprocals of prime numbers diverges. More precisely, the sequence
that takes each prime p to 1/p is not summable.

This is formalized using the `Nat.Primes` type which represents natural numbers
that are prime. -/
theorem prime_reciprocal_not_summable : ¬Summable (fun p : Nat.Primes => 1 / (p : ℝ)) := by
  exact Nat.Primes.not_summable_one_div

/-- Alternative formulation: the reciprocals of primes are not summable.
Uses the inverse notation instead of division. -/
theorem prime_reciprocal_not_summable' : ¬Summable (fun p : Nat.Primes => ((p : ℝ)⁻¹)) := by
  simp only [← one_div]
  exact prime_reciprocal_not_summable

/-! ## As a Sub-sum of the Harmonic Series

The prime reciprocals can be viewed as a subsequence of the harmonic series.
We extract just the terms corresponding to primes. -/

/-- The prime reciprocals, when viewed as a subset of the harmonic series
(using indicator functions), form a non-summable series.

This uses the set indicator: for each n, we get 1/n if n is prime, else 0. -/
theorem indicator_primes_not_summable :
    ¬Summable (fun n : ℕ => Set.indicator {p | Nat.Prime p} (fun n => 1 / (n : ℝ)) n) := by
  exact not_summable_one_div_on_primes

/-! ## Generalization: The p-Series over Primes

We can ask: for which exponents r does ∑_p p^r converge?
The answer is r < -1. Note that r = -1 corresponds to our main theorem. -/

/-- The series ∑_p p^r over primes converges if and only if r < -1.

For r = -1 (our case), the series diverges.
For r < -1, the series converges.
For r > -1, the series diverges even faster. -/
theorem prime_power_summable_iff (r : ℝ) :
    Summable (fun p : Nat.Primes => ((p : ℝ) ^ r)) ↔ r < -1 := by
  exact Nat.Primes.summable_rpow

/-- Special case: The prime reciprocal series (r = -1) diverges. -/
theorem prime_reciprocal_diverges_as_rpow :
    ¬Summable (fun p : Nat.Primes => ((p : ℝ) ^ (-1 : ℝ))) := by
  rw [prime_power_summable_iff]
  norm_num

/-! ## Why This Matters

The divergence of the prime reciprocals tells us something profound about the
distribution of primes. Consider:

1. The series ∑ 1/n² converges (Basel problem = π²/6)
2. The series ∑ 1/n diverges (harmonic series)
3. The series ∑_{p prime} 1/p diverges

Even though primes become increasingly rare (by the Prime Number Theorem,
π(n) ~ n/ln(n)), they remain "dense enough" for their reciprocals to diverge.

This has important consequences in analytic number theory, including:
- Mertens' theorems on prime sums
- The connection to the Riemann zeta function
- Applications to probabilistic number theory -/

/-! ## Contrast with Convergent Cases

While ∑ 1/p diverges, ∑ 1/p² converges. In fact, for any r > 1,
the sum ∑_p 1/p^r converges (prime zeta function). -/

/-- The sum of squared reciprocals of primes converges. -/
theorem prime_squared_reciprocal_summable :
    Summable (fun p : Nat.Primes => 1 / ((p : ℝ) ^ 2)) := by
  have h : Summable (fun p : Nat.Primes => ((p : ℝ) ^ (-2 : ℝ))) := by
    rw [prime_power_summable_iff]
    norm_num
  convert h using 1
  ext p
  have hp_pos : (0 : ℝ) < p := by
    have hp := p.prop
    have : (p : ℕ) ≥ 2 := hp.two_le
    positivity
  rw [one_div, Real.rpow_neg hp_pos.le, Real.rpow_two]

/-! ## The Proof Strategy (Erdős)

The Mathlib proof follows Erdős's elementary argument:

1. Assume for contradiction that ∑ 1/p converges to some S.
2. Define "smooth numbers" (those with all prime factors ≤ k).
3. Show the count of smooth numbers up to n can be estimated.
4. Show that if ∑ 1/p converges, there are "too few" smooth numbers.
5. But we can also show there are "enough" smooth numbers.
6. Contradiction!

This beautiful proof appears in "Proofs from THE BOOK." -/

#check prime_reciprocal_not_summable
#check indicator_primes_not_summable
#check prime_power_summable_iff

end PrimeReciprocalDivergence
