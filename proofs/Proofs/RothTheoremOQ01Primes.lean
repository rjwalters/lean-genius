import Proofs.RothTheoremOQ01Reciprocal
import Mathlib.NumberTheory.SumPrimeReciprocals

/-
# Three-term arithmetic progressions in the primes (roth-theorem-oq-01)

The reciprocal-sum consequence of the Bloom–Sisask density bound
(`RothTheoremOQ01Reciprocal.threeAPFree_summable_reciprocal`) says that every 3-AP-free
set `A ⊆ ℕ` (with `0 ∉ A`) has a *convergent* reciprocal sum.  Contrapositively, a set
whose reciprocal sum *diverges* must contain a nontrivial three-term arithmetic
progression (`exists_nontrivial_threeAP_of_not_summable_reciprocal`).

The primes are the canonical divergent-reciprocal set: `∑_{p prime} 1/p = ∞`
(Euler; Mathlib `not_summable_one_div_on_primes`).  Feeding that single fact into the
contrapositive form of the reciprocal bound yields, with no further analytic work, the
**`k = 3` case of the Green–Tao theorem**:

> the primes contain a nontrivial three-term arithmetic progression `p, p + d, p + 2d`.

This is a genuine, clean, and quantitatively-honest consequence: the *qualitative* Roth
bound `r₃(N) = o(N)` is **not** enough — the primes have density `0`, so Roth alone says
nothing about them.  What closes the argument is precisely the extra power-of-`log` saving
of Bloom–Sisask, packaged here through the reciprocal-sum route.  No new axiom is
introduced: the result inherits exactly the single imported Bloom–Sisask assumption
`RothTheoremOQ02.rothNumberNat_bloom_sisask` (via the reciprocal file) plus Mathlib's
unconditional divergence of the prime reciprocals.
-/

open RothTheoremOQ01Reciprocal

namespace RothTheoremOQ01Primes

/-- The reciprocal sum over the primes, viewed as the subtype `↥{p | p.Prime}`, diverges.
This is Mathlib's `not_summable_one_div_on_primes` transported from its `Set.indicator`
form to the subtype form consumed by `exists_nontrivial_threeAP_of_not_summable_reciprocal`. -/
theorem not_summable_reciprocal_primes :
    ¬ Summable (fun a : ({p : ℕ | p.Prime} : Set ℕ) => (1 : ℝ) / (a : ℝ)) :=
  fun h => not_summable_one_div_on_primes (summable_subtype_iff_indicator.mp h)

/-- `0` is not in the set of primes, the side condition `0 ∉ A` of the reciprocal bound. -/
theorem zero_not_mem_setOf_prime : (0 : ℕ) ∉ ({p : ℕ | p.Prime} : Set ℕ) :=
  fun h => Nat.not_prime_zero h

/-- **The primes are not 3-AP-free.**  If they were, their reciprocal sum would converge
(`threeAPFree_summable_reciprocal`), contradicting Euler's divergence
`not_summable_one_div_on_primes`.  Equivalent to `primes_contain_nontrivial_threeAP`. -/
theorem not_threeAPFree_setOf_prime :
    ¬ ThreeAPFree ({p : ℕ | p.Prime} : Set ℕ) :=
  not_threeAPFree_of_not_summable_reciprocal zero_not_mem_setOf_prime
    not_summable_reciprocal_primes

/-- **Three-term arithmetic progressions in the primes (`k = 3` Green–Tao).**  There exist
a prime `p` and a step `d > 0` with `p`, `p + d`, `p + 2d` all prime.  Obtained from the
Bloom–Sisask reciprocal-sum bound (a set with divergent reciprocal sum contains a nontrivial
3-AP) applied to the primes, whose reciprocals diverge (Euler).  The qualitative Roth bound
`r₃(N) = o(N)` does not suffice — the primes have density `0`; the power-of-`log` saving of
Bloom–Sisask is what makes the argument go through.  No new axiom beyond the single imported
Bloom–Sisask assumption. -/
theorem primes_contain_nontrivial_threeAP :
    ∃ p d : ℕ, 0 < d ∧ Nat.Prime p ∧ Nat.Prime (p + d) ∧ Nat.Prime (p + 2 * d) :=
  exists_nontrivial_threeAP_of_not_summable_reciprocal
    zero_not_mem_setOf_prime not_summable_reciprocal_primes

#check @primes_contain_nontrivial_threeAP
#check @not_threeAPFree_setOf_prime

-- Axiom audit: rests on exactly the single imported Bloom–Sisask assumption
-- `RothTheoremOQ02.rothNumberNat_bloom_sisask` (via the reciprocal file); no new axiom.
#print axioms primes_contain_nontrivial_threeAP

end RothTheoremOQ01Primes
