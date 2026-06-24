import Proofs.EulerTotientOQ01OQ01
import Mathlib

/-
# Carmichael's Function as the lcm of its Prime-Power Values

## Open Question (euler-totient-oq-01-oq-01-oq-01)

The parent entry (`EulerTotientOQ01OQ01.lean`) proves the **keystone** of the
structure theory of Carmichael's function: multiplicativity over coprime factors,
  λ(m·n) = lcm(λ(m), λ(n))   whenever gcd(m, n) = 1
(`CarmichaelMultiplicative.carmichael_mul_coprime`), and explicitly leaves the
prime-power factorization formula
  λ(n) = lcm_i λ(pᵢ^{kᵢ})
"as a routine induction".  This file discharges that deferred corollary:

  λ(n) = lcm_{p ∈ primeFactors n} λ(p^{vₚ(n)})        (`carmichael_eq_factorization_lcm`)

where `vₚ(n) = n.factorization p` is the p-adic valuation, expressed as the
finite `Finset.lcm` over the prime factors of `n`.

## Proof

Carmichael's function is `λ(n) = Monoid.exponent (ZMod n)ˣ` (the parent's
definition, reused here).  We induct on `n` with `Nat.recOnPosPrimePosCoprime`,
which reduces every positive `n` to its prime-power building blocks:

* **n = 1.**  `(ZMod 1)ˣ` is trivial, so its exponent is `1`; the empty
  `Finset.lcm` is also `1`.  (`carmichael_one`)

* **n = p^k, p prime, k ≥ 1.**  The factorization is the single point
  `vₚ(p^k) = k`, so the indexing set is `{p}` and the singleton lcm is exactly
  `λ(p^k)`.

* **n = a·b, a, b > 1 coprime.**  The parent keystone gives
  `λ(a·b) = lcm(λ(a), λ(b))`.  The factorization splits additively over the
  coprime (hence disjoint) prime supports, so the index set splits as a disjoint
  union and `Finset.lcm` distributes over it (`Finset.lcm_union`).  On each part
  the valuation `vₚ(a·b)` agrees with `vₚ(a)` (resp. `vₚ(b)`) because the other
  factor contributes `0` at those primes, so the induction hypotheses apply
  verbatim (`Finset.lcm_congr`).

Since every `(ℤ/p^kℤ)*` is cyclic (`p` odd) or a product of at most two cyclic
groups (`p = 2`), this expresses λ(n) as the lcm of the orders of the cyclic
factors of the unit group — the full structural characterization the parent set
out to reach.

## Honesty note

This is exactly the "routine induction" the parent flagged: no new mathematics,
just the standard multiplicative-to-factorization bootstrap (`carmichael_mul_coprime`
+ `Nat.recOnPosPrimePosCoprime` + `Finset.lcm_union`).  The contribution is the
explicit gallery statement of the prime-power formula, verified with zero axioms.
-/

open ZMod

namespace CarmichaelFactorization

open CarmichaelMultiplicative

/-- The Carmichael function of `1` is `1`: `(ZMod 1)ˣ` is the trivial group, whose
exponent is `1`. -/
theorem carmichael_one : carmichael 1 = 1 := by
  unfold carmichael
  have h : ∀ g : (ZMod 1)ˣ, g ^ 1 = 1 := by
    intro g; simp [Subsingleton.elim g 1]
  exact Nat.dvd_one.mp (Monoid.exponent_dvd_of_forall_pow_eq_one h)

/-- **Carmichael's function is the lcm of its prime-power values.**

For every positive `n`,
  `λ(n) = lcm_{p ∈ primeFactors n} λ(p^{vₚ(n)})`,
the finite lcm taken over the prime factors of `n` (`vₚ(n) = n.factorization p`).

This is the prime-power factorization formula deferred by the parent entry; it
follows from coprime multiplicativity of `λ` by induction on the factorization. -/
theorem carmichael_eq_factorization_lcm {n : ℕ} (hn : n ≠ 0) :
    carmichael n
      = n.factorization.support.lcm (fun p => carmichael (p ^ n.factorization p)) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => exact absurd rfl hn
  | one =>
      simp [Nat.factorization_one, carmichael_one]
  | prime_pow p k hp hk =>
      simp only [hp.factorization_pow, Finsupp.support_single_ne_zero p hk.ne',
        Finset.lcm_singleton, Finsupp.single_eq_same]
      simp
  | coprime a b ha hb hab iha ihb =>
      have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
      have hb0 : b ≠ 0 := (zero_lt_one.trans hb).ne'
      have hdisj : Disjoint a.factorization.support b.factorization.support := by
        simpa only [Nat.support_factorization] using hab.disjoint_primeFactors
      have hsupp : (a * b).factorization.support
          = a.factorization.support ∪ b.factorization.support := by
        rw [Nat.factorization_mul ha0 hb0, Finsupp.support_add_eq hdisj]
      have ea : a.factorization.support.lcm
            (fun p => carmichael (p ^ (a * b).factorization p))
          = a.factorization.support.lcm (fun p => carmichael (p ^ a.factorization p)) := by
        refine Finset.lcm_congr rfl (fun p hp => ?_)
        have hp0 : b.factorization p = 0 :=
          Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp hdisj hp)
        rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, hp0, add_zero]
      have eb : b.factorization.support.lcm
            (fun p => carmichael (p ^ (a * b).factorization p))
          = b.factorization.support.lcm (fun p => carmichael (p ^ b.factorization p)) := by
        refine Finset.lcm_congr rfl (fun p hp => ?_)
        have hp0 : a.factorization p = 0 :=
          Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp hdisj hp)
        rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply, hp0, zero_add]
      rw [carmichael_mul_coprime hab, iha ha0, ihb hb0, hsupp, Finset.lcm_union, ea, eb,
        lcm_eq_nat_lcm]

end CarmichaelFactorization
