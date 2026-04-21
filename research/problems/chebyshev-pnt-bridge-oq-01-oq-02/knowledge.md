# Knowledge: chebyshev-pnt-bridge-oq-01-oq-02

## Key Facts

### Mathlib Lemmas (to verify)
- `Nat.factorization_prod_pow_eq_self`: n = ∏ p^(v_p(n)) for p prime
- `Nat.factorization_choose`: factorization of binomial coefficients
- `Nat.centralBinom`: definition in Mathlib

### Mathematical Background
- Kummer's theorem: v_p(C(m+n, n)) = number of carries adding m and n in base p
- Central binomial C(2n,n) ≤ 4^n (standard bound)
- π(n) = number of primes ≤ n; bound: C(2n,n)^(1/π(2n)) ≤ 2n

## Open Questions
- Is `Nat.factorization_prod_pow_eq_self` the right approach, or is there a direct `Nat.centralBinom_factorization` lemma?

## References
- Chebyshev (1852): Original prime counting bounds
- Kummer (1852): Theorem on carries and p-adic valuations of binomials
