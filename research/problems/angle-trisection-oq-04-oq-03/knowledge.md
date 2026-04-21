# Knowledge: angle-trisection-oq-04-oq-03

## Key Facts

### Pierpont Primes
- A prime p is Pierpont if p - 1 = 2^u · 3^v for some u, v ≥ 0
- Small Pierpont primes: 2, 3, 5, 7, 13, 17, 19, 37, 73, 97, 109, 163, 193, 257, 433, ...
- Note: 2 = 2^1·3^0+1, 3 = 2^1·3^1/3 (hmm: 3-1=2=2^1·3^0 ✓), 5-1=4=2^2 ✓, 7-1=6=2·3 ✓
- All Fermat primes (5, 17, 257, 65537) are also Pierpont primes

### Pierpont Criterion (1895)
- Regular n-gon constructible by compass + angle trisector (neusis) iff
  n = 2^a · 3^b · p₁ · ... · pₘ where pᵢ are distinct Pierpont primes > 3
- Galois theory: constructible iff [Q(ζₙ) : Q] divides some 2^s · 3^t
- [Q(ζₙ) : Q] = φ(n) = Euler totient of n
- So criterion: φ(n) = 2^a · 3^b

### Comparison with Gauss-Wantzel
- Gauss-Wantzel: compass constructible iff φ(n) = 2^k (only powers of 2)
- Pierpont: neusis constructible iff φ(n) = 2^a · 3^b (allows factors of 3)
- Key: angle trisection allows cube roots → field extensions of degree 3

### Constructible n-gons (Pierpont, not Gauss-Wantzel)
- n=7: φ(7)=6=2·3 ✓ (Pierpont prime 7)
- n=9: φ(9)=6=2·3 ✓ (=3²)
- n=13: φ(13)=12=4·3 ✓ (Pierpont prime 13)
- n=14: φ(14)=6=2·3 ✓
- n=18: φ(18)=6=2·3 ✓
- n=19: φ(19)=18=2·3² ✓

## Open Questions
- How is `IsNeusisConstructible` defined in `AngleTrisectionOQ04.lean`?
- Is there existing Mathlib support for φ(n) = 2^a · 3^b characterization?
- Does the parent proof have a `constructible ↔ field degree` lemma?

## References
- Pierpont, J. (1895): "On an unresolved problem of Euclidean geometry"
- Parent proof: `proofs/Proofs/AngleTrisectionOQ04.lean`
- `Mathlib.NumberTheory.ArithmeticFunction` — Euler totient
