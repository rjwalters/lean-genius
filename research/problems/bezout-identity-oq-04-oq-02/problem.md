# Problem: Generalize gcd_complete_characterization to any PID

**Slug**: bezout-identity-oq-04-oq-02
**Created**: 2026-04-21T21:54:20+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

In any principal ideal domain (PID), for elements $a, b \in R$:

$$
\gcd(a, b) \text{ generates } aR + bR
$$

i.e., $\exists\, u, v \in R,\; ua + vb = d$ and $d \mid a$, $d \mid b$, and $d$ is maximal with respect to divisibility.

### Plain Language

The Bézout identity and GCD characterization hold in ℤ via the Euclidean algorithm. Generalize this to any Principal Ideal Domain using Mathlib's `IsBezout` or `IsPrincipalIdealRing` typeclasses — covering ℤ[i], k[x], ℤ[ω], etc.

### Why This Matters

- Unifies GCD theory across number theory, polynomial algebra, and algebraic number theory
- Key for unique factorization in algebraic number theory
- Foundational for the classification of finitely generated modules over PIDs

## Known Results

### What's Already Proven

- `bezout-identity`: Extended Euclidean algorithm for ℤ — gallery
- `bezout-identity-oq-04`: GCD characterization for ℤ — gallery
- `IsBezout`: typeclass with `span_pair_eq_span_gcd` — Mathlib
- `EuclideanDomain.gcd_eq_gcd_ab`: Bézout identity in Euclidean domains — Mathlib

### What's Still Open

- Complete Lean proof that the GCD characterization (divisibility + Bézout) holds over `IsBezout`
- Concrete instances: ℤ[i], k[x] over a field with explicit GCD

### Our Goal

Prove:
```lean
theorem bezout_gcd_complete {R : Type*} [CommRing R] [IsBezout R]
    (a b : R) : ∃ d u v : R, u * a + v * b = d ∧ d ∣ a ∧ d ∣ b ∧
    ∀ c : R, c ∣ a → c ∣ b → c ∣ d
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| bezout-identity | Direct parent: Bézout for ℤ | Int.gcd, Nat.xgcd |
| bezout-identity-oq-04 | GCD characterization for ℤ | divisibility |
| bezout-identity-oq-01 | GCD in polynomial rings | Polynomial.gcd |
| chinese-remainder-constructive | CRT uses Bézout | Nat.chineseRemainder |

## Initial Thoughts

### Potential Approaches

1. **Via `IsBezout.span_pair_eq_span_gcd`**:
   - Mathlib's `IsBezout` has ideal-level: `Ideal.span {a, b} = Ideal.span {gcd a b}`
   - Translate ideal equality to element-level Bézout + divisibility
   - Why it might work: Direct from the IsBezout definition
   - Risk: Need to extract element witnesses from ideal membership

2. **Via `EuclideanDomain.gcd_eq_gcd_ab`**:
   - In a Euclidean domain: gcd a b = a * gcdA a b + b * gcdB a b
   - Prove GCD characterization from Bézout + divisibility
   - Risk: Some PIDs are not Euclidean

3. **Ideal-theoretic approach**:
   - In a PID: every ideal is principal, so ⟨a, b⟩ = ⟨d⟩ for some d = gcd(a,b)
   - The generator d satisfies the GCD conditions by ideal inclusion

### Key Difficulties

- PIDs vs Bézout domains: Bézout + Noetherian = PID; need the right typeclass
- GCD in an abstract PID is only defined up to units (need `Associated`)
- Extracting element witnesses from ideal membership

### What Would a Proof Need?

- Key lemma 1: `IsBezout.span_pair_eq_span_gcd` → element-level Bézout
- Key lemma 2: Ideal span inclusion ↔ divisibility
- Key lemma 3: Maximality of gcd from ideal being the intersection of principal ideals
- Mathlib: `IsBezout`, `Ideal.span_singleton_le_iff_mem`, `dvd_iff_ideal_le`

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- Mathlib's `IsBezout` provides most of the structure at the ideal level
- Main work: unpacking ideal equality into element-level statements
- Good Mathlib support for PIDs and their GCDs

**Estimated Effort**:
- Exploration: 2-4 hours
- If tractable: 2-4 days

## References

### Papers
- Jacobson, N. "Basic Algebra I" (1985) — PID theory
- Lang, S. "Algebra" (2002) — GCD in PIDs

### Mathlib
- `Mathlib.RingTheory.Bezout` — `IsBezout` typeclass
- `Mathlib.RingTheory.PrincipalIdealDomain` — PID structure
- `Mathlib.Algebra.EuclideanDomain.Basic` — Euclidean domain GCD

## Metadata

```yaml
tags:
  - abstract-algebra
  - ring-theory
  - gcd
  - principal-ideal-domain
  - bezout
related_proofs:
  - bezout-identity
  - bezout-identity-oq-04
  - chinese-remainder-constructive
difficulty: low-medium
source: gallery-gap
created: 2026-04-21T21:54:20+02:00
```

**Significance**: 7/10
**Tractability**: 6/10
