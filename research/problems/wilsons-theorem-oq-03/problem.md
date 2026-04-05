# Problem: Legendre's Formula and Wilson's Theorem: p-adic Valuation of (p-1)!+1

**Slug**: wilsons-theorem-oq-03
**Created**: 2026-04-05T10:02:39-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\nu_p(n!) = \sum_{i=1}^{\infty} \left\lfloor \frac{n}{p^i} \right\rfloor
$$

Legendre's formula gives the exact p-adic valuation of n!. Combined with Wilson's theorem ($p$ prime iff $(p-1)! \equiv -1 \pmod{p}$), this determines $\nu_p((p-1)! + 1)$ for all primes $p$.

**Goal**: Formalize Legendre's formula in Lean 4 using Mathlib, and prove the connection to Wilson's theorem — specifically that $\nu_p((p-1)! + 1) = 0$ for all primes $p \geq 3$.

### Plain Language

Legendre's formula counts exactly how many times the prime $p$ divides $n!$: it's the sum of $\lfloor n/p \rfloor + \lfloor n/p^2 \rfloor + \lfloor n/p^3 \rfloor + \cdots$ (finitely many nonzero terms). Wilson's theorem says $(p-1)! \equiv -1 \pmod{p}$ for primes $p$, so $(p-1)! + 1 \equiv 0 \pmod{p}$ but the formula tells us *exactly* how many times $p$ divides $(p-1)!$, letting us determine the precise p-adic valuation of $(p-1)! + 1$.

### Why This Matters

- Legendre's formula is fundamental in number theory — it appears in Kummer's theorem for valuations of binomial coefficients, and in p-adic analysis
- The Wilson-Legendre connection gives a concrete example of combining two classical theorems into a precise numerical result
- Mathlib has both ingredients; formalizing their combination fills a natural gallery gap

## Known Results

### What's Already Proven

- Wilson's theorem is in Mathlib: `ZMod.wilsons_lemma` and `Nat.Prime.factorial_mulInv_atTop`
- `Nat.factorization_factorial` in Mathlib computes the factorization of $n!$
- p-adic valuation tools: `padicValNat`, `multiplicity`, `Nat.factorization`

### What's Still Open

- Whether Mathlib has a clean `legendres_formula` lemma stating $\nu_p(n!) = \sum_i \lfloor n/p^i \rfloor$ in a directly usable form
- The combined theorem: $\nu_p((p-1)! + 1) = 0$ for all primes $p \geq 3$

### Our Goal

1. Prove `legendres_formula`: $\nu_p(n!) = \sum_{i \geq 1} \lfloor n/p^i \rfloor$ using Mathlib's `Nat.factorization_factorial`
2. Prove `wilson_valuation`: for prime $p \geq 3$, `padicValNat p (Nat.factorial (p-1) + 1) = 0`
3. Build the bridge connecting these via the ultrametric inequality $\nu_p(a+b) \geq \min(\nu_p(a), \nu_p(b))$

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `wilsons-theorem` | Parent theorem; Wilson fully formalized | ZMod, prime characterization |
| `fundamental-arithmetic` | Prime factorization infrastructure | Nat.factorization |

## Initial Thoughts

### Potential Approaches

1. **Approach A: Mathlib API bridge**
   - `Nat.factorization_factorial` gives factorization of $n!$; extract the p-component
   - Bridge to `padicValNat` via `Nat.factorization_eq`
   - Risk: API mismatch between `Nat.factorization` (Finsupp) and `padicValNat` (ℕ-valued)

2. **Approach B: Direct inductive proof**
   - Prove $\nu_p(n!) = \nu_p((n-1)!) + \nu_p(n)$ by induction
   - Use $\nu_p(n) = $ multiplicity of $p$ in $n$ directly
   - Risk: more work, but self-contained

3. **Approach C: Digit-sum identity**
   - Use the equivalent formula $\nu_p(n!) = (n - s_p(n))/(p-1)$ where $s_p(n)$ is base-$p$ digit sum
   - May be in Mathlib via `Nat.factorization_factorial` indirectly
   - Risk: base-$p$ representation tools in Lean can be verbose

### Key Difficulties

- Infinite sum is actually finite: need `Finset.sum` with appropriate support
- `padicValNat p (factorial (p-1) + 1)` requires knowing $p \nmid (p-1)!$ (from Legendre) and $p \mid (p-1)! + 1$ (from Wilson)
- The ultrametric bound: $\nu_p(a + b) = \min(\nu_p(a), \nu_p(b))$ when the valuations differ

### What Would a Proof Need?

- Legendre's formula in usable form (possibly already in Mathlib)
- Wilson's theorem: `(p-1)! ≡ -1 [MOD p]`
- Arithmetic: if $\nu_p(a) = k$ and $\nu_p(b) > k$ then $\nu_p(a + b) = k$

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- Legendre's formula is essentially in Mathlib via `Nat.factorization_factorial`; the main challenge is matching the API
- Wilson's theorem is already gallery-complete
- The combined result follows from two known theorems — primarily an API engineering challenge
- Similar to the Bertrand's postulate line of proofs in tractability

**Estimated Effort**:
- Exploration: 1-2 hours (Mathlib search)
- If tractable (likely): 1-2 days for a clean proof
- Main risk: p-adic API complexity in Lean

## References

### Papers
- Legendre, A. M. (1808), *Essai sur la théorie des nombres* — original formula
- Kummer (1852) — binomial coefficient valuation via Legendre

### Mathlib
- `Mathlib.NumberTheory.Factorial` — factorial factorization
- `Mathlib.Data.Nat.Factorization.Basic` — `Nat.factorization_factorial`
- `Mathlib.FieldTheory.Finite.Basic` — `ZMod.wilsons_lemma`
- `Mathlib.NumberTheory.Padics.PadicVal` — `padicValNat`

## Metadata

```yaml
tags:
  - number-theory
  - p-adic
  - factorial
  - legendre-formula
  - wilsons-theorem
related_proofs:
  - wilsons-theorem
  - fundamental-arithmetic
difficulty: low-medium
source: gallery-gap
created: 2026-04-05T10:02:39-07:00
```
