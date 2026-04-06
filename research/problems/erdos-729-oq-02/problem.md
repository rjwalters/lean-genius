# Problem: Legendre's Formula for 2-adic Valuation of Factorials

**Slug**: erdos-729-oq-02
**Created**: 2026-04-05T23:54:18-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
v_2(n!) = n - s_2(n)
$$

where $v_2(n!)$ is the 2-adic valuation of $n!$ (the largest power of 2 dividing $n!$), and $s_2(n)$ is the sum of binary digits of $n$ (the Hamming weight / digit sum in base 2).

More generally, Legendre's formula states: for any prime $p$,
$$
v_p(n!) = \frac{n - s_p(n)}{p - 1}
$$
where $s_p(n)$ is the digit sum of $n$ in base $p$.

### Plain Language

How many times does 2 divide into $n!$? The answer is $n - s_2(n)$, where $s_2(n)$ is the number of 1-bits in the binary representation of $n$. For example, $v_2(8!) = 8 - 1 = 7$ (since $8 = 1000_2$ has one 1-bit, and indeed $8! = 40320 = 2^7 \cdot 315$).

The goal is to formalize this as a Lean 4 theorem using Mathlib's `padicValNat` and `Nat.digits` infrastructure.

### Why This Matters

- **Direct relevance**: The source proof `erdos-729` (Erdős Problem #729 on factorial divisibility) uses `legendre_for_two` as a key lemma but leaves it as a sorry.
- **Foundational**: Legendre's formula underlies many divisibility arguments in combinatorics and number theory, especially for binomial coefficients.
- **Mathlib gap**: If this is not yet in Mathlib, completing it would be a genuine contribution to the library.
- **Kummer's theorem**: Immediately implies Kummer's theorem on the p-adic valuation of binomial coefficients.

## Known Results

### What's Already Proven

- Legendre's formula is classically known (1830) and mathematically elementary.
- Mathlib has `Nat.factorization_factorial` which gives the full factorization of n!.
- `padicValNat p n` in Mathlib computes v_p(n).
- `Nat.digits p n` gives the base-p representation, and `(Nat.digits p n).sum` is s_p(n).

### What's Still Open

- Whether `Nat.factorization_factorial` can be directly connected to `padicValNat` with a clean Lean proof.
- Whether `Nat.digits` digit sum connects cleanly to p-adic valuations in the existing Mathlib API.

### Our Goal

Prove in Lean 4:
```lean
theorem legendre_for_two (n : ℕ) : padicValNat 2 n ! = n - (Nat.digits 2 n).sum
```
or the equivalent statement using `Nat.factorization`. This unblocks `erdos-729`'s sorry on `legendre_for_two`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-729 | Source proof — uses this as an axiom | p-adic valuations, factorial bounds |
| fundamental-arithmetic-oq-03 | Related number theory infrastructure | Factorization in Lean |

## Initial Thoughts

### Potential Approaches

1. **Via `Nat.factorization_factorial`**: Mathlib provides `Nat.factorization_factorial` which gives the exact multiplicity of each prime in n!. Extract the 2-component and connect to digit sum.
   - Why it might work: Direct API connection.
   - Risk: May need intermediate lemmas connecting factorization to digit sum.

2. **Induction on binary representation**: Prove by induction using the recurrence $v_2((2k)!) = v_2(k!) + k$ and $v_2((2k+1)!) = v_2((2k)!)$.
   - Why it might work: Elementary approach, avoids complex API.
   - Risk: More proof effort.

3. **Via existing Mathlib theorem**: Check if `Nat.Prime.factorization_factorial` or similar directly gives this. Mathlib 4 may already have this.
   - Search: `Nat.factorization_factorial`, `padicValNat.factorial`, `Finset.sum_range_choose`
   - Risk: May require version-specific search.

### Key Difficulties

- Connecting `Nat.factorization` (as a `Finsupp`) with `padicValNat` (scalar).
- The digit sum identity requires relating binary representation to the valuation recurrence.

### What Would a Proof Need?

- Key lemma 1: `padicValNat 2 (n !) = (Finsupp.support (Nat.factorization n !)).sum ...` or similar.
- Key lemma 2: Binary digit sum identity: `(Nat.digits 2 n).sum = n - padicValNat 2 (n !)`.
- Technical: Mathlib's `Nat.factorization_factorial` gives `∑ i in Finset.range ∞, n / p^i`.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- Legendre's formula is elementary mathematics with no hard combinatorics.
- Mathlib has all the necessary building blocks: `padicValNat`, `Nat.factorization_factorial`, `Nat.digits`.
- The proof likely already exists in Mathlib under a different name — worth searching first.
- If not, an inductive proof should take hours to days.

**Estimated Effort**:
- Exploration: 1-2 hours (search Mathlib)
- If found in Mathlib: hours (just connect the API)
- If not found: 1-2 days (inductive proof)

## References

### Papers
- Legendre, A.-M. (1830), *Théorie des nombres* — original formula

### Mathlib
- `Mathlib.RingTheory.Multiplicity` — multiplicity / valuation tools
- `Mathlib.NumberTheory.Padics.PadicVal` — `padicValNat`
- `Mathlib.Data.Nat.Digits` — `Nat.digits`, digit sums
- `Mathlib.Data.Nat.Factorization.Basic` — `Nat.factorization_factorial`

## Metadata

```yaml
tags:
  - number-theory
  - p-adic
  - factorials
  - valuation
  - legendre-formula
related_proofs:
  - erdos-729
  - fundamental-arithmetic-oq-03
difficulty: low
source: proof-suggestion
created: 2026-04-05T23:54:18-07:00
```
