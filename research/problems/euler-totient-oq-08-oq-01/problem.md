# Problem: Composite-Modulus Generalized Euler–Fermat

**Slug**: euler-totient-oq-08-oq-01
**Created**: 2026-07-05T02:11:06-07:00
**Status**: Active
**Source**: gallery-gap <!-- extension of verified base proof `euler-totient` -->

## Problem Statement

### Formal Statement

For every integer $a$, every modulus $n \ge 1$, and every exponent
$k \ge \max_{p \mid n} v_p(n)$ (the largest prime-power exponent in the
factorization of $n$),

$$
a^{\,k + \varphi(n)} \equiv a^{\,k} \pmod{n}.
$$

Equivalently, the multiplicative endomorphism $x \mapsto x^{\varphi(n)}$ acts as
the identity on the "eventually periodic" part of the monoid $(\mathbb{Z}/n\mathbb{Z}, \times)$
once the exponent exceeds each prime-power valuation.

### Plain Language

Euler's theorem says $a^{\varphi(n)} \equiv 1 \pmod n$ **only when** $\gcd(a,n)=1$.
This problem removes the coprimality hypothesis: with no restriction on $a$, one
still gets a periodicity statement — raising to the power $\varphi(n)$ leaves
$a^k$ unchanged mod $n$, provided $k$ is large enough to absorb the prime-power
factors that $a$ shares with $n$. The threshold $k \ge \max_p v_p(n)$ is exactly
what is needed so the shared-prime part of $a^k$ is already "saturated" (congruent
to $0$ on each such prime-power factor).

### Why This Matters

This is the clean, fully general form of the Fermat–Euler periodicity used in
practice for computing $a^m \bmod n$ for arbitrary $a$ (e.g. the tetration /
tower-exponent reductions, RSA-style modular exponentiation without the usual
coprimality assumption, and the "lifting the exponent" folklore). It packages
the base entry's prime-power result into the general composite-modulus statement
via the Chinese Remainder Theorem.

## Known Results

### What's Already Proven

- **Euler's theorem** (coprime case): $a^{\varphi(n)} \equiv 1 \pmod n$ for
  $\gcd(a,n)=1$ — base gallery proof `euler-totient` (verified, mathlib badge,
  0 axioms); Mathlib `ZMod.pow_totient` / `Nat.ModEq.pow_totient`.
- **Prime-power case** (the parent `euler-totient-oq-08`): $a^{k+\varphi(p^e)} \equiv a^k \pmod{p^e}$ for $k \ge e$ — the single-prime-power building block this
  entry assembles over.
- Chinese Remainder Theorem — Mathlib `ZMod.chineseRemainder`, `Nat.chineseRemainder`,
  `Nat.Coprime` machinery.
- $\varphi$ is multiplicative and $\varphi(p^e) \mid \varphi(n)$ for $p^e \mid n$
  — Mathlib `Nat.totient_mul`, `Nat.totient_prime_pow`, `Nat.totient_dvd_of_dvd`.

### What's Still Open

- The general composite-modulus assembly `a^(k+φ(n)) ≡ a^k (mod n)` for all `a`,
  with the sharp threshold `k ≥ max_p v_p(n)`, as a single reusable Lean lemma.
- (Optional strengthening) Replace $\varphi(n)$ by the Carmichael function
  $\lambda(n)$ for the *sharp* period — out of scope here; keep $\varphi(n)$.

### Our Goal

Prove the single statement
`a^(k + φ(n)) ≡ a^k (mod n)` for `k ≥ maxPrimePow n` (or the slightly weaker but
cleaner `k ≥ Ω-style bound n` such as `n.factorization.sup id`), for all
`a : ℕ` (or `ℤ`). Reduce to prime powers by CRT; on each `p^e ∥ n` split into
the coprime case (Euler on the unit) and the `p ∣ a` case (both sides ≡ 0 since
`k ≥ e`).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| euler-totient | Base proof: Euler's generalization of Fermat's little theorem (coprime case) | `ZMod.pow_totient`, group of units |
| sum-of-divisors-oq-06-oq-01 | Sibling: prime-power factorization + multiplicativity packaging | `Nat.factorization`, multiplicative closed forms |

## Initial Thoughts

### Potential Approaches

1. **CRT over prime powers (recommended)**: Factor `n = ∏ p^e`. On each `p^e`
   prove `a^(k+φ(n)) ≡ a^k (mod p^e)` and glue with `ZMod.chineseRemainder`
   / `Nat.modEq_and_modEq_iff_modEq_mul` over coprime prime powers.
   - Why it might work: each local factor is elementary; Mathlib has the CRT glue.
   - Risk: bookkeeping over `n.factorization`; establishing `φ(p^e) ∣ φ(n)`.

2. **Per-prime-power case split**: On `p^e`, either `p ∤ a` (then `a` is a unit
   mod `p^e`, `a^{φ(p^e)} ≡ 1`, and `φ(p^e) ∣ φ(n)` gives `a^{φ(n)} ≡ 1`, so
   multiply by `a^k`); or `p ∣ a` (then `a^k ≡ 0` and `a^{k+φ(n)} ≡ 0` since
   `k ≥ e`, both `≡ 0 (mod p^e)`).
   - Why it might work: exhausts all `a`; only uses `k ≥ e` in the divisible case.
   - Risk: the `p ∣ a` vanishing needs `k ≥ v_p(n) = e`, i.e. the threshold hypothesis.

### Key Difficulties

- Formalizing the threshold `k ≥ max_p v_p(n)` cleanly (`n.factorization.sup id`
  is a convenient Lean surrogate).
- The divisibility `φ(p^e) ∣ φ(n)` for each `p^e ∥ n`.
- Working over `ℕ` vs `ZMod n` vs `ℤ` — pick one carrier and stay in it.

### What Would a Proof Need?

- Key lemma 1: prime-power case `p ∤ a → a^(φ(n)) ≡ 1 (mod p^e)` via `φ(p^e) ∣ φ(n)`.
- Key lemma 2: prime-power case `p ∣ a → k ≥ e → a^(k+t) ≡ a^k ≡ 0 (mod p^e)`.
- Technical requirement: CRT recombination over the coprime prime-power factors of `n`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Every ingredient (Euler on units, `φ` multiplicativity/divisibility, CRT) is
  already in Mathlib; the work is assembly and case-splitting, not new theory.
- The base entry `euler-totient` is verified/mathlib/0-axiom, so the coprime
  core is a solved dependency.
- Comparable to `sum-of-divisors-oq-06-oq-01` (prime-power factorization packaging).

**Estimated Effort**:
- Exploration: a few hours (locate CRT + totient-divisibility lemmas)
- If tractable: 1–3 days
- If hard: bounded — worst case the threshold bookkeeping is fiddly but not deep

## References

### Papers
- Standard number-theory texts (Hardy & Wright, *An Introduction to the Theory
  of Numbers*, §5–6) — Euler–Fermat and its non-coprime periodicity form.

### Online Resources
- The "generalized Euler theorem" / "Euler's theorem for non-coprime bases"
  folklore used in tower-exponent (tetration mod n) computations.

### Mathlib
- `ZMod.pow_totient`, `Nat.ModEq.pow_totient` — coprime Euler.
- `Nat.totient_mul`, `Nat.totient_prime_pow`, `Nat.totient_dvd_of_dvd` — φ structure.
- `ZMod.chineseRemainder`, `Nat.chineseRemainder`, `Nat.modEq_and_modEq_iff_modEq_mul`
  — CRT recombination.
- `Nat.factorization`, `Nat.ord_proj` / `Nat.ord_compl` — prime-power valuations.

## Metadata

```yaml
tags:
  - number-theory
  - modular-arithmetic
  - euler-totient
related_proofs:
  - euler-totient
  - sum-of-divisors-oq-06-oq-01
difficulty: medium
source: gallery-gap
created: 2026-07-05T02:11:06-07:00
```

**Significance**: 5/10
**Tractability**: 7/10
