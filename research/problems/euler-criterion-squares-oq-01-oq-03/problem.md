# Problem: The Second Supplement — 2 is a Quadratic Residue mod p iff p ≡ ±1 (mod 8)

**Slug**: euler-criterion-squares-oq-01-oq-03
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $p$ be an odd prime. Then $2$ is a quadratic residue modulo $p$ if and only if $p \equiv \pm 1 \pmod 8$:

$$
\exists\, x \in \mathbb{Z}/p\mathbb{Z},\ x^2 = 2
\quad\Longleftrightarrow\quad
p \equiv 1 \pmod 8 \ \lor\ p \equiv 7 \pmod 8.
$$

Equivalently, in terms of Euler's criterion and the Legendre symbol,

$$
\left(\frac{2}{p}\right) \equiv 2^{(p-1)/2} \equiv (-1)^{(p^2-1)/8} \pmod p,
$$

so that $2$ is a residue exactly when $(p^2-1)/8$ is even, i.e. when $p \equiv \pm 1 \pmod 8$.

### Plain Language

The parent entry proves Euler's criterion: a nonzero residue $a$ is a perfect square modulo an odd prime $p$ exactly when $a^{(p-1)/2} \equiv 1 \pmod p$. That criterion is universal but it does not by itself tell you, for a *specific* number $a$, which primes $p$ make $a$ a square. This leaf carries out that computation for the smallest interesting case, $a = 2$: it asks to prove the classical "second supplementary law" of quadratic reciprocity, namely that $2$ is a square mod $p$ precisely when $p$ leaves remainder $1$ or $7$ when divided by $8$ (and is a non-residue when the remainder is $3$ or $5$). For example $2$ is a square mod $7$ ($4^2 = 16 \equiv 2$) and mod $17$, but not mod $5$ or mod $11$.

### Why This Matters

The two supplementary laws — the value of $(-1/p)$ governed by $p \bmod 4$ and the value of $(2/p)$ governed by $p \bmod 8$ — are, alongside the main reciprocity law, the complete toolkit for evaluating Legendre symbols by hand. Pinning the $a=2$ case down as a clean residue-class criterion turns Euler's abstract exponentiation test into a concrete, decidable congruence condition, and gives downstream entries (Gauss sums, reciprocity algorithms, primality of Mersenne-style numbers, and quadratic-form representability) a directly reusable lemma. It also showcases the bridge from the parent's $a^{(p-1)/2}$ formulation to a $p \bmod 8$ statement that needs no exponentiation at all.

## Known Results

### What's Already Proven

- Parent `euler-criterion-squares-oq-01` (verified): Euler's criterion $a^{(p-1)/2} \equiv \pm 1$ characterizing quadratic residues.
- Sibling `euler-criterion-squares-oq-01-oq-01`: exactly $(p-1)/2$ nonzero quadratic residues mod an odd prime.
- Mathlib: `ZMod.exists_sq_eq_two_iff` states exactly this — for `[Fact p.Prime]` and `p ≠ 2`, `IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7`. Supporting API: `ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one/_three`, `legendreSym`, `ZMod.euler_criterion`, `Nat.Prime` facts, and the cyclic structure of `(ZMod p)ˣ`.
- Classical: the second supplement, provable via Gauss's lemma counting sign changes of $\{2, 4, \dots, p-1\}$ reduced into $(-p/2, p/2)$, or via the Gauss-sum / $(-1)^{(p^2-1)/8}$ identity.

### What's Still Open

- A self-contained gallery Lean theorem packaging `IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7` for odd primes, together with the equivalent non-residue characterization (`p % 8 = 3 ∨ p % 8 = 5`).
- The explicit bridge from the parent's Euler-criterion form $2^{(p-1)/2} \equiv (-1)^{(p^2-1)/8}$ to the $p \bmod 8$ statement, recorded as a reusable lemma.

### Our Goal

State and prove, for an odd prime $p$ (`[Fact (Nat.Prime p)]`, `hp : p ≠ 2`), the equivalence `IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7`, and derive the complementary non-residue characterization. Use `ZMod.exists_sq_eq_two_iff` as the engine, then add the worked numerical corollaries (e.g. $2$ is a residue mod $7, 17, 23$ and a non-residue mod $5, 11, 13$) as `decide`/`native_decide` sanity checks.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| euler-criterion-squares-oq-01 | Direct parent; Euler's criterion $a^{(p-1)/2}\equiv\pm1$ | quadratic residues, finite fields |
| euler-criterion-squares-oq-01-oq-01 | Sibling; counts $(p-1)/2$ residues | fiber counting, cyclic groups |
| elementary-quadratic-reciprocity | Main law that the supplements accompany | Legendre symbol, reciprocity |
| jacobi-symbol-oq-01 | Generalizes Legendre symbol multiplicatively | Jacobi symbol, congruences |

## Initial Thoughts

### Potential Approaches

1. **Direct application of `ZMod.exists_sq_eq_two_iff`.** The result is essentially in Mathlib; the gallery contribution is to restate it cleanly for odd primes, derive the non-residue complement (`¬ IsSquare (2 : ZMod p) ↔ p % 8 = 3 ∨ p % 8 = 5`), and connect it back to the parent's Euler-criterion form.
   - Why it might work: Mathlib provides the headline equivalence directly; the remaining work is the complement (a case split on `p % 8 ∈ {1,3,5,7}` since `p` is odd) and packaging.
   - Risk: handling the odd-prime case split on `p % 8` cleanly and discharging the impossible even residues; choosing whether to present via `IsSquare` or `legendreSym p 2 = 1`.

2. **Euler-criterion bridge $2^{(p-1)/2} \equiv (-1)^{(p^2-1)/8}$.** Prove the exponent identity linking the parent's criterion to the $p \bmod 8$ sign, then conclude residue-ness from the sign being $+1$.
   - Why it might work: makes the entry genuinely "child of Euler's criterion" rather than a re-export, exposing the $(p^2-1)/8$ exponent as a reusable lemma; `legendreSym.eq_pow` and `ZMod.euler_criterion` supply the criterion side.
   - Risk: the parity bookkeeping for $(p^2-1)/8$ across the four classes $p \equiv 1,3,5,7 \pmod 8$ is fiddly; cleaner to feed it from `exists_sq_eq_two_iff` rather than re-derive Gauss's lemma.
