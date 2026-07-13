# Problem: Residue and Coprimality Structure of Sylvester's Sequence

**Slug**: sylvester-sequence-oq-01-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $a_0 = 2$ and $a_{n+1} = a_n^2 - a_n + 1$ be Sylvester's sequence
($2, 3, 7, 43, 1807, \dots$). Establish its elementary arithmetic structure:

1. **Oddness.** $a_n$ is odd for all $n \ge 1$.
2. **Telescoping product / cofactor identity.** $a_{n+1} - 1 = \prod_{k=0}^{n} a_k$, and
   equivalently $a_{n+1} = 1 + a_n(a_n - 1)$.
3. **Pairwise coprimality.** $\gcd(a_i, a_j) = 1$ for all $i \ne j$, obtained from (2) via
   $a_m \equiv 1 \pmod{a_k}$ whenever $k < m$.
4. **Fixed residue.** $a_n \equiv 1 \pmod 6$ for all $n \ge 2$ (indeed $a_n \equiv 1$
   modulo every earlier term $a_k$, $k \le n-1$, and $a_n$ is $\equiv 1 \pmod 6$ because
   $a_2 = 7 \equiv 1$ and the recurrence preserves the residue).

The target is a single axiom-free Lean development packaging (1)–(4) as reusable lemmas.

### Plain Language

Sylvester's sequence is defined by squaring-and-adjusting: each term is one more than the
product of all the previous terms. That single fact forces a rigid arithmetic skeleton:
every term past the first is odd, every term leaves remainder $1$ when divided by any
earlier term (so no two terms share a factor), and from $7$ onward every term is $\equiv 1$
modulo $6$. This problem asks for a clean, machine-checked account of that skeleton.

### Why This Matters

The coprimality of Sylvester's terms is exactly what makes $\sum 1/a_k = 1$ a *distinct*
unit-fraction (Egyptian) representation, and the "$\equiv 1$ modulo earlier terms" law is
the engine behind Euclid–Mullin and Znám-problem constructions of pairwise-coprime integer
families. The parent `sylvester-sequence-oq-01` proves the reciprocal-sum identity and
sibling `sylvester-sequence-oq-01-oq-02` the growth rate; this entry supplies the
*residue/divisibility* half, completing the elementary theory with the congruence and
coprimality lemmas that downstream Egyptian-fraction entries can reuse.

## Known Results

### What's Already Proven

- Reciprocal sum $\sum_{k<n} 1/a_k = 1 - 1/(a_n - 1)$ — parent `sylvester-sequence-oq-01`.
- Doubly-exponential growth $a_n \ge 2^{2^{n-1}}$ — sibling `-oq-01-oq-02`.
- The recurrence $a_{n+1} = a_n^2 - a_n + 1$ and monotone invariant $a_n \ge 2$.

### What's Still Open (for this entry)

- The telescoping product identity $a_{n+1} - 1 = \prod_{k\le n} a_k$ as a standalone lemma.
- Pairwise coprimality $\gcd(a_i,a_j)=1$ for $i \ne j$.
- The mod-$6$ residue $a_n \equiv 1 \pmod 6$ for $n \ge 2$ and oddness for $n \ge 1$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sylvester-sequence-oq-01 | parent: reciprocal sum | induction, telescoping |
| sylvester-sequence-oq-01-oq-02 | sibling: growth bound | induction, `pow` monotonicity |
| euclid-infinitude-of-primes (if present) | coprime-family analogue | $N+1$ coprimality argument |

## Initial Thoughts

### Potential Approaches

1. **Product identity first, then everything follows.** Prove
   $a_{n+1} - 1 = \prod_{k\le n} a_k$ by induction from $a_{n+1} - 1 = a_n(a_n-1)$ and the
   IH $a_n - 1 = \prod_{k<n} a_k$. Coprimality: for $k < m$, $a_k \mid a_m - 1$, so any
   common divisor of $a_k, a_m$ divides $1$.
   - Why it might work: one clean induction feeds all three downstream facts.
   - Risk: `Nat` subtraction in $a_{n+1}-1$ needs the $a_n \ge 1$ side condition.

2. **Modular induction for residues.** Work in `ZMod 6`: show the recurrence sends the
   residue $1 \mapsto 1$ (since $1 - 1 + 1 = 1$) and $a_2 \equiv 1$, giving $a_n \equiv 1
   \pmod 6$ for $n \ge 2$ by induction; oddness via `ZMod 2`.
   - Why it might work: `ZMod`/`decide` handles the residue arithmetic mechanically.
   - Risk: aligning the `Nat`-valued sequence with its `ZMod` image cleanly.

### Key Difficulties

- `Nat` truncated subtraction in the product identity (carry $a_n \ge 1$ throughout).
- Turning "$a_k \mid a_m - 1$" into `Nat.Coprime a_k a_m` via `Nat.coprime_of_...`.

### What Would a Proof Need?

- Lemma: `a (n+1) = 1 + a n * (a n - 1)` and `a (n+1) - 1 = ∏ k in range (n+1), a k`.
- Lemma: `k < m → a k ∣ a m - 1` (from the product identity), hence `Nat.Coprime (a k) (a m)`.
- Lemma: `(a n : ZMod 6) = 1` for `n ≥ 2`, and `Odd (a n)` for `n ≥ 1`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- Elementary induction and modular arithmetic; no analysis.
- Coprimality of Sylvester-type sequences is a textbook argument, well-suited to `Nat`/`ZMod`.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.Data.Nat.GCD.Basic` — `Nat.Coprime`, `Nat.coprime_of_dvd`.
- `Mathlib.Data.ZMod.Basic` — residue arithmetic.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.prod`, telescoping.

### Online Resources
- OEIS A000058 (Sylvester's sequence) — product formula and coprimality notes.
- Graham–Knuth–Patashnik, *Concrete Mathematics* (Euclid-numbers / coprime families).

## Metadata

```yaml
tags:
  - number-theory
  - recurrence-sequences
  - modular-arithmetic
  - coprimality
related_proofs:
  - sylvester-sequence-oq-01
  - sylvester-sequence-oq-01-oq-02
difficulty: medium
source: gallery-gap
created: 2026-07-04
```

**Significance**: 5/10
**Tractability**: 7/10
