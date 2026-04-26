# Problem: Efficient CRT Construction with Explicit Bézout Coefficients

**Slug**: chinese-remainder-constructive-oq-04-oq-03-oq-01
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Given a system of congruences $x \equiv a_i \pmod{m_i}$ for $i = 1, \ldots, n$ over a
Euclidean domain, where each pair $(m_i, m_j)$ satisfies the GCD compatibility condition
$\gcd(m_i, m_j) \mid a_i - a_j$, produce an *explicit* solution formula using Bézout
coefficients rather than an existential witness.

$$x = \sum_{i=1}^n a_i \cdot e_i \pmod{\text{lcm}(m_1,\ldots,m_n)}$$

where $e_i$ are idempotents constructed from Bézout coefficients for $(m_i, M/m_i)$.

### Plain Language

The gallery proof `chinese-remainder-constructive-oq-04-oq-03` (*Non-Coprime CRT for
Arbitrary Lists*) proves existence of a solution but uses a non-constructive induction
via the two-moduli CRT. This problem asks for a computable formula: given explicit Bézout
witnesses for each modulus pair, write down the actual solution as a closed-form sum.

### Why This Matters

- Constructive proofs enable code extraction and verified computation
- An explicit formula is needed for efficient modular reconstruction algorithms
- Bridges the gap between the existential gallery proof and Mathlib's computational CRT

## Known Results

### What's Already Proven

- `chinese-remainder-constructive-oq-04-oq-03` (gallery, verified) — Existential CRT for arbitrary lists over Euclidean domains, via two-moduli CRT induction
- `chinese-remainder-constructive-oq-04` (gallery) — CRT for four moduli
- `chineseRemainder` in `Mathlib.Data.ZMod.Basic` — coprime case, explicit formula

### What's Still Open

- Explicit Bézout-based formula for the non-coprime many-moduli case
- Relation between `listLcm` and `Mathlib.Finset.lcm`
- Minimal non-negative solution bounding by `listLcm` in ℕ

### Our Goal

Formalize in Lean 4 an explicit solution construction:

```lean
theorem crt_explicit_bezout (ms : List ℤ) (as : List ℤ)
    (h_len : ms.length = as.length)
    (h_compat : ∀ i j, (ms[i]).gcd (ms[j]) ∣ as[i] - as[j])
    (bezout : ∀ i, ∃ u v, u * ms[i] + v * (listLcm ms / ms[i]) = 1) :
    ∃ x : ℤ, ∀ i, x ≡ as[i] [ZMOD ms[i]] := by
  -- explicit construction via idempotents
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `chinese-remainder-constructive-oq-04-oq-03` | Direct parent — existential CRT | induction, GCD, EuclideanDomain |
| `chinese-remainder-constructive-oq-04` | Four-moduli case | Bezout, lcm |
| `chinese-remainder-constructive` | Base two-moduli constructive CRT | gcd_eq_one, Bezout |

## Initial Thoughts

### Potential Approaches

1. **Idempotent decomposition** (classical approach):
   - For each $i$, compute $e_i = b_i \cdot (M/m_i)$ where $b_i$ is the Bézout inverse
   - Then $x = \sum a_i e_i \pmod M$ where $M = \text{lcm}(m_1,\ldots,m_n)$
   - Why it might work: standard constructive CRT recipe; Mathlib has all pieces
   - Risk: coprimality assumption needed for idempotents; non-coprime case needs pairwise reduction

2. **Iterated two-moduli construction**:
   - Build the solution iteratively: start with $x_1 = a_1$, then combine $x_k$ and $a_{k+1}$
   - Use explicit Bézout witnesses at each step
   - Why it might work: directly mirrors the inductive gallery proof structure
   - Risk: formula for $e_i$ becomes complex; may need auxiliary lemmas about `listLcm`

### Key Difficulties

- Non-coprime case: idempotents don't directly exist; must use compatibility conditions
- `listLcm` vs `Finset.lcm`: may need to bridge definitions
- Integer quotients: `M / m_i` must be exact division with a proof

### What Would a Proof Need?

- Key lemma: `listLcm_dvd_lcm_pair` relating `listLcm` to pairwise LCMs
- Key lemma: Explicit Bézout witness lifting from pairs to the full list
- Technical: `Int.emod_emod_of_dvd` for combining residues

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical content is classical and well-known
- Mathlib has `Int.gcd_eq_one_iff_coprime`, `Finset.lcm`, `Int.chineseRemainder`
- Main work: bridging `listLcm` vs `Finset.lcm` and writing the explicit formula
- Estimated 3-5 days for a careful Lean 4 proof

**Estimated Effort**:
- Exploration: 3-5 hours (survey Mathlib CRT + GCD infrastructure)
- If tractable: 3-5 days
- If API mismatch is severe: 1 week

## References

### Papers
- Cohen, "A Course in Computational Algebraic Number Theory" (1993) — Chapter 1 on CRT

### Mathlib
- `Mathlib.Data.ZMod.Basic` — `chineseRemainder` coprime case
- `Mathlib.RingTheory.Coprime.Basic` — coprimality lemmas
- `Mathlib.Data.Int.GCD` — `Int.gcd`, `Int.lcm`, Bezout

## Metadata

```yaml
tags:
  - number-theory
  - algorithms
  - chinese-remainder
  - bezout
  - constructive
related_proofs:
  - chinese-remainder-constructive-oq-04-oq-03
  - chinese-remainder-constructive-oq-04
  - chinese-remainder-constructive
difficulty: medium
source: gallery-gap
created: 2026-04-23
```

**Significance**: 7/10
**Tractability**: 6/10
