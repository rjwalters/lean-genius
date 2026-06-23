# Problem: Method of Types as Alternative Proof of Shannon Source Coding

**Slug**: shannon-source-coding-oq-04
**Created**: 2026-04-21T04:57:28-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
|T_Q^n| = \binom{n}{nQ(x_1), nQ(x_2), \ldots, nQ(x_{|\mathcal{X}|})} \approx 2^{nH(Q)}
$$

where $T_Q^n = \{ x^n \in \mathcal{X}^n : \hat{P}_{x^n} = Q \}$ is the **type class** of sequences
with empirical distribution $Q$, and the source coding theorem follows because the dominant
type satisfies $Q \approx p$, so typical sequences concentrate in a set of size $\approx 2^{nH(p)}$.

### Plain Language

The Csiszár-Körner **method of types** gives a combinatorial alternative to the standard
probabilistic (AEP-based) proof of Shannon's source coding theorem. Instead of appealing to
the weak law of large numbers applied to $-\log p(X_i)$, it:

1. Groups all length-$n$ sequences by their **empirical distribution** (type) $\hat{P}_{x^n}$
2. Shows there are only polynomially many distinct types: $|\mathcal{P}_n| \leq (n+1)^{|\mathcal{X}|}$
3. Bounds the size of each type class: $2^{nH(Q)} / (n+1)^{|\mathcal{X}|} \leq |T_Q^n| \leq 2^{nH(Q)}$
4. Identifies the dominant type as the one closest to the source distribution $p$
5. Concludes that encoding only the dominant type class achieves rate $H(p) + \epsilon$

The goal is to formalize this alternative proof in Lean 4, giving a second independent
verification of the source coding theorem via combinatorial rather than measure-theoretic arguments.

### Why This Matters

- **Proof diversity**: Two independent Lean proofs of the same theorem increase confidence
- **Method of types infrastructure**: $|T_Q^n| \approx 2^{nH(Q)}$ is a reusable lemma for
  channel coding, hypothesis testing, large deviations, and Sanov's theorem
- **Combinatorial vs. probabilistic**: Demonstrates the power of the combinatorial approach;
  the type class bounds require only multinomial coefficients and Stirling-type estimates,
  bypassing product measure spaces entirely
- **Foundation for Sanov**: The type class size bound directly yields Sanov's theorem on
  exponential rates for empirical measures, a major result in large deviation theory

## Known Results

### What's Already Proven

- Shannon source coding theorem (AEP-based proof) — `proofs/Proofs/ShannonSourceCoding.lean`
- Shannon entropy formalized — `proofs/Proofs/ShannonEntropy.lean`
- Multinomial coefficients — available in Mathlib (`Nat.multinomial`)
- Stirling's approximation — partial coverage in Mathlib

### What's Still Open

- Type class size bound $|T_Q^n| \approx 2^{nH(Q)}$ — not formalized
- Polynomial bound on number of types — straightforward but not in Mathlib
- Method-of-types proof of source coding — not formalized
- Sanov's theorem via types — downstream application

### Our Goal

Formalize the **type class size bounds** and use them to give an alternative Lean proof
of the source coding theorem. The minimum viable goal is the key lemma:

$$
|T_Q^n| \leq 2^{nH(Q)}
$$

with the lower bound $|T_Q^n| \geq 2^{nH(Q)} / (n+1)^{|\mathcal{X}|}$ as a stretch goal.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shannon-source-coding | Base proof (AEP approach) | Weak LLN, entropy, typical sets |
| shannon-entropy | Entropy definition and properties | Shannon H(X) formalization |
| shannon-channel-coding | Channel coding uses types implicitly | Mutual information |
| central-limit-theorem | AEP alternative infrastructure | Probability measures |

## Initial Thoughts

### Potential Approaches

1. **Direct multinomial bound**: Use `Nat.multinomial` to bound $|T_Q^n|$ via the multinomial
   coefficient identity $\sum_Q |T_Q^n| = |\mathcal{X}|^n$, then the dominant term bound.
   - Why it might work: Lean's Mathlib has multinomial coefficients
   - Risk: Entropy approximation from Stirling may need custom lemmas

2. **Bijective counting**: Establish a bijection between type classes and multisets, use
   existing Mathlib multiset cardinality infrastructure.
   - Why it might work: Avoids Stirling, more combinatorial
   - Risk: Bijection formalization can be verbose

3. **Companion file + Aristotle**: Write the structure with strategic sorries, submit to
   Aristotle for the routine multinomial manipulations.
   - Why it might work: Many steps are routine algebra/inequality chains
   - Risk: Aristotle may not handle entropy approximation steps

### Key Difficulties

- **Empirical distribution type**: Formalizing $\hat{P}_{x^n}(a) = \frac{|\{i : x_i = a\}|}{n}$
  as a probability measure in Lean
- **Entropy for rational distributions**: $H(Q)$ where $Q$ is a rational-valued empirical
  distribution requires real-valued entropy on finite distributions
- **Stirling approximation**: Upper/lower bounds on $n!$ and multinomial coefficients
- **Dominant type argument**: Showing empirical distribution concentrates near true $p$

### What Would a Proof Need?

- Type class definition: `def typeClass (Q : Fin k → ℚ) (n : ℕ) : Finset (Fin n → Fin k)`
- Cardinality bound: `theorem typeClass_card_le : (typeClass Q n).card ≤ 2^(n * H Q)`
- Type count bound: `theorem num_types_le_poly : (types n k).card ≤ (n+1)^k`
- Source coding from types: Combine the above for the compression theorem

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The combinatorial structure is well-understood (Csiszár-Körner textbook Chapter 1)
- Mathlib has multinomial coefficients (`Nat.multinomial`) as building blocks
- The existing `ShannonSourceCoding.lean` provides entropy infrastructure to reuse
- Main obstacle: Stirling approximation bounds — these may need 10-20 lines of custom lemmas
- The empirical distribution formalization is non-trivial but has precedent in probability theory

**Estimated Effort**:
- Exploration (OBSERVE): 1-2 days surveying Mathlib combinatorics and entropy infrastructure
- If tractable path found: 1-2 weeks for full type class size proof
- Core lemma only (upper bound): Potentially 3-5 days

## References

### Papers
- Csiszár & Körner, *Information Theory: Coding Theorems for Discrete Memoryless Systems*, Cambridge, 2011 — Chapter 1 defines method of types
- Cover & Thomas, *Elements of Information Theory*, 2nd ed., Chapter 11 — method of types
- Csiszár, "The method of types", *IEEE Trans. Inf. Theory*, 44(6):2505–2523, 1998

### Mathlib
- `Mathlib.Data.Nat.Choose.Multinomial` — multinomial coefficients
- `Mathlib.Analysis.SpecialFunctions.Log.Stirling` — Stirling approximation (partial)
- `Mathlib.Probability.ProbabilityMassFunction.Basic` — PMF infrastructure
- `Mathlib.Data.Finset.Card` — finite set cardinality
- `Mathlib.Combinatorics.Composition` — compositions of integers

## Metadata

```yaml
tags:
  - information-theory
  - coding-theory
  - combinatorics
  - entropy
  - method-of-types
related_proofs:
  - shannon-source-coding
  - shannon-entropy
  - shannon-channel-coding
difficulty: medium
source: gallery-gap
created: 2026-04-21T04:57:28-07:00
```

**Significance**: 7/10
**Tractability**: 6/10
