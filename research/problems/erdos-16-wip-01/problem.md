# Problem: Complete the Lean Formalization of Erdős Problem #16 (Odd Integers Not of Form 2^k + p)

**Slug**: erdos-16-wip-01
**Created**: 2026-07-09T17:33:18-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
E = \{\, n \text{ odd} : \forall k \geq 1,\ \forall p \text{ prime},\ n \neq 2^k + p \,\}, \qquad \underline{d}(E) > 0.
$$

The gallery entry additionally formalizes Erdős's conjecture, $\mathrm{ErdosConjecture16} : E = (\text{arithmetic progression}) \cup (\text{density-}0\text{ set})$, which Chen (2023) disproved.

### Plain Language

The completion task is to strengthen the work-in-progress Lean 4 formalization of Erdős Problem #16, which studies the odd integers that cannot be written as a power of two plus a prime. Romanoff (1934) proved that a positive proportion of odd integers *are* of the form $2^k + p$, so the exceptional set $E$ has density less than one half. Erdős (1950) used covering congruences with moduli $\{2,3,4,6,8,12,24\}$ to force an infinite arithmetic progression into $E$, and conjectured that $E$ is essentially just this progression plus a negligible density-zero remainder. Chen (2023) disproved that conjecture: $E$ has a much richer structure with several independent positive-density pieces. The current Lean file defines the relevant objects but leaves the supporting theorems (Romanoff's density bound, the covering-congruence construction) documented only in comments; our goal is to formalize the provable ones and cleanly isolate the genuinely deep results.

### Why This Matters

1. **Romanoff-type density**: The problem is a canonical example of a sieve-plus-prime-number-theorem density argument, and formalizing Romanoff's lower bound gives Mathlib a reusable additive-density result.
2. **Covering congruences**: Erdős's construction is the prototype for covering-system techniques that recur across number theory (Sierpiński and Riesel numbers, de Polignac's problem); a verified instance is valuable infrastructure.
3. **Honest status tracking**: Chen's disproof means the entry must clearly separate what is proven, what is merely documented, and what remains open, keeping the gallery's credibility intact.

## Known Results

### What's Already Proven

- Romanoff's theorem — the set $\{2^k + p\}$ has positive lower density among the odd integers (Romanoff, Math. Ann. 109, 1934); documented in the Lean file but not yet formalized.
- Erdős's covering-congruence result — an infinite arithmetic progression lies inside $E$ (Erdős, Summa Brasil. Math. 2, 1950).
- Chen's disproof — $E$ is not a single arithmetic progression plus a density-zero set (Chen, 2023).

### What's Still Open

- The exact structure and precise density of the exceptional set $E$.
- Whether there are infinitely many twin pairs $(n, n+2)$ that are both exceptional.

### Our Goal

Complete the WIP Lean file `Proofs/Erdos16Problem.lean`: discharge the finitely-checkable and elementary facts (for example, that specific numbers such as $127$, $149$, $251$ are exceptional, verified by `decide` on the compositeness of $n - 2^k$; and basic monotonicity and containment lemmas about `lowerDensity`), turn the currently comment-only Romanoff and covering statements into stated theorems where a Mathlib proof is within reach, and keep the genuinely deep pieces (Romanoff's full density bound, Chen's structural disproof) explicitly axiomatized with clear `assumptions` disclosure. Do not attempt to reprove Chen's theorem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-16 | Parent gallery entry (badge wip): defines `IsRomanoff`, `ExceptionalSet`, `lowerDensity`, `IsCoveringSystem`, and `ErdosConjecture16` with all supporting results left in comments. | Covering congruences, asymptotic density, sieve methods, Chinese Remainder Theorem |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Discharge the finite/computational lemmas first.
   - Why it might work: Showing a specific $n$ is exceptional reduces to checking that $n - 2^k$ is composite for the finitely many $k$ with $2^k < n$, which `decide`/`native_decide` handles directly.
   - Risk: `native_decide` introduces `Lean.ofReduceBool`, so those results must be counted as axiomatized per the axiom-integrity policy.

2. **Approach B**: State Romanoff's theorem as a clean interface theorem and build the covering-system instance concretely.
   - Why it might work: The covering system with moduli $\{2,3,4,6,8,12,24\}$ is finite and its covering property is decidable; the reciprocal-sum condition can be checked exactly.
   - Risk: Connecting the covering property to compositeness of $n - 2^k$ for a whole residue class still needs a nontrivial argument that may resist full formalization.

### Key Difficulties

- Romanoff's positive-density bound rests on the prime number theorem and a divergent sieve sum, neither of which is easy to assemble in Mathlib.
- Chen's disproof is recent and deep; it cannot be formalized within this scope and must stay axiomatized.

### What Would a Proof Need?

- Key lemma 1: an exact, decidable predicate for "$n$ is exceptional" over the finite range of relevant $k$.
- Key lemma 2: a verified covering system (residue classes tiling $\mathbb{Z}$ with the prescribed moduli) and its link to compositeness.
- Technical requirements: Mathlib's `Nat.Prime`, `ZMod`, asymptotic density scaffolding, and careful separation of proven vs. axiomatized statements in `meta.json`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The elementary and finite parts (specific exceptional numbers, covering-system checks, density monotonicity) are genuinely tractable and can move the entry closer to verified.
- The core analytic result (Romanoff's density lower bound) and Chen's structural disproof are research-grade and cannot be fully formalized here; they must remain axiomatized.
- Mathlib provides primality, modular arithmetic, and `Finset` machinery sufficient for the tractable pieces.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: 1-2 weeks for the finite/covering lemmas
- If hard: unknown for Romanoff's full density theorem

## References

### Papers
- P. Erdős, "On integers of the form 2^k + p and some related problems", Summa Brasil. Math. 2 (1950), 113–123 — introduces the covering-congruence construction.
- N. P. Romanoff, "Über einige Sätze der additiven Zahlentheorie", Math. Ann. 109 (1934), 668–678 — positive lower density of $2^k + p$.
- Y.-G. Chen and X.-G. Sun, "On Romanoff's constant", J. Number Theory 106 (2004), 275–284 — improved density bounds.

### Online Resources
- https://erdosproblems.com/16 — canonical statement and status of Problem #16.
- https://oeis.org/A006285 — the exceptional set $\{1, 127, 149, 251, 331, \ldots\}$.

### Mathlib
- `Mathlib.Data.Nat.Prime.Basic` — primality predicate used to define `IsRomanoff`.
- `Mathlib.Data.ZMod.Basic` — modular arithmetic for the covering system.

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - romanoff-type
  - covering-congruences
  - additive-density
  - sieve-methods
related_proofs:
  - erdos-16
difficulty: high
source: proof-suggestion
created: 2026-07-09T17:33:18-07:00
```

**Significance**: 7/10
**Tractability**: 5/10
