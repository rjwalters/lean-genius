# Problem: Strong Divisibility for Lucas Sequences Uₙ(P,Q)

**Slug**: fibonacci-identities-oq-02-oq-02
**Created**: 2026-07-01T08:49:18-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $U_n(P,Q)$ be the Lucas sequence defined by $U_0 = 0$, $U_1 = 1$, $U_{n+1} = P\,U_n - Q\,U_{n-1}$. Identify hypotheses on $(P,Q)$ under which

$$
U_m \mid U_n \iff m \mid n,
$$

and more generally $\gcd(U_m, U_n) = U_{\gcd(m,n)}$ (the strong divisibility property).

### Plain Language

The Fibonacci numbers ($P=1$, $Q=-1$) form a strong divisibility sequence: $F_m \mid F_n$ exactly when $m \mid n$. This problem asks for the precise conditions on the parameters $P, Q$ of a general Lucas sequence under which the same characterization holds.

### Why This Matters

Strong divisibility sequences underlie primality tests (Lucas–Lehmer), factorization methods, and the theory of divisibility sequences. Generalizing the parent Fibonacci result to arbitrary $U_n(P,Q)$ identifies exactly which arithmetic hypotheses (e.g. $\gcd(P,Q)=1$) are load-bearing, sharpening a well-known but often folklore result.

## Known Results

### What's Already Proven

- Fibonacci strong divisibility `F_m ∣ F_n ↔ m ∣ n` and `gcd(F_m,F_n) = F_{gcd(m,n)}` — parent entry `fibonacci-identities-oq-02`.
- Lucas-sequence identities `U_{m+n} = U_m U_{n+1} - Q U_{m-1} U_n` (addition formula).
- Mathlib has `Nat.fib` GCD lemmas (`Nat.fib_gcd`, `Nat.fib_dvd`); Lucas sequences generally need custom development.

### What's Still Open

- Whether Mathlib carries a general `Uₙ(P,Q)` divisibility-sequence API, or it must be built.
- The exact side conditions (`gcd(P,Q)=1`, non-degeneracy `P²-4Q ≠ 0`) required for `Uₘ ∣ Uₙ ↔ m ∣ n`.

### Our Goal

State and prove the strong-divisibility characterization for `U_n(P,Q)` in Lean under `gcd(P,Q)=1`, reusing the Lucas addition/duplication formulas. Recover the Fibonacci case `P=1, Q=-1` as a corollary.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fibonacci-identities-oq-02 | Parent: Fibonacci strong divisibility | gcd induction, addition formula |
| fibonacci-identities | Base identities | recurrence, induction |
| pell-equation | Related second-order recurrence | Lucas sequences U/V |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Mirror the Fibonacci gcd proof. Prove `gcd(U_m, U_n) = U_{gcd(m,n)}` by Euclidean-style induction using the addition formula `U_{m+n} = U_m U_{n+1} - Q U_{m-1} U_n` and the coprimality `gcd(U_n, U_{n+1}) = 1` (needs `gcd(P,Q)=1`).
   - Why it might work: the parent proof structure transfers with `Q`-weighted terms.
   - Risk: establishing `gcd(U_n,U_{n+1})=1` and consecutive-term coprimality under general `(P,Q)`.

2. **Approach B**: Work in `ℤ[x]/(x² - Px + Q)` (companion matrix `[[P,-Q],[1,0]]`), using matrix-power structure to derive divisibility.
   - Why it might work: matrix formulation gives clean addition formulas.
   - Risk: heavier algebraic setup; may exceed the direct induction.

### Key Difficulties

- Identifying and formalizing the minimal hypotheses on `(P,Q)`.
- Proving consecutive-term coprimality `gcd(U_n, U_{n+1}) = 1` in the general setting.
- Whether to build a reusable `LucasSequence` structure or specialize.

### What Would a Proof Need?

- Key lemma 1: addition formula `U_{m+n} = U_m U_{n+1} - Q U_{m-1} U_n`.
- Key lemma 2: `gcd(U_n, U_{n+1}) = 1` under `gcd(P,Q)=1`.
- Technical requirements: strong induction / `Nat.gcd` recursion, integer sequence definitions.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The Fibonacci parent proof provides a concrete template.
- Lucas sequences may need to be defined from scratch (limited Mathlib support), adding scaffolding.
- The divisibility induction is standard but the parameter generality adds side-condition work.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1 week
- If hard: 2+ weeks (full reusable API)

## References

### Papers
- Lehmer, "An extended theory of Lucas' functions," *Annals of Mathematics* (1930).
- Ribenboim, *The New Book of Prime Number Records* — Lucas sequence divisibility.

### Online Resources
- https://en.wikipedia.org/wiki/Lucas_sequence — definitions and divisibility properties.

### Mathlib
- `Mathlib.Algebra.GCDMonoid.Basic`, `Mathlib.Data.Nat.Fib.Basic` — `Nat.fib_gcd`, `Nat.fib_dvd` as the Fibonacci-special-case template.

## Metadata

```yaml
tags:
  - number-theory
  - recurrence-sequences
  - divisibility
related_proofs:
  - fibonacci-identities-oq-02
  - pell-equation
difficulty: medium
source: gallery-gap
created: 2026-07-01T08:49:18-07:00
```

**Significance**: 6/10
**Tractability**: 6/10
