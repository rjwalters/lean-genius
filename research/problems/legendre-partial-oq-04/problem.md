# Problem: Formalizing Oppermann's Conjecture and Computational Verification

**Slug**: legendre-partial-oq-04
**Created**: 2026-06-27T11:33:01-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall n > 1,\quad \bigl(\exists\, p \in \mathbb{P},\; n^2 - n < p < n^2\bigr) \;\wedge\; \bigl(\exists\, q \in \mathbb{P},\; n^2 < q < n^2 + n\bigr)
$$

Equivalently, splitting the Legendre interval $(n^2, (n+1)^2)$ at its midpoint $n^2 + n$, Oppermann asserts a prime in each half: one in $(n^2, n^2+n)$ and one in $(n^2+n, (n+1)^2)$. The two formulations coincide after re-indexing, since $(n^2-n, n^2) = ((n-1)^2 + (n-1),\, n^2)$.

### Plain Language

Between any two consecutive perfect squares there is not just one prime (that is Legendre's conjecture) but at least one prime on *each side* of the halfway point. So the gap between squares is "primey enough" that even cutting it in two leaves a prime in both pieces. We do not try to prove this for all $n$ — instead we state it precisely in Lean and check it by direct computation for every $n$ up to a chosen bound.

### Why This Matters

Oppermann's conjecture (1882) is a central rung in the hierarchy of prime-gap conjectures near perfect squares: Cramér $\Rightarrow$ Oppermann $\Rightarrow$ Legendre $\Leftrightarrow$ Andrica $\Rightarrow$ Bertrand (the only proven member). It is strictly stronger than Legendre's conjecture — a counterexample to Legendre would also refute Oppermann, but Oppermann could fail while Legendre holds. It also sharpens the picture of maximal prime gaps near $x$ that connects to Brocard's and Andrica's conjectures. Formalizing the statement and verifying it computationally extends the existing Legendre gallery entry with a measurably harder companion result, and demonstrates the same decidable-witness methodology on a stronger claim.

## Known Results

### What's Already Proven

- Bertrand's postulate (a prime in $(n, 2n)$) — Chebyshev (1852); formalized in Mathlib as `Nat.bertrand` and in the gallery as `bertrands-postulate`
- Baker–Harman–Pintz (a prime in $(x, x + x^{0.525})$ for large $x$) — *Proc. LMS* 83 (2001); implies both Legendre and Oppermann asymptotically (for $x=n^2$ it gives a prime in $(n^2, n^2 + n^{1.05})$, eventually inside each half-interval)

### What's Still Open

- Oppermann's conjecture itself is OPEN for all $n$ — no general proof exists (only finite computational verification, here to bounds far beyond what we attempt in Lean)
- The general unconditional existence of a prime in the shorter sub-interval $(n^2, n^2+n)$ of length $n$, which is what makes Oppermann strictly harder than Legendre

### Our Goal

State Oppermann's conjecture precisely in Lean 4 as a decidable per-$n$ predicate over `Nat`, then verify it by computation for all $n$ from $2$ up to a fixed bound (e.g. $n \le 100$ or as far as `native_decide`/a sieve runs comfortably). We do NOT attempt the general proof — the deliverable is a faithful formal statement plus a machine-checked finite verification, with the full conjecture recorded as an axiom (mirroring the parent `legendre-partial` entry).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| legendre-partial | Parent entry; Oppermann is the strictly stronger split-interval version | explicit prime witnesses, `native_decide`, conjecture stated as `axiom` |
| bertrands-postulate | Weakest (proven) member of the same prime-gap hierarchy; a true general theorem | `Nat.bertrand` from Mathlib, prime-counting bounds |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Decidable predicate + bounded `native_decide`.
   - Define `OppermannAt n : Prop := (∃ p, p.Prime ∧ n^2 - n < p ∧ p < n^2) ∧ (∃ q, q.Prime ∧ n^2 < q ∧ q < n^2 + n)`, supply explicit witnesses, and discharge each case with `native_decide` (or `decide` for the smallest cases).
   - Why it might work: each case is a finite, decidable check; exactly the pattern that already succeeds in `legendre-partial`.
   - Risk: `native_decide` invokes the compiler kernel and pulls in `Lean.ofReduceBool`, so any verified range is `axiomatized`, not `verified`; the range is also bounded and does not scale to large $n$.

2. **Approach B**: Explicit prime sieve + `decide` over a bounded list.
   - Build a small verified primality test or a `List`-based sieve, prove the witnesses prime once, and fold the per-$n$ checks into a single `decide`/`Finset.forall` over `Finset.Icc 2 N`.
   - Why it might work: a single bounded universally-quantified statement is cleaner to state and may avoid per-case boilerplate.
   - Risk: kernel `decide` is far slower than `native_decide` and may time out; engineering a fast certified sieve in Lean is itself nontrivial.

### Key Difficulties

- Oppermann's conjecture is OPEN — only the finite verification is provable; the general $\forall n$ statement must remain an `axiom` (an honest assumption), never a claimed theorem.
- Axiom Integrity Policy: `native_decide` depends on `Lean.ofReduceBool`, so the verified-range result must be marked `status: "axiomatized"`, `badge: "axiom"`, with `Lean.ofReduceBool` disclosed in `assumptions` and `axiomCount ≥ 1`.

### What Would a Proof Need?

- Key lemma 1: a primality witness for one prime in each half-interval, per $n$ in range.
- Key lemma 2: decidability of `OppermannAt n` reduced to a finite bounded search.
- Technical requirements: `Nat` arithmetic over $n^2 \pm n$, careful handling of `Nat` truncated subtraction for $n^2 - n$, and a bounded universal quantifier over `Finset.Icc`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The precise Lean statement and the bounded computational verification are entirely tractable and mirror an existing successful entry; only the general conjecture (out of scope) is hard.
- Similar problems already solved: `legendre-partial` (same witness + `native_decide` pattern) and `bertrands-postulate` (the proven base case of the hierarchy).
- Techniques available in Mathlib: `Nat.Prime`, `Nat.minFac`, `Nat.decidablePrime`, `decide` / `native_decide`, and `Finset.Icc` for bounded ranges.

**Estimated Effort**:
- Exploration: a few hours (settle the statement form and verification bound)
- If tractable: 1–3 days (witnesses, decidable predicate, gallery integration)
- If hard: the general conjecture is unknown / out of reach — not attempted

## References

### Papers
- Oppermann, L., "Om vor Kundskab om Primtallenes Mængde mellem givne Grændser", *Oversigt over det Kongelige Danske Videnskabernes Selskabs Forhandlinger*, 1882 — original statement of the conjecture
- Baker, R. C.; Harman, G.; Pintz, J., "The difference between consecutive primes, II", *Proc. London Math. Soc.* 83 (2001), 532–562 — best unconditional gap bound, implies Oppermann asymptotically

### Online Resources
- https://en.wikipedia.org/wiki/Oppermann%27s_conjecture — statement, history, hierarchy relative to Legendre/Andrica/Cramér, and computational status
- https://en.wikipedia.org/wiki/Legendre%27s_conjecture — the weaker parent conjecture and prime-gap context

### Mathlib
- `Mathlib.Data.Nat.Prime.Basic` (`Nat.Prime`, `Nat.minFac`, `Nat.decidablePrime`) — primality definition and a decidable instance for computational checks
- `Mathlib.Tactic` (`decide`, `native_decide`) — discharges the finite per-$n$ verification (note `native_decide` ⇒ `Lean.ofReduceBool`, hence `axiomatized`)

## Metadata

```yaml
tags:
  - number-theory  # or: algebra, analysis, topology, combinatorics, etc.
  - prime-gaps
  - sieve-methods
related_proofs:
  - legendre-partial
  - bertrands-postulate
difficulty: medium
source: user-request
created: 2026-06-27T11:33:01-07:00
```
