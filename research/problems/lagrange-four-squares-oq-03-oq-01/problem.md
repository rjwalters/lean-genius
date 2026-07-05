# Problem: Sharpen the Elementary Waring Upper Bound g(4) ≤ 50

**Slug**: lagrange-four-squares-oq-03-oq-01
**Created**: 2026-07-01T22:11:22-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\exists\, G < 53 \quad\text{such that}\quad \forall\, N \in \mathbb{N},\ \exists\, x_1,\dots,x_G \in \mathbb{N},\quad N = \sum_{i=1}^{G} x_i^4 .
$$

Concretely, we target $G = 50$: every natural number is a sum of at most $50$ fourth powers, established by a purely elementary, machine-checked argument that refines the parent's $g(4) \le 53$.

### Plain Language

Waring's problem asks, for each exponent $k$, for the smallest number $g(k)$ such that *every* positive integer can be written as a sum of at most $g(k)$ non-negative $k$-th powers. For squares the answer is Lagrange's four-square theorem, $g(2) = 4$. For fourth powers the elementary route runs through Liouville's identity
$$6(a^2+b^2+c^2+d^2)^2 = \sum_{1 \le i < j \le 4}\big((x_i+x_j)^4 + (x_i-x_j)^4\big),$$
which turns $6m^2$ into a sum of $12$ fourth powers whenever $m$ is a sum of four squares — and by Lagrange every $m$ is. Feeding Lagrange in twice and splitting $N = 6\lfloor N/6\rfloor + (N \bmod 6)$ gives the parent's bound of $48 + 5 = 53$ summands. This problem asks how much lower a still-elementary argument can drive that constant: by treating the small remainder $N \bmod 6$ and the near-zero blocks more carefully (many of the $48$ summands are genuinely $0$), the $53$ can be trimmed toward $50$ and below.

### Why This Matters

Mathlib provides Lagrange's four-square theorem but no constructive Waring bound for fourth powers at all; the parent entry supplied the first machine-checked $g(4) \le 53$. Sharpening that constant demonstrates that the *quality* of an elementary, axiom-free additive bound can be improved without invoking the analytic circle method, and it produces reusable machinery (tighter residue bookkeeping, minimal-length sum-of-fourth-powers lists) for Waring-type formalizations at higher exponents. It also narrows the machine-checked bracket around the true value $g(4) = 19$.

## Known Results

### What's Already Proven

- Lagrange's four-square theorem: every $n \in \mathbb{N}$ is a sum of four squares — `Nat.sum_four_squares` (Mathlib, `Mathlib.NumberTheory.SumFourSquares`).
- $g(4) \le 53$, machine-checked and axiom-free via Liouville's identity + Lagrange used twice + Euclidean division by $6$ — parent entry `lagrange-four-squares-oq-03` (`Proofs/LagrangeFourSquaresOQ03.lean`, `waring_four`).
- Finiteness of $g(k)$ for every $k$ — Hilbert (1909); the fourth-power case by Liouville (1859) via the identity above.
- Classical elementary refinements pushing Liouville's bound below $53$ (into the $50$/$45$ range) by more careful residue and small-number handling — folklore following Liouville and Wieferich.
- The exact value $g(4) = 19$ — lower bound from the "bad" numbers $n = 31 \cdot 16^k$ (which force $19$ fourth powers), matching upper bound completed by Balasubramanian, Deshouillers, and Dress (1986).

### What's Still Open

- How low can a *purely elementary*, machine-checked argument drive the fourth-power Waring constant — can the Liouville route plus residue/small-case bookkeeping reach $50$, $45$, or lower while staying axiom-free?
- Whether the finite small-case verification (each residue class and each small $N$ needing few fourth powers) can be discharged by `decide`/`Decidable` instances without ballooning kernel cost.

### Our Goal

Prove $g(4) \le 50$: strengthen the parent's `waring_four` to at most $50$ fourth powers, keeping the proof elementary (Liouville identity + Lagrange) and axiom-free (no `native_decide`, so no `Lean.ofReduceBool`). The scope is the constant only — not the true value $g(4) = 19$, which is out of elementary reach.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| lagrange-four-squares-oq-03 | Direct parent; establishes g(4) ≤ 53 via the Liouville identity we refine | Liouville identity, `Nat.sum_four_squares`, `ring`, list-based sum-of-fourth-powers predicate |
| lagrange-four-squares | Grandparent; the four-square theorem that feeds every step | Descent / Euler four-square identity, `Nat.sum_four_squares` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — refined residue analysis mod 16 plus small-remainder handling**: Rather than paying a flat $5$ summands for $N \bmod 6$ and a flat $48$ for the quotient, split by residue (fourth powers are $\equiv 0$ or $1 \pmod{16}$) so most residue classes need far fewer than $5$ extra unit summands, and reuse the many zero summands already present in the $48$-term block.
   - Why it might work: fourth powers occupy only two residue classes mod 16, so the achievable sums in each class are highly constrained and finitely checkable, letting several of the $53$ summands be provably discarded.
   - Risk: the residue bookkeeping mod 16 interacts with the Euclidean-division-by-6 decomposition, and reconciling the two moduli cleanly (without a large case explosion) is fiddly.

2. **Approach B — greedy/decomposition argument bounding the number of blocks**: Subtract the largest fourth power $\le N$ repeatedly for the small part while using the Liouville blocks for the bulk, and bound the total number of blocks (rather than summands) needed to cover all residues, padding minimally.
   - Why it might work: a block-counting bound sidesteps tracking individual summands and can absorb the residue directly into a short greedy tail whose length is bounded by a finite check.
   - Risk: greedy termination and the worst-case tail length require a finite verification whose size must be kept small enough for the Lean kernel; an overly generous tail bound could fail to beat $53$.

### Key Difficulties

- Residue bookkeeping mod 16 (fourth powers are $0$ or $1$ mod 16) must be reconciled with the mod-6 Euclidean split used to assemble the blocks.
- A finite small-case verification (that each residue / each small $N$ needs few fourth powers) has to be discharged cheaply — ideally by `decide`, not `native_decide`, to preserve the axiom-free status.
- Keeping the whole argument elementary: no circle-method estimates, no analytic input, only Lagrange + polynomial identities + finite checks.

### What Would a Proof Need?

- Key lemma 1: a sharpened count showing the $48$-summand block can be reduced (or that its zero summands can absorb part of the residue) so the total drops below $53$.
- Key lemma 2: a residue-class lemma (fourth powers mod 16 ∈ {0,1}) turning "few summands suffice for the remainder" into a finite, decidable check.
- Technical requirements: the parent's `IsSumOfFourthPowers` predicate and its `append`/zero-pad closure lemmas; a `Decidable`-backed finite verification for the small cases; the Liouville identity closed by `ring`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The parent already did the hard structural work (Liouville identity, `natAbs` bridge, list predicate, $g(4) \le 53$); this is a refinement of the constant, not a new mechanism.
- Similar elementary residue-and-small-case arguments are standard and finite, and the fourth-power residue structure mod 16 is very simple (only two classes).
- Mathlib supplies `Nat.sum_four_squares`, `ring`, and `decide` for the finite residue checks — everything needed is already in place.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 3–5 days
- If hard: unknown (residue/modulus reconciliation may resist a clean, small kernel check)

## References

### Papers
- Liouville (1859) — the identity $6(a^2+b^2+c^2+d^2)^2 = \sum_{i<j}((x_i+x_j)^4+(x_i-x_j)^4)$ giving elementary finiteness of $g(4)$.
- Hilbert (1909) — finiteness of $g(k)$ for all exponents $k$.
- Balasubramanian, Deshouillers, Dress (1986) — completion of the exact value $g(4) = 19$.

### Online Resources
- https://en.wikipedia.org/wiki/Waring%27s_problem — overview of $g(k)$, the fourth-power case, and the history of the bounds.

### Mathlib
- `Mathlib.NumberTheory.SumFourSquares` (`Nat.sum_four_squares`) — Lagrange's four-square theorem, the engine of every step.
- `decide` / `Decidable` instances on `Nat` — for the finite residue-class and small-remainder verifications, keeping the proof `native_decide`-free (no `Lean.ofReduceBool`).

## Metadata

```yaml
tags:
  - number-theory
  - waring-problem
  - four-squares
  - fourth-powers
  - liouville-identity
related_proofs:
  - lagrange-four-squares-oq-03
  - lagrange-four-squares
difficulty: medium
source: gallery-gap
created: 2026-07-01T22:11:22-07:00
```

**Significance**: 5/10
**Tractability**: 6/10
