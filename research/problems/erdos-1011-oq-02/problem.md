# Problem: Is the leading constant c = 1 in g(r) ~ c·r² log r?

**Slug**: erdos-1011-oq-02
**Created**: 2026-07-09T15:40:17-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Determine whether } g(r) = (1 + o(1))\, r^2 \log r, \text{ i.e. whether the constant } c \text{ with } g(r) \sim c\, r^2 \log r \text{ equals } 1.
$$

### Plain Language

In Erdős Problem #1011 one studies f_r(n), the least edge count forcing a triangle in an
n-vertex graph of chromatic number at least r. Simonovits showed that asymptotically
f_r(n) = n²/4 - g(r)·n/2 + O(1), where g(r) measures how many vertices must be deleted
from a triangle-free graph of chromatic number r to make it bipartite. The current bounds
are (1/2 - o(1))·r² log r ≤ g(r) ≤ (2 + o(1))·r² log r, leaving a factor-of-four gap in the
leading constant c of g(r) ~ c·r² log r. This problem asks whether the "natural" guess
c = 1 is correct — pinning the constant exactly halfway between the two known bounds.

### Why This Matters

Fixing c would close the last quantitative gap in a sixty-year-old extremal program linking
edge count, chromatic number, and triangle existence. The value of c is directly tied to the
asymptotics of the off-diagonal Ramsey number R(3,k), so a proof that c = 1 (or a refutation)
would sharpen our understanding of both extremal graph theory and Ramsey theory simultaneously.

## Known Results

### What's Already Proven

- Simonovits asymptotic f_r(n) = n²/4 - g(r)·n/2 + O(1) — Simonovits, "A method for solving extremal problems in graph theory" (1966), formalized as `simonovits_asymptotic` in `Proofs/Erdos1011Problem.lean`
- Lower bound g(r) ≥ (1/2 - o(1))·r² log r — Davies & Illingworth (2022), axiom `davies_illingworth_lower`
- Upper bound g(r) ≤ (2 + o(1))·r² log r — Hefetz, Horn, King & Pfender (2025), axiom `hhkp_upper`
- Exact small cases f_2, f_3, f_4 (Turán; Erdős-Gallai; Ren-Wang-Wang-Yang) — axioms `turan_theorem`, `erdos_gallai_theorem`

### What's Still Open

- Whether the leading constant c in g(r) ~ c·r² log r equals 1
- Whether the lower bound 1/2 or the upper bound 2 (or some value between) is the truth
- Any matching pair of bounds that would determine c exactly

### Our Goal

We do not attempt to resolve the open constant. Instead we aim to formalize the statement
"c = 1" as a precise conjecture in Lean 4, together with the surrounding bounds g(r) ≥ (1/2 -
o(1))·r² log r and g(r) ≤ (2 + o(1))·r² log r, so that the claim c = 1 is expressible and its
consistency with the known bounds is machine-checked.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1011 | Parent problem defining f_r(n), g(r), and the bounds that bracket c | Threshold functions, axiomatized extremal bounds |
| ramseys-theorem | Off-diagonal R(3,k) controls the upper bound on g(r) and hence on c | Ramsey coloring arguments, probabilistic bounds |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Formalize c as the (conjectural) limit of g(r)/(r² log r) and state c = 1 as a definition-level conjecture.
   - Why it might work: it needs only the existing axiomatized bounds plus a limit definition, so it is expressible without new mathematics.
   - Risk: the limit may not be known to exist, so the statement must be phrased conditionally (liminf/limsup) to be faithful.

2. **Approach B**: State the sandwich 1/2 ≤ liminf g(r)/(r² log r) ≤ limsup ≤ 2 and record c = 1 as the midpoint conjecture.
   - Why it might work: keeps everything within currently provable bounds and isolates the open gap cleanly.
   - Risk: proving even the sandwich in Lean requires unpacking the Davies-Illingworth and HHKP axioms into asymptotic form, which may need substantial real-analysis scaffolding.

### Key Difficulties

- The constant c is genuinely open; no proof strategy for c = 1 exists in the literature.
- Expressing r² log r asymptotics and o(1) error terms rigorously in Lean requires careful handling of `Filter.Tendsto` and `Asymptotics`.

### What Would a Proof Need?

- Key lemma 1: a Lean definition of g(r) consistent with the Simonovits asymptotic used in the parent file.
- Key lemma 2: formal statements of the lower and upper asymptotic bounds implying 1/2 ≤ liminf and limsup ≤ 2.
- Technical requirements: Mathlib's `Filter`, `Asymptotics.IsLittleO`, and real-logarithm infrastructure to phrase c = 1 faithfully.

## Tractability Assessment

**Difficulty**: Moonshot

**Justification**:
- Determining c is an open research problem with a factor-of-four gap unresolved since Simonovits's 1966 work.
- Similar constant-determination problems (e.g. exact off-diagonal Ramsey constants) remain famously open.
- Mathlib provides asymptotic and filter tooling for stating the conjecture, but no machinery capable of closing the gap.

**Estimated Effort**:
- Exploration: 2-3 days to formalize the statement and its consistency with known bounds
- If tractable: weeks for the formal-statement scaffolding only
- If hard: unknown (resolving c is open research)

## References

### Papers
- M. Simonovits, "A method for solving extremal problems in graph theory", 1966 — introduces g(r) and the asymptotic f_r(n) = n²/4 - g(r)·n/2 + O(1).
- E. Davies & M. Illingworth, "Triangles in graphs with forbidden subgraphs and large chromatic number", 2022 — proves g(r) ≥ (1/2 - o(1))·r² log r.
- P. Hefetz, M. Horn, R. King & F. Pfender, "Triangles in graphs with high chromatic number", 2025 — proves g(r) ≤ (2 + o(1))·r² log r.

### Online Resources
- https://erdosproblems.com/1011 — canonical statement of Erdős Problem #1011 and its status.

### Mathlib
- `Mathlib.Analysis.Asymptotics.Asymptotics` — provides `IsLittleO`/`IsBigO` for phrasing o(1) and ~ statements.
- `Mathlib.Order.Filter.Basic` — `liminf`/`limsup` needed to state the conjectural constant c.

## Metadata

```yaml
tags:
  - extremal-graph-theory
  - graph-theory
  - chromatic-number
  - triangles
  - turan-type
  - open-problem
related_proofs:
  - erdos-1011
  - ramseys-theorem
difficulty: moonshot
source: proof-suggestion
created: 2026-07-09T15:40:17-07:00
```
