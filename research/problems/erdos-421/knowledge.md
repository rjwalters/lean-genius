# Erdős #421 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Is there a sequence $1\leq d_1<d_2<\cdots$ with density $1$ such that all products $\prod_{u\leq i\leq v}d_i$ are distinct?



A construction of Selfridge (see [786]) shows that there exists such a sequence of density $>1/e-\epsilon$ for any $\epsilon>0$.

See also [786].


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #786
- Problem #420
- Problem #422
- Problem #2
- Problem #39
- Problem #1

## References

- (None available)

## Sessions

See `src/data/research/problems/erdos-421.json` for the running session log
(`knowledge.builtItems`, `insights`). The summary below reflects state as of
2026-04-27.

### Session 2026-04-27 — Verification

**Mode**: REVISIT (knowledge_score=39 RICH).

**Outcome**: No new theorems added — file is in stable state.

**State verified**:
- `proofs/Proofs/Erdos421Problem.lean`: 579 lines, 25 theorems, 1 axiom, 0 sorries.
- The single axiom `selfridge_construction` encodes Selfridge's deep result
  (density > 1/e − ε); it is NOT removable without proving the original
  construction. Status `axiomatized` is appropriate.
- Gallery `src/data/proofs/erdos-421/meta.json` accurately reflects file state
  (axiomCount 1, theoremCount 25, sorries 0, lineCount 579).
- Prior counting infrastructure (numValidPairs_eq, total_product_lower_from_counting,
  adjacent_product_bound, product_strict_mono_right, etc.) is fully proven;
  the prior knowledge note "1 sorry remaining for numValidPairs_eq" is stale.

**Open questions for future sessions**:
- The mathematical conjecture itself remains open (does density 1 exist?).
- A potential next step: explicit density upper bounds derivable from
  `total_product_lower_from_counting`. This would be original mathematical
  research, not formalization.
- The `RelatedProblem786` definition is stated but no theorems use it; could
  be removed or connected to actual Erdős #786 results.

**No commits this session** — verification only.

---

*Generated from erdosproblems.com on 2026-01-13*
