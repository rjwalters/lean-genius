# Erdős #693 - Knowledge Base

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

Let $k\geq 2$ and $n$ be sufficiently large depending on $k$. Let $A=\{a_1<a_2<\cdots \}$ be the set of those integers in $[n,n^k]$ which have a divisor in $(n,2n)$. Estimate\[\max_{i} a_{i+1}-a_i.\]Is this $\leq (\log n)^{O(1)}$?



See also [446].


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
- Problem #446
- Problem #692
- Problem #694
- Problem #2
- Problem #39
- Problem #1

## References

- Er79e

## Sessions

### Session 2026-03-26 (researcher-7) - Prove polylog_implies_subpoly

**Mode**: REVISIT (AXIOM HUNT)
**Outcome**: progress (axiom eliminated, 3→2 axioms)

#### What I Did
- **Proved `polylog_implies_subpoly`** (was axiom, now 47-line theorem)
  - Key technique: `Real.log_le_rpow_div` gives `log x ≤ x^δ / δ`
  - With `δ = ε/(2α)`: `(log x)^α ≤ (1/δ)^α · x^(ε/2)` (rpow monotone)
  - Constant absorbed: for large x, `C·K ≤ x^(ε/2)`, so `C·K·x^(ε/2) ≤ x^ε`
  - Pattern follows Erdos1138OQ03 `cramer_implies_gap_sublinear`
- Changed imports to `import Mathlib` (needed for rpow algebra lemmas)

#### Key Findings
- `maxGap_pigeonhole` is FALSE as stated for small n (e.g., n=2, k=2: A={3}, maxGap=0, but axiom requires gap·1 ≥ 2)
- Remaining 2 axioms: `maxGap_pigeonhole` (needs corrected statement), `divisor_density_ford` (deep, Ford 2008)
- Note: Docker was unavailable so proof was not build-verified

#### Files Modified
- `proofs/Proofs/Erdos693Problem.lean` — polylog_implies_subpoly: axiom → theorem, import change
- `src/data/proofs/erdos-693/meta.json` — axiomCount: 3 → 2
- `src/data/research/problems/erdos-693.json` — updated knowledge

#### Next Steps
- Fix `maxGap_pigeonhole` statement (add `n ≥ 3, k ≥ 2` hypotheses)
- Build-verify `polylog_implies_subpoly` proof when Docker available

---

*Generated from erdosproblems.com on 2026-01-14*
