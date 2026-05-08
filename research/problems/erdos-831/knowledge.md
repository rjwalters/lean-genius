# Erdős #831 - Knowledge Base

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

Let $h(n)$ be maximal such that in any $n$ points in $\mathbb{R}^2$ (with no three on a line and no four on a circle) there are at least $h(n)$ many circles of different radii passing through three points. Estimate $h(n)$.



See also [104] and [506].


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
- Problem #104
- Problem #506
- Problem #830
- Problem #832
- Problem #2
- Problem #39
- Problem #1

## References

- Er75h
- Er92e

## Sessions

### Session 2026-05-08 (Bookkeeping audit, researcher-3)

**Mode**: REVISIT
**Outcome**: completed (no new mathematical work)

#### What I Did
- Verified `proofs/Proofs/Erdos831Problem.lean` on `origin/main`: 717 lines, 0 sorries, 1 axiom (`erdos_831_growing` on line 344)
- Verified `src/data/proofs/erdos-831/meta.json` already reflects accurate state (`status: "axiomatized"`, `badge: "axiom"`, `sorries: 0`, `axiomCount: 1`)
- Reviewed merged history: #7326, #7788, #7799, #7797, #7819, #7822, #7832, #15625, #15646 — converged to current axiomatized state on 2026-05-04
- Updated `research/problems/erdos-831/state.md` and `src/data/research/problems/erdos-831.json` from `Phase: NEW / iter 1 / "Begin problem exploration"` (which was severely stale relative to the iter-7 JSON-knowledge state) to `Phase: ACT / iter 8` with accurate focus / blockers / nextAction text

#### Axiom Classification
- `erdos_831_growing : ∀ k : ℕ, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → h n ≥ k`

  This is the open Erdős conjecture itself, NOT a routine assumption. Estimating h(n) is the actual open problem. erdosproblems.com/831 lists status: OPEN. There is no Mathlib path to a proof — proving even h(n) → ∞ would be a research-level mathematical advance.

#### Tractable Follow-Ups (out of scope for this session)
The following are bounded Lean tasks that could be opened as separate slugs but are NOT required to consider this slug "formalized to the open conjecture":

1. **Base cases h(n) for n ≤ 2.** Given the definition `h(n) = sInf {countDistinctRadii S | card S = n ∧ GP S}`, for any n ≤ 2 every term in the set is 0 (allCircumradiiFinset filters by p1≠p2≠p3≠p1, requiring ≥3 distinct points; sets of card ≤ 2 cannot produce such triples). Proof would route through a `countDistinctRadii_of_card_lt_three` lemma and pigeonhole arguments on the GP membership conditions.

2. **Upgrade the h(4) = 1 docstring to a theorem.** The docstring (Erdos831Problem.lean:323-336) describes the equilateral-triangle + circumcenter counterexample showing h(4) ≤ 1 (and h(4) ≥ 1 is trivial). Formalizing this would require constructing the Lean-coordinate set {(0,0), (1,0), (1/2, √3/2), (1/2, √3/6)}, proving GP via the existing 27/81-case patterns from the h(3) proof (scaled up to 64-case collinearity and 4-point-concyclic verification), and computing all four circumradii to 1/√3 by `field_simp + ring` after expanding the 2×2 determinant area formula.

3. **Prune unused stubs.** `orchardConfiguration` and `unitDistanceProblem` are defined but unused. They could either be removed or have at least one downstream use added.

None of these advance the open conjecture; they polish the formalization at the margins.

#### Files Modified
- `src/data/research/problems/erdos-831.json` (phase, currentState, knownResults, lastUpdate)
- `research/problems/erdos-831/state.md` (full rewrite to reflect actual iter-8 state)
- `research/problems/erdos-831/knowledge.md` (this session block)

#### Honest Outcome
This is a tracker-correction session, not a proof advance. The pool entry's `phase: NEW / "Begin problem exploration"` was severely stale; the actual formalization has been at the axiomatized-with-1-axiom state since 2026-05-04. The candidate-pool record is now consistent with the gallery `meta.json` and the Lean source.

The full Erdős #831 conjecture remains genuinely open at the research level.

---


*Generated from erdosproblems.com on 2026-01-15*
