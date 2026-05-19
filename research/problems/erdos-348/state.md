# Current State

**Phase**: COMPLETED
**Since**: 2026-03-24T15:15:41Z (registry graduated)
**Iteration**: 2

## Current Focus

Gallery proof verified. `proofs/Proofs/Erdos348Problem.lean` (570 lines,
0 sorries, 1 axiom, 18 theorems, 14 definitions), status `axiomatized`,
badge `axiom`. The Erdős database status for the problem itself remains
"open" — the slug's deliverable is the formalization plus base cases,
not a resolution of the open mathematics.

## Deliverable (Shipped)

Formalization of Erdős #348 (Erdős–Graham, ErGr80): for what values of
$0 \leq m < n$ is there a complete sequence $A = \{a_1 \leq a_2 \leq \cdots\}$
of integers that remains complete after removing any $m$ elements but
fails completeness after removing any $n$ elements? Verified base cases:

- $(m=0, n=1)$: powers of 2 (sequence of powers of $2$ is complete; removing
  any $1$ element breaks completeness).
- $(m=1, n=2)$: Fibonacci sequence (`fib_1_robust` post-bugfix in PR #15981).

Axiom inventory: 1 remaining axiom encoding the open Erdős–Graham
conjecture itself (the case $m=2, n=3$ and beyond remains open in the
literature; van Doorn showed nonexistence in the strong-completeness
reading, but Erdős–Graham likely meant the weak-completeness variant).

Axiom reduction history: 8 → 3 (PR #7461 + #7438) → 2 (PR #7512
`fib_not_2_robust`) → 1 (PR #4899 Fibonacci monotonicity).

## Active Approach

None — registry-graduated as the formalization deliverable. The
underlying $(m=2, n=3)$ question is upstream open mathematics, not
actionable from this slug without new combinatorial input.

## Blockers

- Resolving the $(m=2, n=3)$ case requires either a complete sequence
  exhibiting the gap or a proof that no such sequence exists in the
  weak-completeness sense.
- van Doorn's nonexistence result holds only under the strong-
  completeness definition (`∑_{B ⊂ A finite} B = ℕ` exactly); the
  weak variant (allowing finitely many exceptions) is open.

## Cross-References

- Gallery: `src/data/proofs/erdos-348/` (canonical: 1 axiom, 570 lines,
  18 theorems, 14 definitions, 0 sorries, status `axiomatized`, badge
  `axiom`)
- Lean: `proofs/Proofs/Erdos348Problem.lean`
- Predecessors: PR #2244 (initial stub), PR #4899 (Fibonacci monotonicity
  axiom elimination), PR #7438 (12 sorries proved across 3 problems),
  PR #7461 (axiom 11→10 reduction wave including erdos-348), PR #7512
  (`fib_not_2_robust`, 3→2 axioms), PR #7852 (proof improvements),
  PR #15981 (necessary conditions + `fib_1_robust` bug fix).
- Related Erdős problems: #347, #349 (immediate neighbors); #1, #2,
  #39, #83, #888, #1998, #2000 (problem.md tag list).

## Re-Open Trigger

If a literature result or new combinatorial construction settles the
$(m=2, n=3)$ case under weak completeness, this slug can be re-opened
to add a new axiom (or theorem) and strengthen the deliverable to a
resolution.

## Attempt Counts

- Total attempts: 2 (1 prior research arc culminating in graduation +
  this STATE-SYNC catchup)
- Approaches tried: 1 (base-case formalization + axiom reduction)
