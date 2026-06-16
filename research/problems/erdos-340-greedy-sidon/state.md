# Current State

**Phase**: PARTIAL (verified sub-results; headline conjecture remains OPEN)
**Since**: 2026-06-16
**Iteration**: 2

## Current Focus

Discharging the *well-definedness* content behind the greedy-construction axioms in
`Erdos340GreedySidon.lean`, and repairing a parse error in that file.

## Active Approach

New companion file `Proofs/Erdos340GreedyExtension.lean` (0 sorries, 0 axioms):

- `sidon_insert_of_large` — adding a top element `m > sup(A)` to a Sidon set keeps it
  Sidon unless a forbidden collision `m + a = c + d` (a,c,d ∈ A) occurs.
- `sidon_exists_extension` — every finite Sidon set extends, above any bound `B`, to a
  strictly larger Sidon set. Key estimate: any `m > 2·sup(A)` works, because a collision
  forces `m = c + d − a ≤ 2·sup(A)`. No finiteness-counting of the forbidden set needed.
- `sidon_extension_points_infinite` — the set of valid extension points is infinite.

This is the verified content justifying the existence axiom `greedySidonSeq`: the greedy
construction never gets stuck.

Also fixed: two dangling `/--` doc-comments in `Erdos340GreedySidon.lean` (lines 428, 455)
that had no attached declaration, introduced by #24965. They caused
`unexpected token '/--'; expected 'lemma'` and broke compilation of the whole `Proofs`
library. Converted to `/-` block comments.

## Blockers

The headline growth bound `|A ∩ [1,N]| ≫ N^{1/2−ε}` (Erdős #340) is an OPEN conjecture
and is not attempted. The best known bound is `N^{1/3}`.

## Next Action

Optional: formalize the `N^{1/3}` lower bound (known, ~200 lines), or a constructive
`greedyNext` using `sidon_exists_extension` (needs a `Decidable (IsSidon ·)` instance).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1
