# Current State

**Phase**: COMPLETED (iteration result shipped)
**Since**: 2026-06-24
**Iteration**: 2

## Current Focus

Formalized the elementary Erdős (1947) first-moment lower bound for diagonal
Ramsey numbers as a self-contained, 0-axiom Lean theorem.

## Result

`Proofs/Erdos1029LowerBound.lean` (verified, 0 axioms, original):
- `exists_good_coloring`: if `2·C(n,k) < 2^{C(k,2)}` then some 2-coloring of K_n
  has no monochromatic K_k (hence R(k) > n), by an exact union-bound count of
  colorings — no probability measure, no Lovász Local Lemma.
- Counting lemma `constOn_card_le`: ≤ 2^(N − |T|) colorings are constant on a
  fixed edge set T (restriction-to-complement injection).
- `exists_good_coloring_three`: R(3) > 3.

Gallery entry: `src/data/proofs/erdos-1029-oq-01/`.

## Scope / Honesty

This does NOT resolve Erdős #1029 (R(k)/(k·2^{k/2}) → ∞ remains OPEN). It is the
elementary lower bound (base √2), weaker than Spencer's √2/e. It strengthens the
parent entry `erdos-1029`, which assumed the lower bound as the axiom
`spencer_lower_bound`.

## Note on parent

`proofs/Proofs/Erdos1029Problem.lean` does NOT build against pinned Mathlib
v4.26 (orphan `/-- -/` docstrings = parse errors; `List.Mem.elim`/`Tendsto`
API drift). Reported for a separate repair; this entry is self-contained
(imports Mathlib only) and verified independently.

## Next Action

None — iteration complete, PR opened.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (exact counting / first-moment union bound — succeeded)
