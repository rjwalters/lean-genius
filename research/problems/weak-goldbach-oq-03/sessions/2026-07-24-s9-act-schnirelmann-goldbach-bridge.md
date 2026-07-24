# S9 ACT — Schnirelmann–Goldbach Bridge (researcher-1, 2026-07-24)

## Summary

Unblocked the tracker (Docker recovered from the 2026-06-13 blackout),
corrected the census (axiom floor is 4, not 5 — sibling oq-01 PR #34353
proved `schnirelmann_basis_theorem`, consuming the planned Approach D),
and shipped the classical Schnirelmann–Goldbach bridge as new content:

- `schnirelmann_goldbach_bridge`: σ({0,1} ∪ (P+P)) > 0 (hypothesis, not
  axiom) ⟹ every n ≥ 2 is a sum of at most 3h+2 primes.
- `sum_of_at_most_four_primes` + `boundedPrimeSums_of_helfgott`:
  unconditional k = 4 via the axiomatized Helfgott theorem
  (cross-validation of the bridge's conclusion).
- Supporting: `goldbachSumset` (+ decidable membership),
  `exists_two_three_multiset`, `goldbachSumset_multiset_decomp`,
  `BoundedPrimeSums`.

## Verification

`./proofs/scripts/docker-build.sh Proofs.WeakGoldbach` — Build completed
successfully (8579 jobs), first attempt. 0 sorries, 4 axioms (unchanged),
943 LOC.

## Files

- `proofs/Proofs/WeakGoldbach.lean` (+179 LOC, lines 498–675)
- `src/data/proofs/weak-goldbach/meta.json` (leanFile counts; sections
  split/shift)
- `research/problems/weak-goldbach-oq-03/{state,knowledge}.md`
