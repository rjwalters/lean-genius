# Research State: erdos-szekeres-oq-01

## Current State
**Phase**: ACT (Approach B in progress) + S4 ORIENT note (Approach A surveyed 2026-06-13)
**Path**: full
**Since**: 2026-06-13 (S4 ORIENT, researcher-1; ACT-1 since 2026-06-10)
**Iteration**: 4 (S1 OBSERVE → S2 ACT-1 #22772 → S3 ACT-1 cont. → S4 ORIENT Approach-A survey)

## Current Focus
ACT-1 complete (S2, #22772): `maxIncLen`/`maxDecLen` defined via `Nat.findGreatest`
(Classical, noncomputable) plus singleton witnesses `hasIncreasingEndingAt_one` /
`hasDecreasingEndingAt_one` and lower bounds `one_le_maxIncLen` / `one_le_maxDecLen`
via `Nat.le_findGreatest` (commit f6642a8eeeb). Refactored
`HasIncreasingEndingAt`/`HasDecreasingEndingAt` positional disjunction to use
`j.val = len - 1` (fixes `Fin (len - 1 + 1)` vs `Fin len` type mismatch).
Docker 3058 jobs clean. File 281 → 344 LOC. Axiom count unchanged at 2.

## Active Approach
Assign each index `i` the pair `(a_i, b_i)` where `a_i = maxIncLen f i` is the
longest increasing-subsequence length ending at `i` and `b_i = maxDecLen f i` is
the longest decreasing one. If no increasing run of length `r` and no decreasing
run of length `s` exist, all pairs lie in the grid `(r-1) × (s-1)`; the pigeonhole
on an injective position→pair map yields the Erdős–Szekeres bound. The remaining
formal burden is the injectivity of that map.

## Alternative Approach (Approach A — surveyed S4, 2026-06-13, researcher-1)

Mathlib's **Archive** already *proves* Erdős–Szekeres: `Theorems100.erdos_szekeres`
in `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` (no axioms, same
pigeonhole-on-pairs argument). The Archive is importable here (precedent:
`proofs/Proofs/BallotProblem.lean` imports `Archive.Wiedijk100Theorems.BallotProblem`).

Discharge path: `import` the Archive theorem, instantiate with `α := Fin n`, `β := α`,
index shift `r ↦ r-1`, `s ↦ s-1` (makes the bound `(r-1)(s-1) < n` match the parent's
`n ≥ (r-1)(s-1)+1` exactly), then convert each `Finset (Fin n)` / `StrictMonoOn`
disjunct into the parent's `IncreasingSubseq` / `DecreasingSubseq` structure via
`Finset.orderEmbOfCardLe` + `StrictMonoOn.comp_strictMono`. See `problem.md` and
`knowledge.md` (S3/S4 ORIENT) for full detail.

This would discharge the axiom in ~30–50 LOC of plumbing, making Approach B's
bottom-up `maxIncLen`/`maxDecLen` scaffold unnecessary for the axiom-discharge goal.
**Recommendation**: prototype Approach A before investing further ACT in Approach B.

## Attempt Count
- Total attempts: 2 (both Approach B, ACT-1)
- Current approach attempts: 2
- Approaches tried: 2 (B in progress; A surveyed, not yet attempted in Lean)

## Blockers
ACT (either approach) is build-gated on Docker availability (2026-06-13 blackout) for
verification; ORIENT/PREP only until restored.

## Next Action
**First** (recommended): ACT — prototype **Approach A**. Add
`import Archive.Wiedijk100Theorems.AscendingDescendingSequences` to
`proofs/Proofs/ErdosSzekeres.lean`, replace `erdos_szekeres_existence_axiom` with a
proved theorem per `knowledge.md` → "Recommended ACT plan for Approach A", then
`./proofs/scripts/docker-build.sh Proofs.ErdosSzekeres`. If the import or conversion
fails, fall back to **Approach B** ACT-2:

ACT-2 (Approach B fallback): Prove the key extension lemma `maxIncLen_lt_of_lt` — for
`i < j : Fin n` with `f i < f j`, `maxIncLen f i < maxIncLen f j`. Strategy: extract
witness `k : Fin L → Fin n` from `HasIncreasingEndingAt f i L`; define `k'` on
`Fin (L+1)` appending `j` after `k`'s end-position `i` (using the refactored predicate
requirement `j.val = L` for the last index); verify `StrictMono` positions and values,
then `Nat.le_findGreatest` gives `maxIncLen f j ≥ L+1`. Symmetric for `maxDecLen` under
`f j < f i`. Target +60–100 LOC.
