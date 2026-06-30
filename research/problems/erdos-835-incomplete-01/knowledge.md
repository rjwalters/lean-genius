
## Session 2026-06-22 (researcher-1) — INTEGRATION FIX (orphaned from build)

**Mode**: REVISIT (pool re-served already-completed slug). **Outcome**: progress
(integrity fix, no new math).

### Finding
researcher-9's PR #27684 created `proofs/Proofs/Erdos835Incomplete01.lean` (verified,
0-axiom: erdosRosenfeld_surjective etc.) and a gallery `meta.json`, but the Lean file was
**never registered in `proofs/Proofs.lean`** (only `Erdos835Problem` was) — so it was not
part of the build and its verified claim went unchecked by CI. Same orphan pattern as
erdos-11-wip-01 (PR #27788) this session.

### What I Did
- Registered `import Proofs.Erdos835Incomplete01` in `proofs/Proofs.lean` (LC_ALL=C sorted:
  before `Erdos835Problem`, since 'I' < 'P').
- Verified via host single-file `lean` (Docker down): EXIT=0; `#print axioms
  erdosRosenfeld_surjective` = [propext, Classical.choice, Quot.sound] only — 0-axiom.

### Next Steps
- Erdős #835 main question is SOLVED (answer NO, 3≤k≤8); the scaffold's two sorries
  (chromatic-number def + k=2 construction) remain in `Erdos835Problem.lean`, not this file.

## Session 2026-06-23 (researcher-3) — REVISIT: repaired sibling scaffold

**Mode**: REVISIT (pool re-served completed slug). **Outcome**: progress —
fixed the broken sibling file `Erdos835Problem.lean` (gallery slug `erdos-835`)
and proved its k=2 case.

### Finding
`proofs/Proofs/Erdos835Problem.lean` was **registered in `Proofs.lean` but did
not compile** — a build-integrity hole. Errors: baseSet embedding `by intro; omega`
failed, `JohnsonGraph.loopless` unprovable for k=0 (johnsonAdj had no S≠T clause),
`chromaticNumber`'s `Nat.find` lacked `DecidablePred`, three orphan `/--` doc
comments (parse errors), and `interval_cases`/`fin_cases` unavailable under the
narrow import set. Gallery meta (`erdos-835`) recorded 2 sorries.

### What I Did
- `import Mathlib` (was three narrow modules; tactics now resolve).
- baseSet embedding → `add_left_injective 1`.
- `johnsonAdj` now requires `S.val ≠ T.val` (irreflexive for all k) → loopless trivial.
- Added `kSubsetsFintype` instance (via `Fintype.subtype` over `powersetCard`),
  letting `chromaticNumber` use `colorable_of_fintype` as the `Nat.find` witness
  (replaces the def-sorry); wrapped in `classical` for `DecidablePred`.
- **Proved `k_equals_2`** (was a sorry with a mathematically-wrong constant-0
  colouring): perfect-matching 3-colouring of K₄; enumerate the four 3-subsets via
  `powersetCard` + `fin_cases`, discharge each colour by `decide`.
- Kept the 6 computational axioms (k=3..8 — χ(J(2k,k))>k+1, out of kernel reach).
- Updated `src/data/proofs/erdos-835/{meta.json,annotations.json}`: sorries 2→0,
  lineCount 177→212, defs 10→11, realigned 21 annotations, fixed assumptions text.

### Result
`Erdos835Problem.lean` compiles clean (EXIT 0); `#print axioms k_equals_2` /
`chromaticNumber` = standard triple only (kernel `decide`, no ofReduceBool/sorryAx).
File status stays `axiomatized` (6 axioms) but now 0 sorries and actually builds.
