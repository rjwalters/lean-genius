
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

## Session 2026-06-30 (researcher-1) — ACT: added the UPPER half (proper colouring)

**Mode**: REVISIT (pool re-served the COMPLETED slug, MODERATE depth-first).
**Outcome**: progress — new math, VERIFIED 0-axiom green build.

### Finding
The file proved only the *lower* half of `property ⇔ χ(J(2k,k)) = k+1`
(surjectivity: no colour wasted). The complementary *upper* half — that the
property is a genuine **proper** colouring of the Johnson graph — was absent.
Also two stale issues: research-json `sorryCount` read 4 (actual 0, prose
mentions of "sorry"), and the docstring referenced a nonexistent theorem
`erdosRosenfeld_uses_all_colors` (actual name `erdosRosenfeld_range_univ`).

### What I Did
- Added `erdosRosenfeld_window_injective`: within any `(k+1)`-window `A`, χ is
  injective on the `k`-subsets of `A`. Lift χ to a total `φ` (junk default off
  the k-subsets); the property surjects the k-subsets of A onto `Fin(k+1)`, and
  `|A.powersetCard k| = C(k+1,k) = k+1 = |Fin(k+1)|`, so
  `Finset.injOn_of_surjOn_of_card_le` promotes surjection → injection.
- Added `erdosRosenfeld_proper`: adjacent k-subsets in J(2k,k) (`|S∩T| = k-1`,
  hence `|S∪T| = k+1` via `Finset.card_union_add_card_inter` + omega) sit in the
  common (k+1)-window `S∪T`, so window-injectivity forces distinct colours.
- Fixed the doc references; updated research-json + gallery meta/annotations
  (4→6 thm, 128→207 lines, sorryCount 4→0; +1 section, +1 annotation,
  realigned the 5 existing annotation line-ranges).

### Result
`docker-build.sh Proofs.Erdos835Incomplete01` green (7743 jobs).
`#print axioms` of both new theorems = [propext, Classical.choice, Quot.sound]
only (no sorryAx / ofReduceBool). File: 6 thm / 4 def / 0 sorry / 0 axiom.

### GOTCHA
After `rw [dif_pos h]` the goal `χ ⟨U.val, _⟩ = χ U` was *not* auto-closed by
rw's reducible-transparency rfl (Subtype proof-irrelevance needs default
transparency). Fix: `exact dif_pos ⟨U.2.1, U.2.2⟩` — `exact` checks defeq at
default transparency and closes it directly.

### Next Steps (unchanged, all hard)
- Repair scaffold `Erdos835Problem.lean` parse error; discharge chromaticNumber.
- Formalize the explicit k=2 colouring of J(4,2).
- Formalize computational χ(J(2k,k)) > k+1 for 3≤k≤8 (the 6 sibling axioms).
