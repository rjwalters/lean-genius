# State: pascals-hexagon-oq-03-incomplete-01

## Current Phase: ORIENT
## Iteration: 1

## Status
Claimed by researcher-4 on 2026-06-25 (S1). Mathematical analysis of
**OQ-03-OQ-02** (`pascalLine` well-definedness) complete and verified by hand;
Lean implementation **proposed but not machine-checked** — local build
unusable this session (Docker wrapper down; host disk 99% full; dependency
oleans corrupted by a `cache unpack`/`get` onto the full disk, `leantar`
failing).

## What was established
- Exact dihedral-generator action on the Pascal triple `(P,Q,R)`:
  - `hexRot: (P,Q,R) ↦ (Q, R, −P)`
  - `hexRev: (P,Q,R) ↦ (−Q, −P, R)`
  (signs from `cross_anticomm`; derivation in the session note).
- Consequence: the spanned projective Pascal line is `D₆`-invariant, so
  `pascalLine` descends to `HexagonLabeling` — the content of OQ-03-OQ-02.
- Proposed total definition of `pascalLine` via `Quotient.out'` (discharges the
  blocking definition-`sorry`) plus the six generator-action lemmas. The four
  sign-free / single-`cross_anticomm` cases have full proposed proofs; the three
  `hexRev` sign cases are sketched (coordinate `cross_apply` + `ring`).

## Next Action
On a host with a working build (Docker back up, or disk freed):
1. Apply the proposed edit to `proofs/Proofs/PascalsHexagonOQ03.lean`.
2. Compile via `./proofs/scripts/docker-build.sh Proofs.PascalsHexagonOQ03`;
   fix the three `hexRev` lemmas with the coordinate-`ring` tactic.
3. If green, the file drops from 3 `sorry` to 2 (only the genuinely-open
   `steiner_count_eq_20` / `kirkman_count_eq_60` remain), and the gallery
   meta.json for `pascals-hexagon-incomplete-01-oq-03` should be re-checked.

## Out of scope
`steiner_count_eq_20`, `kirkman_count_eq_60` — genuinely open (real projective
geometry + concurrence proofs over Conway–Ryba combinatorics).
