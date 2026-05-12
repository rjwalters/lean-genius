# Current State

**Phase**: OBSERVE (S1 — affirmative resolution + scaffold)
**Since**: 2026-05-12 (S1 OBSERVE iteration, researcher-12)
**Iteration**: 1

## Current Focus

S1 OBSERVE — first iteration on a fresh-slug `minpoly-charpoly-oq-01`
that the seeker added 2026-05-12T09:56:28Z. No prior work exists for
this OQ (the sibling `minpoly-charpoly-oq-03` has reached S2, and
provides a structural template; see `MinpolyCharpolyOQ03.lean`).

This iteration delivers:

1. **Affirmative strategy-level resolution.** Jordan normal form
   *can* be formalized in Lean 4 using the parent's minpoly/charpoly
   infrastructure plus three Mathlib ingredients (gen-eigenspace
   decomposition, gen-eigenspace internal direct sum, Jordan-Chevalley)
   — *modulo one Mathlib gap* (the nilpotent canonical form).
2. **Four-step roadmap** (sub-OQs OQ-01-OQ-01 through OQ-01-OQ-04)
   totalling ~930 lines.
3. **Lean scaffold** `Proofs/MinpolyCharpolyOQ01.lean` (228 lines, 1
   sorry, 4 theorems, 4 definitions/structures):
   * `JordanBlockShape` data structure
   * `jordanBlock R λ d` matrix definition (with two unconditional API
     lemmas: `jordanBlock_diag_eq`, `jordanBlock_super_diag_eq`)
   * `jordan_normal_form_exists` weak-form theorem statement (sorry-
     guarded)
   * `totalDim_empty` sanity lemma (unconditional)
4. **Gallery integration**: `src/data/research/problems/minpoly-charpoly-oq-01.json`
   and manifest import in `proofs/Proofs.lean`.

## Active Approach

Three-stage assembly, each stage cleanly resolvable:

1. Apply Mathlib's `Module.End.iSup_genEigenspace_eq_top` to split
   `V = ⨆_λ V_λ^∞` over the algebraically closed field `K`.
2. Promote the supremum to an internal direct sum via
   `Mathlib/LinearAlgebra/Eigenspace/Pi.lean` infrastructure.
3. On each `V_λ`, use `Module.End.exists_isNilpotent_isSemisimple`
   (Jordan-Chevalley) to split `f|_{V_λ} = λ · 1 + N_λ` (the semisimple
   part on a generalized eigenspace is `λ · 1`, the nilpotent part is
   `N_λ`).
4. Put `N_λ` into nilpotent-shift basis (**the Mathlib gap** — this is
   OQ-01-OQ-02). Standard textbook construction (Axler §8.D); ~400
   lines in Mathlib style.
5. Reassemble.

## Blockers

None at the strategy level. One *local* gap (the nilpotent canonical
form) is a self-contained classical proof, not a genuine obstacle.

## Sub-OQs Identified

* **OQ-01-OQ-01** — `jordanBlock` definition + basic API. ~80 lines.
* **OQ-01-OQ-02** — Jordan basis theorem for nilpotent operators on a
  finite-dim space. The load-bearing piece. ~400 lines.
* **OQ-01-OQ-03** — Per-eigenspace assembly: `f|_{V_λ}` similar to a
  direct sum of `jordanBlock K λ dᵢ`. ~250 lines.
* **OQ-01-OQ-04** — Global assembly: `f` similar to a direct sum of
  `jordanBlock`s across all eigenvalues. ~200 lines.

## Files Modified

* **Added**: `proofs/Proofs/MinpolyCharpolyOQ01.lean` (228 lines)
* **Added**: `research/problems/minpoly-charpoly-oq-01/problem.md`
* **Added**: `research/problems/minpoly-charpoly-oq-01/knowledge.md`
* **Added**: `research/problems/minpoly-charpoly-oq-01/state.md` (this)
* **Added**: `src/data/research/problems/minpoly-charpoly-oq-01.json`
* **Modified**: `proofs/Proofs.lean` (one new import line)

## Build Status

Not run locally. `proofs/.lake` is a recursive self-symlink in this
worktree (per
[`feedback_researcher_lake_symlink_broken.md`](../../../.claude/projects/-Users-rwalters-GitHub-lean-genius/memory/feedback_researcher_lake_symlink_broken.md)),
which forces a cold Mathlib clone (~30-45 min). Following the project
convention for S1 OBSERVE scaffolds with a single sorry on the main
theorem statement, CI is the ground truth.

The new file imports only:

* `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`
* `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly`
* `Mathlib.LinearAlgebra.Eigenspace.Triangularizable`
* `Mathlib.LinearAlgebra.JordanChevalley`
* `Mathlib.FieldTheory.IsAlgClosed.Basic`
* `Mathlib.Tactic`
* `Proofs.MinpolyCharpoly` (in-tree parent file, line 1 only — pure
  conceptual link via the docstring)

All Mathlib imports are stable Mathlib v4.26.0 modules with API in use
elsewhere in the gallery (e.g., `MinpolyCharpolyOQ03.lean`,
`CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean`).

## Next Action (S2+)

Pick the smallest sub-OQ first to land an unconditional contribution:

* **S2 candidate A** — Open child OQ `minpoly-charpoly-oq-01-oq-01`
  and scaffold `MinpolyCharpolyOQ01OQ01.lean` with the `jordanBlock`
  API: charpoly identity `(jordanBlock R λ d).charpoly = (X - C λ)^d`,
  minpoly identity, nilpotent-shift identity. ~80 lines, fully
  dischargable (no sorry).
* **S2 candidate B** — Upgrade the S1 weak-form
  `jordan_normal_form_exists` to the strong form (existence of an
  invertible `P`), still sorry-guarded but with the full statement
  surfaced. ~5-line statement edit.
* **S2 candidate C** — Begin OQ-01-OQ-02 (the nilpotent canonical
  form). Largest piece (~400 lines); needs the most preparation.

Recommend candidate A: smallest, fully dischargable, makes
unconditional Lean-level progress in S2.

## Coordination Notes

* No prior PR or branch exists for this OQ (verified via
  `gh pr list --search "minpoly-charpoly-oq-01" --state all` and
  `git branch -r | grep minpoly-charpoly-oq-01`, 2026-05-12T10:00 UTC).
* Sibling OQ-03 has an active scaffold in
  `Proofs/MinpolyCharpolyOQ03.lean` (S2, researcher-10, 2026-05-12);
  this OQ-01 scaffold mirrors its structure for cross-OQ consistency.

## Pool Status Note

This slug should advance from `available` → `in-progress` upon
PR creation; the claim was placed via `claim-random` in the
`MODERATE+`-tier saturation phase (3 contested probes; fell back to
direct tier-B selection — `minpoly-charpoly-oq-01` was a fresh tier-B
slug with 0 open PRs and 0 recent merges).
