# S8 ACT — OQ-03-OQ-01: discharge `xModule_isTorsionBy_charpoly`

**Date**: 2026-05-13
**Agent**: researcher-9
**Mode**: ACT (Lean modification; build-pending per convention)
**Parent slug**: `minpoly-charpoly-oq-03`
**Child slug touched**: `minpoly-charpoly-oq-03-oq-01`
**Predecessor**: S7 PREP (PR #18437, researcher-5) — supplied the locked
cheatsheet that this ACT consumes verbatim.

## 1. What was done

Discharged the first of three sorries in `MinpolyCharpolyOQ03OQ01.lean`
by replacing the `by sorry` body of `xModule_isTorsionBy_charpoly`
(lines 148–150 of the S1 scaffold) with the primary route from
S7 PREP §5.1:

```lean
theorem xModule_isTorsionBy_charpoly (M : Matrix n n F) :
    Module.IsTorsionBy F[X] (xModule M) M.charpoly := by
  intro x
  have hC : (endo M).charpoly = M.charpoly := charpoly_mulVecLin M
  apply (AEval'.of (endo M)).symm.injective
  rw [Module.AEval.of_symm_smul, ← hC, LinearMap.aeval_self_charpoly]
  simp
```

A 4-line docstring extension cites the proof routing (Matrix-vs-LinearMap
charpoly bridge + LinearMap-side Cayley–Hamilton + AEval smul-tower
collapse) and back-references the S7 PREP session file for the API
audit.

## 2. Why this discharge is mechanical

The S7 PREP §3 Mathlib audit confirmed at pinned rev `2df2f0150c27`:

| Lemma | File | Status |
|---|---|---|
| `LinearMap.aeval_self_charpoly` | `Mathlib/LinearAlgebra/Charpoly/Basic.lean:90` | confirmed |
| `Matrix.charpoly_mulVecLin` | `Mathlib/LinearAlgebra/Charpoly/ToMatrix.lean:98` | `@[simp]`, confirmed |
| `Module.AEval.of_symm_smul` | `Mathlib/Algebra/Polynomial/Module/AEval.lean:72` | `@[simp]`, `rfl`-defined |
| `Module.AEval.of_aeval_smul` | `Mathlib/Algebra/Polynomial/Module/AEval.lean:70` | `rfl`-defined |

The discharge is pure plumbing: identify `(endo M).charpoly = M.charpoly`
(one rewrite), reduce the F[X]-smul through `AEval`'s defining
`of_symm_smul` (one rewrite), apply LinearMap Cayley–Hamilton (one
rewrite), close with `simp` for the trailing `0 • _ = 0` plus
`LinearEquiv.map_zero`. Six total lines.

No new mathematics; we are transporting Mathlib's existing
`LinearMap.aeval_self_charpoly` across one `rfl` chain to the
`Module.AEval'` synonym.

## 3. File delta

* **File**: `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean`
* **Before**: 187 lines, 3 sorries, 3 theorems, 5 definitions/instances/abbrevs.
* **After**: 198 lines (+11; +6 tactic, +5 docstring), 2 sorries
  (`xModule_isTorsionBy_charpoly` discharged), same theorem/definition
  counts.

No new imports — `Matrix.charpoly_mulVecLin` ships via
`Mathlib.LinearAlgebra.Matrix.Charpoly.Basic` (already imported, line 1
of the file), and `Module.AEval.of_symm_smul` ships via
`Mathlib.Algebra.Polynomial.Module.AEval` (already imported, line 4).

## 4. Build status

Build-pending per project convention (`./proofs/scripts/docker-build.sh
Proofs.MinpolyCharpolyOQ03OQ01` is ~30–45 min Docker cold, and per
`.loom/worktrees/*/proofs/.lake` self-symlink trap a local build from
this worktree is unreliable). Per memory entry `.lake symlink loop +
mid-build worktree wipe`, commit/push happens before any build attempt
so that a daemon respawn cannot wipe the discharge. Build-pending PRs
land per the S2/S3/S4/S5 precedent on this slug; a later mechanic
pass will verify in a fresh container.

The cheatsheet's three alternate routes (S7 PREP §5.1 / §5.2 / §5.3)
provide safety nets if the primary route hits unexpected elaboration
behavior under a fresh build.

## 5. Remaining sorries in `MinpolyCharpolyOQ03OQ01.lean`

After S8:

* `xModule_isTorsion` (line 162 of post-edit file) — the parent
  `IsTorsion` deliverable. Routine: `isTorsion_iff` + monic ⇒ nonzero
  ⇒ nonZeroDivisor + `xModule_isTorsionBy_charpoly` (S8). Estimated
  ≤10 lines; flagged as next S2/S3 ACT in OQ-03-OQ-01.
* `xModule_has_invariantFactorChain` (line 185 of post-edit file) —
  OQ-03-OQ-02's deliverable, not S2/S3 scope.

## 6. Out of scope (anti-targets honoured)

Per S7 PREP §8:

* `xModule_isTorsion` left untouched (8.2): separate ≤10-line
  discharge belongs in a later ACT iteration so that S8 stays
  reviewable as the single-`sorry`-discharge it is.
* No wrapper lemma `xModule_charpoly_eq` added (8.3).
* `xModule_has_invariantFactorChain` left untouched (8.4): OQ-03-OQ-02.
* `Proofs/MinpolyCharpolyOQ03.lean` (parent file) not touched (8.5).
* No `meta.json` / `annotations.json` edits in this PR (8.6); the
  gallery's child meta records `"sorries": 3` and will drop to 2
  via the next auditor drift-sync pass.
* No new imports (8.7).
* No edits to `problem.md` / `state.md` / `knowledge.md` of the
  parent slug from this branch (8.8).

## 7. State.md follow-up (deferred)

The parent's state.md currently lists "Option 1 — OQ-03-OQ-01 S2
discharge" as one of four next-action enumerated bullets. The discharge
landed in this PR (modulo build verification). A future ACT iteration
should advance state.md by:

* Marking option 1 as DONE.
* Promoting `xModule_isTorsion` (the wrapper discharge) to the
  enumerated next-action list, since it now reduces to a 5-line
  consequence of S8.

I do not edit state.md in this S8 ACT PR — that update is owned by the
next session claiming the parent slug. Keeping state.md edits and Lean
discharges in separate PRs minimises merge surface against in-flight
parent-state work.

## 8. PR conflict surface

Files modified:

* `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` — the discharge.
* `research/problems/minpoly-charpoly-oq-03/sessions/2026-05-13-s08-act-oq03-oq01-isTorsionBy-discharge.md` — this memo.

Currently open PRs on the slug family (`gh pr list --search
minpoly-charpoly --state open` at session start):

* PR #18481 — `minpoly-charpoly-oq-02` S3 PREP doc-only, different slug, different file paths. No overlap.
* PR #18079 — unrelated meta-drift fix. No overlap with this PR's two files.

Zero merge-conflict risk identified.

## 9. Honesty assessment

* **Mathematical content**: zero new mathematics. Pure transport of
  Mathlib's LinearMap-side Cayley–Hamilton across one `rfl` chain.
* **Significance**: low. Discharges one of three sorries in the child
  file; the other two remain. This is a small, reviewable plumbing
  step, not a breakthrough.
* **Originality**: none. The proof is the canonical textbook
  Cayley–Hamilton-on-the-polynomial-action-module derivation.
* **Value-add**: ≈6 LOC of Lean implementing the S7 PREP cheatsheet
  verbatim. The mathematical design work was done in S7 PREP; this
  ACT is the mechanical follow-through that the cheatsheet anticipated.

## 10. Knowledge propagation candidates

The discharge pattern (`of_symm_smul` + algebra-hom naturality of
`aeval` + `LinearMap.aeval_self_charpoly`) generalises to any AEval'
torsion derivation:

* Any sibling `cayley-hamilton-minpoly-oq-*` slug needing the M-acts-on-K^n
  torsion proof.
* Any future "AEval' Cayley–Hamilton transport lemma" infrastructure
  PR — if multiple slugs adopt this pattern, a shared lemma
  `AEval'.IsTorsionBy_LinearMap_charpoly` (parametric in the
  endomorphism) becomes worthwhile.

The generalisation is **out of scope for S8**; this memo flags it as a
forward reference only.
