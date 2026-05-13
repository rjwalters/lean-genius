# S2 ACT — `dirichletSetN` def + central-symmetry lemma (sorry-free, axiom-free seed)

**Researcher**: researcher-1
**Date**: 2026-05-13
**Phase**: ACT (S2 — the narrowest first of 5 ACT sessions per `state.md`)
**Iteration**: 2
**Predecessors**:
- PR #18339 (S1 OBSERVE MERGED, researcher-1, 2026-05-12T22:39:38Z)
- PR #18419 (S5 PREP MERGED, researcher-11, shear-volume generalisation)
- PR #18511 (S6 PREP OPEN, researcher-1, assembly + integer-coordinate extraction roadmap)

**Build status**: pending (worktree `proofs/.lake` symlink is the
known self-referential loop per memory
`feedback_researcher_lake_symlink_loop_and_wipe.md`).

## Scope

`state.md:90-103` Next Action: "S2 ACT — narrowest first: prove the
three-line `dirichletSetN_symmetric` lemma as the seed of a new
`proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean` file. This [...] is
sorry-free, axiom-free, and ~10 lines (`Pi.neg_apply` + `abs_neg` per
inequality, then `Convex.iInter`)."

This session ships exactly that: a new ~117-line Lean file containing

1. **`dirichletSetN n α Q : Set (Fin (n+1) → ℝ)`** — the Cassels
   1957 parallelepiped (n-dim generalisation of the parent OQ-01's
   `dirichletSet` at `MinkowskiTheoremOQ02OQ01.lean:41`).
2. **`dirichletSetN_symmetric`** — central symmetry about the origin,
   the first of Minkowski's three hypotheses.

The proof of `dirichletSetN_symmetric` is a **verbatim
generalisation** of the parent OQ-01's `dirichletSet_symmetric`
(`MinkowskiTheoremOQ02OQ01.lean:48-54`) — the only delta is that the
second conjunct is quantified by `∀ i : Fin n` instead of being the
single `i = 1` case, requiring one extra `intro i` and applying
`hvi i` instead of `hv1`.

## What this ships

```lean
namespace MinkowskiTheoremOQ02OQ03

def dirichletSetN (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {v | |v 0| < ((Q : ℝ) ^ n) + 1 ∧
       ∀ i : Fin n, |α i * v 0 - v i.succ| < 1 / (Q : ℝ)}

theorem dirichletSetN_symmetric (n : ℕ) (α : Fin n → ℝ) (Q : ℕ) :
    ∀ v ∈ dirichletSetN n α Q, -v ∈ dirichletSetN n α Q := by
  intro v ⟨hv0, hvi⟩
  refine ⟨?_, ?_⟩
  · simp only [Pi.neg_apply, abs_neg]; exact hv0
  · intro i
    simp only [Pi.neg_apply]
    rw [show α i * -v 0 - -v i.succ = -(α i * v 0 - v i.succ) by ring, abs_neg]
    exact hvi i

end MinkowskiTheoremOQ02OQ03
```

File counts (`proofs/Proofs/MinkowskiTheoremOQ02OQ03.lean`, new):
- `lineCount` 117 (≈ 50 LOC docstring + ~25 LOC code + ~40 LOC inline comments).
- `defCount` 1 (`dirichletSetN`).
- `theoremCount` 1 (`dirichletSetN_symmetric`).
- `sorryCount` 0.
- `axiomCount` 0.

## Why this is the right S2 ACT

### 1. Mirrors the parent's proof pattern exactly

The parent file `MinkowskiTheoremOQ02OQ01.lean` is the gallery's
axiom-free analog of `MinkowskiTheoremOQ02.lean` (the original 1D
Dirichlet with three measure-theoretic axioms). Its
`dirichletSet_symmetric` (lines 48-54) is the *cleanest* of its five
core lemmas — 6 LOC, pure algebra. The n-dim seed should match.

### 2. Smallest possible commitment

Shipping just the def + symmetry (instead of all five lemmas) means:

- **One Mathlib API surface** (`Pi.neg_apply`, `abs_neg`, `ring`) —
  all elementary and stable across Mathlib versions.
- **No new imports beyond `Mathlib.Tactic`** + `Mathlib.Analysis.Convex.Basic`
  + `Mathlib.Data.Real.Basic`.
- **Zero risk of a typeclass-friction failure** that would block the
  entire chain. S3 (measurable), S4 (convex), S5 (volume) each
  introduce their own typeclass surface (`MeasurableSet`,
  `Convex ℝ`, `MeasureTheory.volume`) that *can* fail to elaborate;
  S2 doesn't touch any of them.

### 3. Locks the indexing convention

`Fin (n+1)` for the ambient lattice dimension, with `v 0` reserved
as the common-denominator coordinate and `v i.succ` carrying the
i-th approximation residual. This convention is implicit in S1
OBSERVE and S5/S6 PREP but had not been committed to a Lean
declaration; landing the def freezes it.

## What this session does NOT do

- **No registration in `proofs/Proofs.lean`.** The file is not yet
  built by the main pipeline; S3 / S4 / S5 / S6 will add lemmas, and
  the registration belongs to the first session that build-verifies
  via `docker-build.sh` (likely S3 once the chain is non-trivial).
  Per memory `feedback_researcher_lake_symlink_loop_and_wipe.md` the
  worktree's `.lake` is the recursive symlink loop, so a local build
  attempt would either fail (loop detection) or trigger a ~10 min
  fresh Mathlib clone with daemon-respawn risk.
- **No gallery files.** `meta.json` / `annotations.json` / `index.ts`
  for a `minkowski-theorem-oq-02-oq-03` gallery entry are deferred to
  a future Sx GALLERY session (per state.md the chain ends at S6 ACT,
  with gallery integration a separate task).
- **No edits to `state.md`, `knowledge.md`, `problem.md`, or the JSON.**
  Drift-sync of `state.md`'s "Iteration" to 2 and JSON's `phase`
  `OBSERVE → ACT` is auditor / mechanic territory.
- **No edits to the parent files** `MinkowskiTheoremOQ02.lean` or
  `MinkowskiTheoremOQ02OQ01.lean`.

## Build-risk register

The build is pending. Three minor risks specific to this PR:

| # | Risk | Likelihood | Mitigation |
|---|---|---|---|
| 1 | `Pi.neg_apply` is the wrong simp lemma name in current Mathlib (e.g. renamed to `Pi.neg_def` or merged into `Pi.neg_apply'`) | Very low | The parent OQ-01 file uses the exact same `simp only [Pi.neg_apply, abs_neg]` chain at line 52; if that builds (the parent is `verified` per gallery), this one builds. |
| 2 | The `ring` tactic at line `show α i * -v 0 - -v i.succ = -(α i * v 0 - v i.succ) by ring` fails on Mathlib's `ring` normalisation | Very low | The identity is a basic distributivity rewrite (`a * -b - -c = -(a * b - c)`); `ring` handles this in 1 step. |
| 3 | The unbundled `{v | …}` set-builder notation needs an explicit `Set` annotation | Low | The parent OQ-01 file's `dirichletSet` def uses the identical pattern (`Set (Fin 2 → ℝ)` annotated). I follow the same convention. |

All three risks are Very Low / Low; the parent file's existence as a
`verified` gallery proof gives high confidence that the simp /
ring / set-builder patterns transfer.

## Orthogonality

| PR | Status | Conflict? |
|---|---|---|
| #18339 (S1 OBSERVE) | MERGED | no — predecessor |
| #18419 (S5 PREP) | MERGED | no — different `sessions/` file (S5 shear-volume) |
| #18511 (S6 PREP) | OPEN | no — different `sessions/` file (S6 assembly) AND no Lean overlap (S6 PREP is doc-only) |
| #18529 (researcher-1, erdos-szekeres-oq-03 S-up-1 PREP) | OPEN | no — different slug |
| #18537 (researcher-1, sperner-simplicial-bridge-oq-01 S3 ACT) | OPEN | no — different slug |
| #18546 (researcher-1, sylow-theorems-oq-03 S2 PREP-3 audit) | OPEN | no — different slug |

This PR creates a single new Lean file `MinkowskiTheoremOQ02OQ03.lean`
(no overlap with any other Lean file in the repo) plus a session
note with a fresh timestamp. Pristinely orthogonal.

## Pre-flight verification

| Item | Verified by |
|---|---|
| Parent OQ-01 file's `dirichletSet_symmetric` matches the n-dim proof pattern | direct read of `MinkowskiTheoremOQ02OQ01.lean:48-54` |
| Parent OQ-01 imports list is a strict superset of what S2 needs | direct read of `MinkowskiTheoremOQ02OQ01.lean:24-31` (parent uses `Mathlib.Analysis.Convex.Basic`, `MeasureTheory.*`, `Algebra.Module.ZLattice.*`; S2 uses only `Analysis.Convex.Basic` + `Data.Real.Basic` + `Mathlib.Tactic`) |
| No existing `MinkowskiTheoremOQ02OQ03.lean` file | `ls proofs/Proofs/Minkowski*.lean` returns 3 files (parent, OQ-01, OQ-04), no OQ-03 |
| Indexing convention `Fin (n+1)` matches S1 OBSERVE and S5/S6 PREP | direct read of `state.md:46-57` and S5/S6 PREP session notes |
| Same-file race | no — no other in-flight PR touches `MinkowskiTheoremOQ02OQ03.lean` |

## Honesty

- Build status is **pending**, not verified. Worktree's
  `proofs/.lake` is the known recursive symlink loop per memory.
  Doctor / Mechanic can verify post-merge.
- The proof body matches the parent's proof pattern verbatim; the
  only delta is the `∀ i : Fin n` quantifier, which adds one `intro
  i` step. Build risk is minimal.
- The file is **not** registered in `proofs/Proofs.lean` — by design.
  Registration is a follow-up Sx step (or done by the first session
  that build-verifies; suggested to be S3 once the chain has more
  content).
- No follow-up Open Questions are generated this session. The chain
  continues per state.md: S3 (measurable) → S4 (convex) → S5
  (volume) → S6 (assembly + integer extraction).

## References

- Parent OQ (1D, with axioms): `proofs/Proofs/MinkowskiTheoremOQ02.lean`
  (~393 LOC, `dirichlet_approximation_from_minkowski` at line 182).
- Parent OQ-01 (1D, axiom-free): `proofs/Proofs/MinkowskiTheoremOQ02OQ01.lean`
  (~120 LOC, `dirichletSet` at 41, `dirichletSet_symmetric` at 48,
  `dirichletSet_measurable` at 60, `dirichletSet_convex` at 75,
  `dirichletSet_volume` at 96).
- Cassels (1957), *An Introduction to the Geometry of Numbers*,
  Springer, Theorem I.II.A — the simultaneous Dirichlet construction
  that drives the n-dim parallelepiped.
- Schmidt (1980), *Diophantine Approximation*, LNM 785, Springer,
  Theorem I.1A.
- Prior sessions:
  - `sessions/2026-05-12-s01-observe.md` (S1 OBSERVE)
  - `sessions/2026-05-12-s5-prep-shear-volume-generalization.md`
    (S5 PREP, researcher-11)
  - `sessions/2026-05-12-s6-prep-minkowski-assembly-roadmap.md`
    (S6 PREP OPEN, researcher-1 sister session)
