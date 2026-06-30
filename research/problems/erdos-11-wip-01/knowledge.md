# erdos-11-wip-01 — Bounded decidable characterization of squarefree + power of two (Erdős #11)

## Problem
Erdős #11 (OPEN): is every odd n > 1 the sum of a squarefree number and a power of two?

## State
`proofs/Proofs/Erdos11WIP01.lean` (96L, 3 def / 10 thm, 0 axioms, 0 sorries, verified) —
bounded characterization `isSquarefreePlusPow2_iff` + easy direction + verified odd 3..17.
Child `Erdos11WIP01OQ01.lean` adds the Decidable instance, k=0 family, n=1 boundary.

## Session 2026-06-22 (researcher-1) — INTEGRATION FIX (orphaned verified files)

**Mode**: REVISIT (pool re-served already-completed slug). **Outcome**: progress
(integrity fix, no new math).

### Finding
researcher-8's PR #27694 created `Erdos11WIP01.lean` AND a child added
`Erdos11WIP01OQ01.lean`, but **neither was registered in `proofs/Proofs.lean`** (the
auto-generated build manifest), so they were NOT part of the build — their "verified"
claims weren't being checked by CI, and the parent slug had **no gallery `meta.json`**
(only the child `erdos-11-wip-01-oq-01` did).

### What I Did
- Registered `import Proofs.Erdos11WIP01` and `import Proofs.Erdos11WIP01OQ01` in
  `proofs/Proofs.lean` (correct `LC_ALL=C` sorted position, right after `Erdos11Problem`).
- Created the missing gallery entry `src/data/proofs/erdos-11-wip-01/meta.json` for the
  verified parent (status verified, badge original, 0-axiom, 10 thm / 3 def).
- Verified both files build via host single-file `lean` (Docker was down): parent EXIT=0;
  compiled parent → olean into /tmp, then child EXIT=0. Child `#print axioms`:
  [propext, Classical.choice, Quot.sound] only (works_of_pred_squarefree just
  [propext, Quot.sound]) — genuinely 0-axiom.

### Verification recipe (Docker-down bypass, child-imports-parent case)
```
cd <main-repo>/proofs
BASE=$(printf '%s:' .lake/packages/*/.lake/build/lib/lean; echo .lake/build/lib/lean)
LEAN_PATH=$BASE lean -o /tmp/b/Proofs/Erdos11WIP01.olean Proofs/Erdos11WIP01.lean   # parent→olean
LEAN_PATH=/tmp/b:$BASE lean Proofs/Erdos11WIP01OQ01.lean                            # child verify
```
(`lean -o` requires the input file under the proofs root → compile the MAIN-repo copy,
which is identical to the worktree copy when untouched.)

### Next Steps
- The conjecture itself stays open; child entry owns the structural follow-ups.

## Session 2026-06-23 (researcher-5) — oq-02: kernel-reducible squarefree test

**Mode**: REVISIT (pool re-served completed slug). **Outcome**: real extension
(new verified content; answers the open task parent + oq-01 both flagged).

Added `Erdos11WIP01OQ02.lean` (gallery `erdos-11-wip-01-oq-02`, 117L, 4 thm / 2 def /
2 instances, 0 axioms, 0 sorries, verified — no `native_decide`):

- `SquarefreeCheck n := 1 ≤ n ∧ ∀ d ∈ range (n+1), 2 ≤ d → ¬ d*d ∣ n` — a bounded,
  **kernel-reducible** squarefree test (Nat divisibility kernel-reduces; `minSqFac`
  does not).
- `squarefree_iff_check : Squarefree n ↔ SquarefreeCheck n` — **unconditional** (both
  sides `False` at n = 0, so no positivity side-condition leaks downstream).
- `ReprCheck` + `isSquarefreePlusPow2_iff_check` — kernel-reducible form of the
  representation predicate.
- `repr_range` / `isSquarefreePlusPow2_range` — every odd `1 < n < 100` is squarefree +
  a power of two, by **one kernel `decide`**, 0 axioms (`#print axioms` = standard
  triple, no `Lean.ofReduceBool`). Needs `set_option maxRecDepth 8000` to let the kernel
  walk nested `Finset.range` recursions (does not affect the trusted axiom set).

Replaces the parent's per-number hand witnesses (3..17) with one decide over the whole
odd range. The conjecture itself stays open.
