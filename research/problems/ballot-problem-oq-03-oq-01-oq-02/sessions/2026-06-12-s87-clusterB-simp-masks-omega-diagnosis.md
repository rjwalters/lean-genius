# Session 87 — DIAGNOSE: the 3 Cluster B `simp only [splitPosAt] at ki kj` lines MASK 6 latent omega failures (not dead code)

**Date**: 2026-06-12
**Researcher**: researcher-2
**Mode**: DIAGNOSE (experiment + revert; no code shipped)
**Base SHA**: `fa1c4d27aa8` (origin/main; includes S86 merge `e781c9fdcac`)
**File**: `Proofs/BallotProblemOQ03OQ02.lean` (2589 LOC, unchanged — experiment reverted)

## §0. What this S87 tested

S86 (`state.md` §Session 86) left the S87 next-action:

> **S87 ACT** (recommended): Cluster B inner-body first 3 fixes — L2109/
> L2117/L2122. Each likely 1-2 LOC simp/rw/omega adjustment. Expected
> outcome: 20 → 17 visible.

Three of the 12 Cluster B errors are `` `simp` made no progress `` at
L2109, L2123, L2152 — all the identical line `simp only [splitPosAt] at
ki kj`. `splitPosAt` is a `noncomputable def` built by well-founded
recursion, so `simp` cannot unfold it; the line genuinely makes no
progress. The natural hypothesis: **these are dead no-op lines; deleting
them removes 3 errors (20 → 17) with no effect on the following tactics.**

This S87 **falsified** that hypothesis by experiment.

## §1. Experiment

Deleted all three `simp only [splitPosAt] at ki kj` lines (L2109, L2123,
L2152), leaving the `rcases … <;> omega` that immediately follows each.
Docker rebuild (`docker-build.sh Proofs.BallotProblemOQ03OQ02`, hot cache):

| | Before (baseline) | After deletion |
|---|---|---|
| `simp made no progress` errors | 3 | **0** ✓ |
| total source errors | 20 | **23** ✗ (+3 regression) |

The 3 `simp` errors vanished as expected, but **6 new `omega could not
prove the goal` errors appeared** — exactly 2 per deleted line, at the
`rcases hcol/hfinal with h | h <;> omega` that each `simp` line preceded:

* zero branch (`cases c | zero`): new omega ×2 at post-delete L2109:33
* succ branch (`cases c | succ c'`): new omega ×2 at post-delete L2122:33
* final-succ branch (`cases cfg.m | succ m'`): new omega ×2 at post-delete L2150:35

Net: 3 `simp` errors → 6 `omega` errors = **+3**. Reverted; baseline
restored to 20.

## §2. Root cause — why those omegas fail

The `simp … made no progress` error short-circuits Lean's elaboration of
the **rest of that tactic block**, so with the `simp` line present the
following `rcases … <;> omega` is never run and never reported. The
`simp` line is therefore **masking** 6 genuine omega failures — it is not
dead, it is load-bearing-by-accident (it suppresses worse errors).

The omega counterexample (zero branch, captured from the build log) shows
the real obstruction. omega's atoms include:

```
q := match c with | 0 => 0 | k.succ => northBeforeEast (List.take kj … ++ List.drop ki …) k
j := colEntry (↑(t.snd ci)) (c + 1)
n := northBeforeEast (List.take ki ↑(t.snd ci) ++ List.drop kj ↑(t.snd cj)) c
```

i.e. **`c` is still symbolic inside the `| zero =>` branch** — the `match
c` term is opaque (not reduced to `0`) and the `colEntry … (c+1)` /
`northBeforeEast … c` facts stay disconnected. `c` was introduced by
`set c := canonCol cfg hwf t hht` (L2048), so it is a let-/definition-
bound local; `cases c with | zero => …` does **not** substitute `c := 0`
into the surrounding hypotheses the way it would for a plain free
variable. omega thus sees `c` as an unconstrained nonneg integer and
cannot derive the contradiction the branch needs.

The `simp only [splitPosAt] at ki kj` was evidently an earlier attempt to
unblock this (unfold `ki`/`kj` so omega can relate them) — but it cannot
unfold `splitPosAt`, fails, and the failure incidentally hides the omega
gap.

## §3. Actionable next step for S88+

The correct fix is **not** to touch the `simp` lines in isolation; it is
to make the branch value of `c` (and `cfg.m` in the final column)
omega-visible so the `match c` term reduces and the `colEntry (c+1)`
facts connect. Candidate approaches (each needs one Docker build to
confirm):

1. **`clear_value c` before `cases c`** (and `clear_value`/equation for
   `cfg.m`) so `c` becomes a genuine free variable that `cases`
   substitutes (`c := 0` / `c := c'+1`) into all hypotheses, collapsing
   the opaque `match c` atom.
2. **Equation-carrying case split**: replace `cases c with` by
   `rcases Nat.eq_zero_or_pos c with hc0 | hcpos` / `obtain ⟨c', rfl⟩`,
   threading an explicit `c = 0` / `c = c'+1` hypothesis omega can use.
3. After whichever split, the three `simp only [splitPosAt] at ki kj`
   lines can then be **deleted** (they are still no-ops) — but only once
   the omega beneath each actually closes.

Once the `c`/`cfg.m` substitution is fixed, this should resolve the 3
`simp` errors **and** the 6 latent omegas together (Cluster B 12 → ~3,
modulo the L2116/L2121/L2143/L2148 `northBeforeEast_prefix` side-goal
omegas and the L2124/L2128/L2132 `No goals`/`split_ifs` errors, which are
separate Cluster B sub-failures with their own causes).

## §4. Honesty calibration

* No code shipped. The experiment was reverted; `BallotProblemOQ03OQ02.lean`
  is byte-identical to origin/main (`fa1c4d27aa8`).
* The "20 → 17" S86/S87 prediction is **wrong for the deletion-only
  approach**: deletion gives 20 → 23. The 3 `simp` errors and 6 omega
  errors are one coupled defect, not 3 independent dead lines.
* Counterexample/atom data in §2 is quoted verbatim from the S87 build
  log (zero-branch omega at L2109:33).
* An incidental process note: the first build attempt this session built
  an **unedited** copy because the edit landed in the main checkout
  rather than this worktree; corrected by re-applying in
  `.loom/worktrees/researcher-2/` and rebuilding. Result above is from
  the worktree build.

## §5. Ship scope

3 files (docs/tracker only, NO `.lean` change):

1. `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-06-12-s87-clusterB-simp-masks-omega-diagnosis.md` (new, this memo)
2. `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` (prepend Session 87 block)
3. `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` (currentState focus/phase/nextAction/iteration)

NO sibling slug edits. NO `leanFiles[]` numeric touches.
