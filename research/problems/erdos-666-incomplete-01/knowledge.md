# Knowledge: erdos-666-incomplete-01

## Overview

Initial knowledge for problem `erdos-666-incomplete-01`.

## Gallery Proof Summary

- Gallery: `erdos-666` — Erdős Problem #666: C₆ in Hypercube Subgraphs
- Sorries: 1, Axioms: 1
- Tags: erdos, graph-theory, hypercube, cycles, extremal-graph-theory, disproved

## Known Results

(To be populated during OBSERVE phase)

## Key References

- Gallery: `src/data/proofs/erdos-666/`
- Lean source: `proofs/Proofs/` (check namespace `Erdos666`)

## Session (researcher-2, 2026-07-08): interval refutation ε ≤ 1/4

**Mode**: REVISIT (MODERATE) · **Outcome**: progress (4 theorems VERIFIED, 0 new axioms),
branch research/erdos666-interval-refutation-r2

**Contribution — Part IV.5: refutation on the whole interval ε ≤ 1/4.** The axiom
`chung_no_threshold : ¬ConjectureAt (1/4)` only names the single density 1/4. Added
a density-monotonicity chain that extends the refutation to every ε ≤ 1/4 without any
new axiom:
- `epsilonDense_antitone` (unseal EpsilonDenseSubgraph): ε'≤ε ⇒ (ε-dense H ⇒ ε'-dense H),
  since `ε'·Eₙ ≤ ε·Eₙ ≤ #edges` (`Eₙ = n·2ⁿ⁻¹ ≥ 0`, `mul_le_mul_of_nonneg_right` +
  `le_trans`). One-liner term proof.
- `denseForcesC6_mono` / `conjectureAt_mono`: `DenseForcesC6` and `ConjectureAt` are
  monotone in ε (ε-dense graphs are a subclass of ε'-dense ones; same threshold N).
- `chung_no_threshold_le : ε ≤ 1/4 → ¬ConjectureAt ε` — the headline: monotonicity would
  push a conjecture-at-ε up to 1/4, contradicting the axiom. So Erdős's conjecture fails
  robustly across the whole range (0, 1/4], not at an isolated point.

**File state:** 1 axiom (`chung_no_threshold`, genuinely deep — Chung's 4-partition, not
in Mathlib, NOT eliminable), 0 sorries. 326→368 lines.

**Gotcha:** a `/-- docstring -/` must come AFTER `unseal … in`, not before — a docstring
cannot attach to the `unseal` command (`unexpected token 'unseal'; expected 'lemma'`).
Match the existing `chung_c6free` order: `unseal … in` / `/-- … -/` / `theorem`.

**Remaining (unchanged):** `conder_better_bound` keeps a `True` placeholder for the
ε=1/3 density (needs Conder's 3-coloring = a new deep axiom); `GeneralizedConjecture`
(C_{2k}) open. Build: green attempt 1.

## Session 2026-07-09 (researcher-4) — Conder ε=1/3 sharpening, axiom count held at 1

**Mode**: REVISIT (MODERATE) · **Outcome**: progress (VERIFIED 0 sorry / 1 axiom,
host `lake env lean` EXIT=0, `#print axioms` = propext/Classical.choice/Quot.sound +
`Erdos666.conder_no_threshold` only — no sorryAx).

### What I did
Replaced the vacuous `conder_better_bound` (a `True`-placeholder theorem whose
docstring *claimed* Conder's ε=1/3 improvement but proved nothing about density)
with the genuine, published result — **without raising the axiom count**:

1. **Axiomatized the STRONGER result.** `conder_no_threshold : ¬ ConjectureAt (1/3)`
   (Conder 1993's 3-edge-colouring, each class C₄,C₆-free ⇒ a (1/3)-dense C₆-free
   subgraph) is now the single deep axiom, replacing `chung_no_threshold`.
2. **Derived Chung from Conder.** `chung_no_threshold : ¬ConjectureAt (1/4)` is now a
   THEOREM: `fun h => conder_no_threshold (conjectureAt_mono (by norm_num : (1:ℝ)/4 ≤ 1/3) h)`.
   `#print axioms chung_no_threshold` confirms its only nonstd dep is
   `conder_no_threshold` (not itself). So axiom count stays **1** (swap 1/4→1/3,
   the stronger), and every downstream user of `chung_no_threshold` (erdos_conjecture_false,
   chung_no_threshold_le) is untouched.
3. **Sharp interval.** `conder_no_threshold_le : ε ≤ 1/3 → ¬ConjectureAt ε` extends the
   refutation to the whole (0, 1/3], strictly beyond researcher-2's (0, 1/4].
4. Renamed the placeholder `conder_better_bound` → honest `conder_counterexample`
   (existence witness only, no fake density claim). Moved the three monotonicity
   lemmas up (before the axiom) so `chung_no_threshold` can consume `conjectureAt_mono`.

### Files modified
- `proofs/Proofs/Erdos666Problem.lean` (368 → 413 lines; axiom 1→1 renamed, theorems 9→11).
- `src/data/proofs/erdos-666/meta.json` — leanFile counts, assumptions, proofStrategy
  (×2: .meta + .overview), section line-ranges remapped, conder section text.
- `src/data/proofs/erdos-666/annotations.json` — ann-666-chung (both now theorems),
  ann-666-conder-bound (real 1/3 content, range 323–354).

### Key findings / notes (reusable)
- **Axiom-count-neutral strengthening pattern**: when a file axiomatizes result A and a
  strictly stronger published result B implies A, axiomatize B and DERIVE A as a theorem.
  Net axioms unchanged, math strengthened, and (here) a `True` placeholder removed.
  Requires the monotonicity/implication lemma to be defined *before* the derived corollary.
- `#print axioms <derived>` is the honesty check: it must list the NEW axiom, proving the
  old name is genuinely derived, not silently re-axiomatized.
- **Fleet-race cache corruption** hammered every build this session: docker + host
  `lake env lean` failed on a DIFFERENT missing/invalid Mathlib olean/.ir each run
  (OpenPartialHomeomorph → aesop Index.ir → AddTorsor.Coord → Monoidal.Action.Opposites →
  Ring.Basic); one run even SIGSEGV'd (exit 139) with no error. Control test on the
  *original* file gave EXIT=0, and `lake exe cache get!` (force full re-download) then
  gave my file a clean EXIT=0 — the crashes were environment, not code. Verify with the
  ORIGINAL file as a control before blaming your edit.
- **Worktree-eater struck again** mid-`git commit`: `.loom/worktrees/researcher-4-2` was
  deleted, staged changes lost. RECOVERY: the edited Lean file survived in a `/tmp` copy
  made during verification; JSON edits were reconstructed from the session's jq commands.
  Lesson: keep a `/tmp` copy of the main edited file, and the branch ref survives worktree
  deletion (recreate with `git worktree add <path> <branch>`).

### Next steps (unchanged hard core)
- `GeneralizedConjecture` (C_{2k}) remains open — genuinely different (sparser
  c·n^{aₖ}·2ⁿ density), not a specialization of the C₆ refutation.
- Erdős's dense C₄,C₆-free ⇒ C₈ existence (moment/KST counting) — not session-sized,
  not in Mathlib. The elementary refutation theory is now essentially complete.
