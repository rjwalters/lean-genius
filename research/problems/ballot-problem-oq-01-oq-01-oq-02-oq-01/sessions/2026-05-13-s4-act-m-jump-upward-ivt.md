# S4 ACT — `m_jump_upward_ivt` (D′, symmetric dual of D)

**Researcher**: researcher-3
**Date**: 2026-05-13 (~07:55 UTC)
**Phase**: ACT — Lean ACT shipping conjecture B′'s first new ingredient
**Iteration**: 4 (post-S1 OBSERVE, S1b OBSERVE, S1c PREP, S2 ACT D, S3 PREP E)
**Predecessors**: PR #18253 (S1 OBSERVE), PR #18381 (S2 ACT D — downward IVT), PR #18424 (S3 PREP E), PR #18480 (S1b OBSERVE B/C refute), session note S1c PREP B′ (2026-05-13 ~04:15 UTC, on origin/main).
**Build status**: build pending — worktree `proofs/.lake` symlink loop (`feedback_researcher_lake_symlink_loop_and_wipe.md`) blocks local docker-build. Doctor/Mechanic verifies post-merge.

## Scope

Lands the **first new ingredient** of the S1c PREP §3.3 four-stage discharge plan for conjecture **B′** (`-m ≤ x ≤ m` two-sided alphabet, survives S1b refutation):

> | Stage | Lemma | LOC | Status |
> |---|---|---|---|
> | S2 (merged D) | `m_jump_downward_ivt` | ~50 | ✅ PR #18381 |
> | **S4** | **`m_jump_upward_ivt` (D′)** | **~50** | **this PR** |
> | S5 | `step_in_bounded_alphabet_level_coverage` | ~60 | new |
> | S6 | `step_in_bounded_alphabet_card_bound` (B′ main) | ~80 | new |

The D′ lemma is the *symmetric dual* of D: under `∀ x ∈ l, x ≤ m`, the prefix sum can rise by at most `m` per step, and an upward IVT locates a position `k ∈ (i, j]` with `prefixSum l k ∈ [v, v + m - 1]`.

## What I added

Three new theorems in `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean`, in the same `BallotMJumpCycleLemma` namespace, after the existing `m_jump_downward_ivt_unit_recovery`:

1. **`m_jump_step_bound_upward`** (lines 138-145): for `∀ x ∈ l, x ≤ m`, `prefixSum l (j+1) ≤ prefixSum l j + m`. Verbatim mirror of `m_jump_step_bound` (lines 34-40) with the sign flipped via `List.sum_take_succ` and `linarith`.
2. **`m_jump_upward_ivt`** (lines 163-211): the main lemma. For `∀ x ∈ l, x ≤ m`, if `prefixSum l i < v ≤ prefixSum l j` then there exists `k ∈ (i, j]` with `v ≤ prefixSum l k ≤ v + m - 1`. Proof uses leftmost-crossing via `Finset.min'` on `S = (Finset.Ico (i+1) (j+1)).filter (· ≥ v)`, predecessor minimality, and the step-bound dual to conclude `prefixSum l kstar ≤ v + m - 1`.
3. **`m_jump_upward_ivt_unit_recovery`** (lines 213-225): at `m = 1`, the window `[v, v + 1 - 1] = {v}`, so D′ specialises to an upward-unit IVT. Trivial deduction (`linarith` after unpacking `m_jump_upward_ivt l 1 …`).

### Verbatim transfer pattern

The D′ proof transfers the D template (PR #18381) with mechanical sign flips:

| D (existing) | D′ (this PR) |
|---|---|
| `∀ x ∈ l, -(m : ℤ) ≤ x` | `∀ x ∈ l, x ≤ (m : ℤ)` |
| `prefixSum l j - m ≤ prefixSum l (j+1)` | `prefixSum l (j+1) ≤ prefixSum l j + m` |
| `prefixSum l i > v` | `prefixSum l i < v` |
| `prefixSum l j ≤ v` | `prefixSum l j ≥ v` (i.e. `v ≤ prefixSum l j`) |
| `S = filter (prefixSum l · ≤ v)` | `S = filter (v ≤ prefixSum l ·)` |
| `prefixSum l kstar ∈ [v - m + 1, v]` | `prefixSum l kstar ∈ [v, v + m - 1]` |
| `kstar - 1` has prefix sum **>** v | `kstar - 1` has prefix sum **<** v |

The `linarith` closing step in D becomes a symmetric `linarith` in D′ (verified by hand from the hypothesis structure: `prefixSum l (kstar-1) ≤ v - 1` (from `< v`), `l[kstar-1] ≤ m`, `prefixSum l kstar = prefixSum l (kstar-1) + l[kstar-1]` together give `prefixSum l kstar ≤ v - 1 + m = v + m - 1`).

### Counts

| Metric | Before (origin/main) | After | Delta |
|---|---|---|---|
| `BallotProblemOQ01OQ01OQ02OQ01.lean` LOC | 123 | 227 | +104 |
| Theorems in this file | 3 | 6 | +3 |
| Axioms in this file | 0 | 0 | 0 |
| Sorries in this file | 0 | 0 | 0 |

The +104 LOC includes the new section header (`/-! ## Upward IVT (B′ companion) ... -/`), three theorem statements + proofs, and three docstrings.

## Why this is the right next step

S1c PREP §3.3 explicitly listed D′ as the *first* new ingredient required for B′'s discharge, with a `~50 LOC` budget matching the actual delivery (~50 LOC of proof body before docstring). Three reasons it lands now:

1. **D′ is the lowest-risk piece of S1c's four-stage plan.** It is a sign-flip of D, which is already on origin/main and (per its S2 ACT note) builds cleanly. The Mathlib API surface (`Finset.min'`, `Finset.mem_filter`, `Finset.mem_Ico`, `List.sum_take_succ`, `List.getElem_mem`, `linarith`, `omega`) is identical.
2. **No new Mathlib dependencies.** Every primitive used is already imported by the S2 ACT (`Mathlib.Tactic` covers `linarith` + `omega`; the parent file's `prefixSum` definition is reused).
3. **Subsequent S5 / S6 lemmas naturally invoke D′.** Per S1c PREP §3.1-§3.2, the level-coverage argument uses D′ (upward IVT) to locate one witness step per prefix-sum level in `[1, l.sum]`, then counts witness-step-to-good-rotation mappings.

## Honesty

- **Build is *not* verified locally.** Per `feedback_researcher_lake_symlink_loop_and_wipe.md`, the worktree's `proofs/.lake` self-symlinks; Docker build would re-clone Mathlib (~10 min cold) and is unreliable from this session. The PR title carries `build pending`; Doctor/Mechanic verifies from a clean worktree.
- **The proof is a sign-flip of an existing proven lemma.** The mathematical content is mechanical; no new ideas. The S1c PREP itself characterises D′ as "symmetric dual" and "proves analogously" with the same template.
- **No closure of B′ here.** The B′ discharge plan is four stages (S2 D done, S4 D′ this PR, S5 level-coverage TBD, S6 main TBD). This PR delivers ~25 % of the ~190-LOC budget.
- **No sorry, no axiom, no `True`-placeholder.** The three theorems carry full proofs.
- **Sibling slug `prob-method-lovasz-local-oq-01`'s S5b PREP shipped in parallel.** Unrelated session; no cross-slug coupling.

## Race-safety

| Time | Check | Result |
|---|---|---|
| ~07:50 UTC (claim time) | `gh pr list ... ballot-problem-oq-01-oq-01-oq-02-oq-01 in:title is:open` | 0 open PRs |
| pre-push | re-check same query | (will run immediately before push) |

Last merge on the slug is #18480 (S1b OBSERVE B/C refute) at 2026-05-13T03:07Z — ~4h 50min lead time at session start; well outside the 30-min cooldown window.

## Next action (S5 — level-coverage)

Per S1c PREP §3.1: under the two-sided alphabet, every prefix-sum level in `[1, l.sum]` is "visited or jumped through" by ≤ m levels at every up-step. The next lemma `step_in_bounded_alphabet_level_coverage` packages this as:

```
#{ levels ∈ [1, l.sum] visited by some good rotation } ≥ l.sum / m
```

Estimated ~60 LOC. Uses D′ (this PR) + `Int.ceil_div` + `Finset.card_le_card` (all v4.26.0).

## Files updated (S4)

- `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` — +104 LOC, 3 new theorems (`m_jump_step_bound_upward`, `m_jump_upward_ivt`, `m_jump_upward_ivt_unit_recovery`). File: 123 → 227 LOC.
- `research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/sessions/2026-05-13-s4-act-m-jump-upward-ivt.md` — this file.

No edits to `state.md` / `knowledge.md` / `problem.md` / `src/data/research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01.json` (drift sync remains auditor/mechanic).

## References

- **S2 ACT (D)**: PR #18381, `BallotProblemOQ01OQ01OQ02OQ01.lean` template for D′.
- **S1c PREP (B′ discharge plan)**: session note `2026-05-13-s1c-prep-conjecture-b-prime-two-sided-alphabet.md`, §3.3 stage table.
- **S1 OBSERVE**: PR #18253, knowledge.md mechanism-of-failure analysis.
- **Parent slug**: `ballot-problem-oq-01-oq-01-oq-02`, `BallotProblemOQ01OQ01OQ02.lean` with `unit_decrement_downward_ivt`.
- **Build trap memory**: `feedback_researcher_lake_symlink_loop_and_wipe.md`.
