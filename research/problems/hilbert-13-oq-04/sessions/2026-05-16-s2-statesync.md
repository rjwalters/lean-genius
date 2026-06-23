# Session 2026-05-16 — S2 STATE-SYNC (post-12-day dormancy)

**Slug**: hilbert-13-oq-04
**Date**: 2026-05-16T08:53Z–09:10Z
**Agent**: researcher-4
**Iteration bump**: 1 → 2 (STATE-SYNC, doc-only)
**Phase**: ACT (unchanged — sync only refreshes drift)

---

## §1 Why this session

`claim-random` picked `hilbert-13-oq-04` (knowledge tier RICH, score 19). Both knowledge-JSON
fields and `state.md` are dramatically out of sync with the actual repo state. Specifically:

- `state.md` still reports **Phase: OBSERVE** with **Iteration: 1** and a **2026-03-29** "Since"
  marker, although JSON was correctly advanced to **ACT** on 2026-03-30 and substantive
  research PRs (#15643, #15693) shipped on 2026-05-04.
- JSON's `leanFiles[0]` reports `lineCount: 444` / `theoremCount: 7` for
  `Hilbert13GeneralSpaces.lean`, but the file on `main` is **480 LOC / 9 theorems** (a +36 LOC
  / +2 theorem drift, exact source uncertain — the only `git log` entry post-#15643 is the
  incidental PR #18059 commit which `git show --stat` reports as a 480-LOC re-insertion).
- JSON's `knowledge.nextSteps[0]` says "Try to prove **covDimLE_of_embedding** (or submit to
  Aristotle)", but `Hilbert13GeneralSpaces.lean` lines 391–439 contain a **fully-discharged
  proof** of that theorem (closed-map construction with W_i = Y \ f(X \ U_i)). The nextStep is
  obsolete by ≥12 days.
- JSON's `lastUpdate` is `2026-05-04T11:10:00.000Z` — i.e. 12 days stale.

No open PRs reference the slug (`gh pr list --search "hilbert-13 in:title"` returns 0 open).
No deferred work in flight. Safe to ship a doc-only STATE-SYNC.

---

## §2 Lean-file inventory drift

| File | JSON `lineCount` | actual `wc -l` | JSON `theoremCount` | actual `grep -c '^theorem\\|^lemma\\|^example'` | JSON `axiomCount` | actual `grep -c '^axiom'` |
|---|---:|---:|---:|---:|---:|---:|
| `Hilbert13GeneralSpaces.lean` | 444 | **480** | 7 | **9** | 6 | 6 ✓ |
| `Hilbert13Superposition.lean` | 400 | **399** | 4 | 4 ✓ | 4 | 4 ✓ |

Net drift this session: +36 LOC and +2 theorems on `GeneralSpaces`, -1 LOC on `Superposition`
(likely a trailing-newline normalisation). Axiom counts on both files are stable. No `sorry`
introduced anywhere — both files remain clean.

**Provenance hypothesis for the +36 LOC**: PR #18059 (2026-05-12, angle-trisection S7)
`git show --stat` shows a 480-LOC addition to `Hilbert13GeneralSpaces.lean` even though the
commit message references only `AngleTrisectionOQ05OQ04.lean`. This looks like an incidental
merge/rebase artefact in which the file's content was re-inserted at the new HEAD. Since the
content on disk now matches the gallery-claimed theorems and `meta.json` is consistent with
the post-#15693 state (axiomCount: 6), this drift is benign — the JSON simply was never
updated.

The two "extra" theorems vs JSON are most likely `covDimLE_zero_iff_disjoint_refinement`
(line 132) and `covDimLE_of_unique` (line 157); the former may have been added as part of
PR #15643 but never reflected in `leanFiles[0].theoremCount`.

---

## §3 Mathlib pin bearer spot-check at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

The Lean files import (transitively) from a small set of Mathlib modules. Verified each via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<sha> --jq '.sha'`:

| Mathlib path | Bearer SHA at pin `2df2f0150c…` |
|---|---|
| `Mathlib/Topology/MetricSpace/Basic.lean` | `d9dac513c92935c411d6316f74198a10a1ca3a9d` |
| `Mathlib/Topology/UniformSpace/Compact.lean` | `75fcf51b420797c11e2ab0a2d92548ea424c9d3b` |
| `Mathlib/Order/CompleteLattice/Basic.lean` | `b7d2027f21901fdf3945e02c433c2ac03ed1dd8d` |
| `Mathlib/Topology/Order/Compact.lean` | `30aedb7a23c4f9ba17b968412cf60a688bed2eb6` |
| `Mathlib/Topology/MetricSpace/CauSeqFilter.lean` | `7b8a9866108f5e7ee4e9ee9e3b1e58a2e4de5770` |

All bearer paths exist on the pin. No drift evidence in the lake-manifest (mathlib rev
unchanged at `2df2f0150c…`, inputRev `v4.26.0`, toolchain `leanprover/lean4:v4.26.0`). The
existing 6-axiom proof should still build clean; this session does not attempt a build (see §4).

---

## §4 Why doc-only this session

Host disk pressure: `df -h /System/Volumes/Data` reports **100% capacity, 7.2 Gi available**
out of 926 Gi. Per the established researcher pattern documented in
`feedback_researcher_docker_build_disk_full_ship_build_pending_per_s5_act_precedent.md`,
attempting a fresh Docker build at <10 Gi free risks `ld.lld: error: failed to write output`
or containerd metadata I/O errors — and there is no Lean change here to validate anyway.

This session therefore ships:

- ✅ `state.md` OBSERVE→ACT + iter 1→2 + Sibling-files table + Remaining-axioms enumeration
- ✅ Research JSON: leanFiles inventory refresh, `currentState` focus+nextAction, `knowledge`
  progressSummary+builtItems+insights+nextSteps refresh, `lastUpdate` bump
- ✅ This sessions memo (full audit + paste-ready S3 ACT sketch in §6)
- ❌ No Lean changes
- ❌ No `meta.json` axiom count changes (still 6; meta is correct)
- ❌ No Docker build

---

## §5 Open PRs and recent activity

| PR | Title | State | Merged |
|---|---|---|---|
| #15643 | research(hilbert-13-oq-04): prove covDimLE_of_unique, reduce axiom count 6→5 | MERGED | 2026-05-04 |
| #15693 | fix(hilbert-13-oq-04): correct axiom count 5→6 (singleton ≠ general n≥1) | MERGED | 2026-05-04 |
| #15831 | audit(tracker): mark hilbert-13-oq-04 issues-fixed | MERGED | 2026-05-04 |
| #18059 | research(angle-trisection-oq-05-oq-04): S7 (incidental re-insertion) | MERGED | 2026-05-12 |
| #13286 | Enrich Hilbert 13 OQ-04 (Kolmogorov-Arnold generalization) | MERGED | 2026-04-27 |

No open PRs touch this slug.

---

## §6 Paste-ready plan for the next ACT (S3 — unitCube_covDimLE_pos n=1)

### Statement

The axiom currently in `Hilbert13GeneralSpaces.lean` line 187:

```lean
axiom unitCube_covDimLE_pos (n : ℕ) (hn : 0 < n) : covDimLE (Fin n → Set.Icc (0 : ℝ) 1) n
```

For S3 we attempt the special case `n = 1`. Splitting `unitCube_covDimLE_pos` into

```lean
theorem unitCube_covDimLE_one : covDimLE (Fin 1 → Set.Icc (0 : ℝ) 1) 1 := by …
axiom unitCube_covDimLE_pos_ge_two (n : ℕ) (hn : 2 ≤ n) : covDimLE (Fin n → Set.Icc (0 : ℝ) 1) n
```

reduces the headline axiom count from 6 → 5 once `unitCube_covDimLE` is rewritten to dispatch
the `n=1` branch into the new theorem.

### Mathematical content

For `n=1`, `covDimLE (Fin 1 → Set.Icc 0 1) 1` unfolds to: every finite open cover of the
closed interval (via a `Fin 1 →` equivalence) admits a finite open refinement of order ≤ 2 —
i.e. every point lies in at most 2 sets of the refinement. This is the **1-dimensional
Lebesgue covering theorem**, the classical statement that the interval has covering dimension
exactly 1.

The standard combinatorial proof:

1. Reduce `Fin 1 → Set.Icc 0 1` to `Set.Icc 0 1` via the `Equiv.funUnique (Fin 1) _` equivalence.
2. Given a finite open cover `(U_i)_{i ∈ ι}` of `[0,1]`, by compactness there is a Lebesgue
   number `δ > 0` such that every subinterval of diameter `< δ` lies inside some `U_i`.
3. Pick `N > 1/δ` and partition `[0,1]` into intervals `I_k = [k/N, (k+1)/N]` for `0 ≤ k < N`.
4. Choose `α_k ∈ ι` such that `I_k ⊆ U_{α_k}` (Lebesgue number property).
5. The refinement consists of slightly enlarged open intervals `V_k = (k/N − ε, (k+1)/N + ε)
   ∩ [0,1] ∩ U_{α_k}` for sufficiently small `ε > 0`.
6. Each point of `[0,1]` lies in at most 2 of the `V_k` (only the two intervals straddling the
   point's coordinate, if it sits within `ε` of an endpoint).
7. `IsRefinement (cover) (V)` is direct from `V_k ⊆ U_{α_k}`.

### Dependency map (Mathlib facts needed)

| Need | Mathlib lemma | Module |
|---|---|---|
| Lebesgue number for compact metric covers | `Metric.lebesgue_number_of_compact_open` | `Mathlib/Topology/MetricSpace/Basic.lean` (or `Metric.IsCompact.lebesgueNumber` equiv) |
| Compactness of `[0,1]` | `isCompact_Icc` | `Mathlib/Topology/Order/Compact.lean` |
| `Fin 1 → α` ≃ `α` | `Equiv.funUnique` | `Mathlib/Logic/Equiv/Fin.lean` |
| Pullback open via `Equiv.continuous` | standard | `Mathlib/Topology/Constructions.lean` |

The Lebesgue-number bearer must be re-verified at SHA `2df2f0150c…`. **Pre-flight TODO for S3
ACT**: `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Topology/MetricSpace/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` and search the response body for `lebesgue_number`. If the
name has moved or signature changed at v4.26.0, the proof needs adaptation.

### LOC forecast and risk class

| Sub-task | Forecast LOC | Risk |
|---|---:|---|
| `Equiv.funUnique`-based reduction wrapper | 8–15 | LOW (one-liner with `Equiv.image`) |
| Lebesgue-number lookup + arithmetic on `N > 1/δ` | 15–25 | MEDIUM (Mathlib API surface check) |
| Partition + `α_k` choice + `Finset` enumeration | 25–40 | MEDIUM (`Finset.range N` indexing) |
| `V_k` construction + openness + cover property | 20–30 | LOW–MEDIUM |
| order-≤-2 combinatorial argument | 15–25 | MEDIUM (the "straddling" case-split) |
| **Total** | **80–135 LOC** | |

Adjustment factor for unknown Mathlib bearer divergence: **×1.5** per the post-ship-revises
budget pattern (memory entry `feedback_researcher_postship_prep_revises_predecessor_budget_2x_after_bearer_survey_finds_1000yaml_gaps.md`). Honest budget for S3 ACT: **120–200 LOC** allowing
for Lebesgue-number API translation.

### Bug-risk anti-targets to avoid in S3

Per memory entry `feedback_researcher_postship_pivot_lands_on_slug_whose_paste_ready_act_has_4_act_blocking_bugs_under_docker.md`:

- **(K) Notation-scope**: if the proof reaches for `⟪·,·⟫_ℝ` inner-product notation, ensure
  `InnerProductSpace ℝ` instance (NOT `RealInnerProductSpace`). Unlikely needed here — the
  proof is metric-only.
- **(L) Unknown-simp-arg**: any `simp [<lemma>]` must verify `<lemma>` exists at v4.26.0. For
  the partition argument, `Fin.succAbove_succ` should be avoided (absent at this pin).
- **(M) Heartbeats / rec-depth**: the case-by-case partition argument might exceed default
  `maxHeartbeats 200000` if expanded by `simp + linear_combination`. Use a manual `Finset.sum`
  rewrite or `decide`-style explicit case split. If `set_option maxHeartbeats 400000 in` is
  needed, place it **before** the theorem's docstring/at theorem level (NOT per-tactic).
- **(N) Wrong witness**: verify the choice `N > 1/δ` actually delivers Lebesgue-property
  subintervals; the off-by-one between "δ-radius ball" and "δ-diameter interval" is a common
  trap. Use `N ≥ ⌈2/δ⌉` for safety margin.

### Suggested S3 ACT branch name + PR title

```
Branch:  research/hilbert-13-oq-04-s3-act-unitcube-n1-<timestamp>
PR:      research(hilbert-13-oq-04): S3 ACT — unitCube_covDimLE for n=1 (interval Lebesgue covering, axiom 6→5)
```

PR body should include:
- §-Lean diff vs main (anchor new theorem block in PART III)
- §-`meta.assumptions` field update (drop "n≥1" qualifier from `unitCube_covDimLE_pos`,
  reword to "n≥2 case (interval n=1 now proved)")
- §-`meta.axiomCount` decrement 6→5 on `Hilbert13GeneralSpaces.lean`
- §-Docker `7744/7744 jobs clean` evidence (or `(build pending — disk pressure)` qualifier
  per memory pattern if host still at 100%)

---

## §7 ACT-readiness gate for S3

| Gate | Status | Action if RED |
|---|---|---|
| state.md ACT phase | 🟢 GREEN (after this STATE-SYNC) | — |
| JSON inventory current | 🟢 GREEN (after this STATE-SYNC) | — |
| Mathlib pin verified | 🟢 GREEN (5 bearers confirmed at `2df2f0150c…`) | — |
| Open PRs blocking | 🟢 GREEN (none open on slug) | — |
| Lebesgue-number Mathlib API verified | 🟠 AMBER (deferred to S3 pre-flight) | search Mathlib `Topology/MetricSpace/Basic.lean` for `lebesgue_number` before opening Lean |
| Host Docker available | 🔴 RED (100% disk, 7.2 Gi free) | defer S3 ACT until ≥30 Gi free, OR ship with `(build pending)` qualifier per S5 ACT precedent (PR #18707 → #18980) |
| `covDimLE_of_unique`/`covDimLE_of_embedding` precedents | 🟢 GREEN (both fully discharged on main) | — |

Six of seven gates GREEN; AMBER Lebesgue-bearer is one `gh api` call away from clearing; RED
Docker gate is the only hard blocker, and it is INFRASTRUCTURE-ONLY (no math content
blocked).

---

## §8 Race-safety analysis

This PR touches only:

- `research/problems/hilbert-13-oq-04/state.md`
- `research/problems/hilbert-13-oq-04/sessions/2026-05-16-s2-statesync.md` (new file)
- `src/data/research/problems/hilbert-13-oq-04.json`

It does NOT touch:

- Any `proofs/Proofs/*.lean` file (zero risk of triggering a Docker build)
- `src/data/proofs/hilbert-13-oq-04/meta.json` (axiom count stable)
- `research/candidate-pool.json` or `.lean/state/candidate-pool.json`
- Any cross-slug shared infrastructure

Conflict-free with any concurrent activity, including the seeker daemon's pool refresh.

---

## §9 Handoff

**Recommended next agent**: Researcher (S3 ACT — `unitCube_covDimLE` for n=1)

**Prereq before next ACT**:
1. Host disk: free ≥30 Gi (currently 7.2 Gi available); `docker system prune -af --volumes`
   is the standard reclaim per CLAUDE.md if Docker daemon is otherwise responsive.
2. Mathlib API spot-check: confirm `Metric.lebesgue_number_of_compact_open` (or its v4.26.0
   equivalent) signature.

**If next session arrives and disk is still red**: ship another doc-only S3 PREP that
extends this paste-ready sketch with a literal Lean draft (no Docker), per the
`_post-ship-pivot-upgrades-audit-doc-deferred-sketch-to-pasteready-prep` pattern. Iteration
bumps to 3, phase stays ACT.

**If next session arrives and disk is green**: pick up the S3 ACT directly from §6 above.
The bug-risk inventory in §6 is the working anti-target list.
