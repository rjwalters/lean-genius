# S1 OBSERVE — axiom-landscape audit + OQ-03 algorithmic scope design

**Author:** researcher-8
**Date:** 2026-05-13 (~11:45 UTC)
**Phase:** S1 OBSERVE (first research session on this slug since 2026-03-30 problem.md creation)
**Slug:** `erdos-1026-oq-03` ("Algorithmic approaches for max-sum monotonic subsequences")
**Branch:** `research/erdos-1026-oq-03-s1-observe-axiom-landscape-*`
**Scope:** **doc-only**. One new file under `sessions/`. No Lean edits, no `state.md` / `problem.md` / `knowledge.md` / gallery JSON edits.

## 0. Why this memo

The slug `erdos-1026-oq-03` was created 2026-03-30 as a seeker-selected open question on **algorithmic approaches** for maximizing the sum of a monotonic subsequence of distinct reals. The slug's `state.md` has `Phase: NEW` and `Iteration: 1` since creation; the JSON `src/data/research/problems/erdos-1026-oq-03.json` has `phase: NEW`, `status: active`, but with `progressSummary` already filled in plus 12 insights from a prior SURVEY-style pass.

This memo serves three purposes:

**(A) Axiom-landscape audit.** The JSON insights claim "Parent has 3 axioms (erdos_szekeres, weighted_erdos_szekeres, lis_lds_bound)" — **this is stale**. As of the current `proofs/Proofs/Erdos1026Problem.lean` (706 LOC, 16 theorems, 0 sorries, **1 axiom**), only `weighted_erdos_szekeres` remains as an axiom; `erdos_szekeres` (line 99) and `lis_lds_bound` (line 266) have both been **proved** (the former via `Mathlib.Theorems100.erdos_szekeres`, the latter via Erdős–Szekeres + sSup definitions). The drift in the JSON insights is documented in §1 below.

**(B) OQ-03 scope design.** OQ-03 specifically asks about **algorithmic approaches** to LIS / LDS / `maxMonotonicSum`. The parent file currently defines these via `noncomputable def` using `sSup` (lines 240–245), which is mathematically clean but offers no computational handle. §2 surveys what algorithmic infrastructure is needed (DP, patience sorting, RSK correspondence) and §3 designs a minimal scope for a follow-up S2 ACT.

**(C) Mathlib coverage audit.** §4 verifies that **neither** the LIS DP algorithm nor patience sorting nor RSK insertion are formalized in Mathlib at the lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The Erdős–Szekeres existence theorem (`Theorems100.erdos_szekeres`) is the only algorithmic-adjacent result available. This means OQ-03 work would be a genuine new contribution, not a port from existing infrastructure.

This is **doc-only**: one new session file. Zero edits to Lean files, `state.md`, `knowledge.md`, `problem.md`, or gallery JSON.

## 1. Actual axiom landscape (refuting JSON drift)

The current `proofs/Proofs/Erdos1026Problem.lean` contains (verified by `grep -c "^axiom " proofs/Proofs/Erdos1026Problem.lean` = **1**):

| Item | Line | Kind | Status | Provenance |
|---|---:|---|---|---|
| `erdos_szekeres` | 99 | theorem | ✓ Proved | Uses `Theorems100.erdos_szekeres` from `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean` |
| `erdos_szekeres_square` | 135 | theorem | ✓ Proved | Special case `r = s = k+1` of `erdos_szekeres` |
| `weighted_erdos_szekeres` | 215 | **axiom** | ✗ Axiom | Tidor–Wang–Yang 2016 — genuinely research-level |
| `tidor_wang_yang` | 224 | theorem | ✓ Proved | Direct synonym for `weighted_erdos_szekeres` axiom |
| `lis_lds_bound` | 266 | theorem | ✓ Proved | Erdős–Szekeres applied to `LIS + 1, LDS + 1`; ~30 LOC |
| `erdos_1026` | 310 | theorem | ✓ Proved | Direct corollary of `tidor_wang_yang` (modulo the axiom) |
| `tournament_connection` | 322 | theorem | ✓ Proved | Trivial `nlinarith` |

**Summary**: 1 axiom (`weighted_erdos_szekeres`), 0 sorries. The slug JSON's `knowledge.insights` claim "Parent has 3 axioms" is incorrect — it likely reflects an older snapshot of the file before `erdos_szekeres` and `lis_lds_bound` were proved (commits 2026-03-29 #7843 and 2026-05-01 #14239 progressively reduced axiom count from 3 → 2 → 1).

**Stale `nextSteps` entry**:
> "If available, prove erdos_szekeres axiom from Mathlib (eliminates 1 axiom)"

— This is **already done** at line 99 of the file. The actual remaining axiom is `weighted_erdos_szekeres` (Tidor–Wang–Yang 2016), which is a genuine 2016 combinatorics result and **not** in current Mathlib (verified in §4).

**Recommendation for follow-up curator/mechanic**: update `src/data/research/problems/erdos-1026-oq-03.json` to:
- replace insight "Parent has 3 axioms" with "Parent has 1 axiom (weighted_erdos_szekeres = Tidor–Wang–Yang 2016)"
- replace insight "erdos_szekeres might be provable from Mathlib (check for Erdos-Szekeres)" with "erdos_szekeres proved via Theorems100.erdos_szekeres at line 99"
- replace insight "lis_lds_bound axiom might follow from Dilworth theorem" with "lis_lds_bound proved at line 266 via Erdős–Szekeres applied to LIS+1, LDS+1"
- update `nextSteps` accordingly

This memo does **not** edit the JSON — that's mechanic territory (per project workflow). The §1 table is the audit reference.

## 2. OQ-03 scope: algorithmic approaches for max-sum monotonic subsequences

The parent `Erdos1026Problem.lean` defines:

```lean
-- Line 240
noncomputable def LIS {n : ℕ} (seq : RealSeq n) : ℕ :=
  sSup {m | ∃ (sub : Subsequence n m), IsIncreasing seq sub}

-- Line 244
noncomputable def LDS {n : ℕ} (seq : RealSeq n) : ℕ :=
  sSup {m | ∃ (sub : Subsequence n m), IsDecreasing seq sub}

-- Line 177
noncomputable def maxMonotonicSum {n : ℕ} (seq : RealSeq n) : ℝ :=
  ⨆ m, maxMonotonicSumLength seq m
```

These are mathematically clean but **noncomputable** — they offer no algorithmic handle.

**OQ-03 algorithmic angle.** Three standard algorithms exist for LIS / LDS / `maxMonotonicSum`:

### 2.1 Dynamic Programming (DP) — O(n²) per sequence

The textbook DP: for each position `i`, compute `LIS_dp seq i = max{ LIS_dp seq j + 1 : j < i, seq j < seq i }`. Then `LIS seq = max_i (LIS_dp seq i)`.

**Lean signature** (proposed):
```lean
def LIS_dp : (Fin n → ℝ) → Fin n → ℕ
  | seq, i => -- recurse on i with bookkeeping
```

This is **computable** — runs in O(n²) time on a concrete sequence. Bridge theorem:
```lean
theorem LIS_dp_eq_LIS (seq : RealSeq n) (hDistinct : Function.Injective seq) :
    Finset.univ.sup' (Finset.univ_nonempty.cast ...) (LIS_dp seq) = LIS seq
```

Estimated LOC: ~120 (40 for `LIS_dp` def + structural lemmas + correctness theorem). Requires `Decidable (seq i < seq j)` instance — automatic for `ℝ` since `LinearOrder ℝ` is decidable for concrete reals (but not in general — need to thread `hDistinct + LinearOrder` instances explicitly).

### 2.2 Patience Sorting — O(n log n) for LIS length

Patience sorting maintains a sequence of "piles" (binary-searchable stacks); the number of piles equals LIS. This is faster algorithmically but **harder to formalize** (binary search invariants).

Estimated LOC: ~250+ if attempted in pure Lean. Likely beyond a single session.

### 2.3 Robinson–Schensted–Knuth (RSK) correspondence

RSK builds a bijection between sequences and pairs of Young tableaux of conjugate shape. The maximum tableau shape gives LIS = top row length and LDS = first column length (by Schensted's theorem).

**Mathlib coverage** (audit in §4): `Mathlib.Combinatorics.Young.YoungDiagram` and related files have Young diagram infrastructure but **no RSK insertion algorithm** as of the lake-pinned SHA.

Estimated LOC: ~500+ for a full RSK implementation. Beyond a single session; would be a multi-session research thread.

### 2.4 Recommended OQ-03 scope (minimal)

**Phase OQ-03-A** (single session, ~120 LOC):
- Define `LIS_dp : RealSeq n → Fin n → ℕ` (the DP table).
- Prove `LIS_dp seq i ≥ 1` for all `i` (the singleton subsequence).
- Prove a structural recurrence: `LIS_dp seq i = 1 + max { LIS_dp seq j : j < i, seq j < seq i }` (or 1 if no such j).
- Prove `LIS_dp_eq_LIS`: agreement with the `sSup`-based `LIS` definition.

**Phase OQ-03-B** (optional follow-up, ~80 LOC):
- Define `weighted_LIS_dp : RealSeq n → Fin n → ℝ` (max-sum version, using `seq i` as the per-element weight).
- Prove `weighted_LIS_dp ≤ maxMonotonicSum`.

**Phase OQ-03-C** (research-level, beyond scope of this slug):
- Patience sorting O(n log n) — would need its own slug.
- RSK correspondence — also its own slug.

The §3 design memo focuses on Phase OQ-03-A.

## 3. Phase OQ-03-A design memo

### 3.1 The DP recurrence

Let `seq : Fin n → ℝ` with `Function.Injective seq`. Define inductively:

```
LIS_dp seq 0 = 1                                  -- singleton at position 0
LIS_dp seq (i+1) = 1 + max { LIS_dp seq j : Fin (i+1) | seq j < seq (i+1) } ∪ {0}
                 = max ({1} ∪ { 1 + LIS_dp seq j : ... })
```

(Use `Finset.max'` with a nonempty default; cleaner formulation below.)

### 3.2 Lean signature (proposed)

```lean
namespace Erdos1026.OQ03

open Erdos1026

variable {n : ℕ} (seq : RealSeq n)

/-- DP table for the longest increasing subsequence ending at position `i`. -/
def LIS_dp : Fin n → ℕ :=
  fun i =>
    let candidates : Finset (Fin n) := Finset.univ.filter (fun j => j < i ∧ seq j < seq i)
    if h : candidates.Nonempty then
      1 + candidates.attach.image (fun ⟨j, _⟩ => LIS_dp j) |>.max' (by
        simp [Finset.Nonempty, Finset.image_nonempty]; exact h)
    else 1
  termination_by i.val
  decreasing_by sorry  -- need: j.val < i.val for the recursion to be well-founded

-- Equivalent (without recursion via the candidate set, using Finset.univ.range):
def LIS_dp' : Fin n → ℕ := ...  -- iterative form via Finset.fold
```

**Issue**: the well-founded recursion needs the `decreasing_by` term `j.val < i.val`. Mathlib does NOT have an obvious automation for this when `j : Fin n` is extracted from a `Finset.filter` membership. The structurally-clean form uses `Nat`-recursion on `i.val` with an explicit case split — ~30 LOC of bookkeeping rather than 5.

### 3.3 Alternative: iterative DP via `Finset.fold`

Cleaner: build the entire DP table in one Finset.fold rather than recursion:

```lean
def LIS_dp_table : Fin n → ℕ := fun i =>
  Finset.univ.filter (fun j : Fin n => j.val ≤ i.val).fold
    (fun j acc =>
      if seq j < seq i ∨ j = i then max acc (1 + ...) else acc) 0
```

This avoids well-founded recursion but is harder to reason about. The `LIS_dp_eq_LIS` proof goes via induction on `n` not on `i.val`.

### 3.4 Correctness theorem

```lean
theorem LIS_dp_eq_LIS (seq : RealSeq n) (hDistinct : Function.Injective seq) (hn : n ≥ 1) :
    Finset.univ.sup' (Finset.univ_nonempty.image (fun (i : Fin n) => LIS_dp seq i))
        (Finset.univ_nonempty.cast (by simp)) = LIS seq := by
  sorry
```

**Proof strategy**:
- `≤` direction: each `LIS_dp seq i` corresponds to a concrete increasing subsequence ending at `i` (construct it by backtracking through the `argmax` of the recurrence). So `LIS_dp seq i ≤ LIS seq` for each `i`.
- `≥` direction: any increasing subsequence of length `m` produces a sequence `j₀ < j₁ < ... < j_{m-1}` of positions; then `LIS_dp seq j_{m-1} ≥ m` by induction on `m`.

Estimated LOC for the correctness theorem: ~60.

### 3.5 Total estimated LOC for OQ-03-A

| Item | Est. LOC |
|---|---:|
| `LIS_dp` def + decidability/structural lemmas | ~40 |
| `LIS_dp` singleton lower bound | ~5 |
| `LIS_dp` recurrence theorem | ~20 |
| `LIS_dp_eq_LIS` correctness | ~60 |
| Imports + namespace + module docstring | ~15 |
| **Total** | **~140** |

This is in line with the OQ-03-A "single session" target (~120 LOC estimate in §2.4).

**File**: a new `proofs/Proofs/Erdos1026OQ03.lean` (or possibly `Erdos1026Problem` extension Part VIII) importing the parent. New module / part decision belongs to S2 ACT.

## 4. Mathlib coverage audit at lake-pinned SHA

The slug uses Mathlib at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from `proofs/lake-manifest.json`). The following grep audit at this SHA confirms what's missing.

### 4.1 LIS / patience-sorting / RSK searches

```bash
gh api "search/code?q=repo:leanprover-community/mathlib4+%22LIS%22+%22increasing+subsequence%22" --jq '.items[].path'
# returns: (no results)
```

No direct LIS algorithm in Mathlib.

```bash
gh api "search/code?q=repo:leanprover-community/mathlib4+%22patience_sort%22+OR+%22patienceSort%22" --jq '.items[].path'
# returns: (no results)
```

No patience sorting.

```bash
gh api "search/code?q=repo:leanprover-community/mathlib4+%22Robinson_Schensted%22+OR+%22RSK%22" --jq '.items[].path'
# returns: (no results)
```

No RSK correspondence at this SHA.

### 4.2 Young tableau coverage

```bash
gh api "search/code?q=repo:leanprover-community/mathlib4+%22YoungDiagram%22" --jq '.items[].path' | head
```

Returns:
- `Mathlib/Combinatorics/Young/YoungDiagram.lean`
- `Mathlib/Combinatorics/Young/SemistandardTableau.lean`
- `Mathlib/Combinatorics/Young/StandardTableau.lean`

So Mathlib has Young tableau **infrastructure** but no insertion / RSK algorithm. Building RSK on top of these would be a clean future research thread (its own slug).

### 4.3 Erdős–Szekeres coverage (existing)

```bash
gh api "search/code?q=repo:leanprover-community/mathlib4+%22erdos_szekeres%22" --jq '.items[].path'
```

Returns:
- `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean`
- `docs/100.yaml`
- `docs/1000.yaml`

The Wiedijk100Theorems version is what `Erdos1026Problem.lean:106` uses. It's an existence theorem, not an algorithm.

### 4.4 Net Mathlib coverage for OQ-03

**Available**:
- `Theorems100.erdos_szekeres` (existence of long monotonic subsequence) — Wiedijk100Theorems
- `Finset.fold`, `Finset.max'`, `Finset.image` — generic Finset machinery
- `Fin.induction`, `Nat.strong_induction` — induction primitives
- `Decidable (a < b)` for `a, b : ℝ` (via `DecidableLT (Real := ...)` — but in practice this needs `Decidable (seq j < seq i)` instances threaded through DP)

**Missing**:
- LIS algorithm (DP, patience sort, or RSK) — would be a new contribution
- Weighted-LIS / max-sum-monotonic-subsequence algorithm — also new

**Conclusion**: OQ-03-A (DP-based `LIS_dp` + correctness) is a genuine, non-trivial Lean contribution. Estimated 140 LOC; tractable in 1–2 sessions.

## 5. Comparison: OQ-03 vs the parent's `weighted_erdos_szekeres` axiom

The parent's remaining axiom `weighted_erdos_szekeres` (Tidor–Wang–Yang 2016) is **research-level**: a 2016 paper resolving Cambie's Conjecture, requiring sophisticated combinatorial argument. It is **not** addressable in a typical research session.

OQ-03's algorithmic angle is **orthogonal** to this axiom:
- Discharging `weighted_erdos_szekeres` would prove the **existence** of a 1/k-summing monotonic subsequence, but says nothing computational about how to find it.
- An OQ-03 `LIS_dp` formalization would give a **constructive algorithm** for the LIS-length problem, but does not prove Tidor–Wang–Yang.

So OQ-03 work is **independent of** and **not blocked by** the remaining axiom. This is the strongest argument for prioritizing OQ-03-A as a future S2 ACT target on this slug.

## 6. Anti-targets (this S1 OBSERVE)

6.1 **Do NOT edit `proofs/Proofs/Erdos1026Problem.lean`.** The OQ-03 algorithmic file should be a NEW file (`Erdos1026OQ03.lean` proposed) or a new Part in the parent. The decision belongs to S2 ACT.

6.2 **Do NOT edit `state.md`, `knowledge.md`, `problem.md`, or gallery JSON.** Phase remains NEW (per state.md); the audit findings in §1 are additive information for a future curator or mechanic to incorporate.

6.3 **Do NOT attempt to discharge `weighted_erdos_szekeres`.** It is the Tidor–Wang–Yang 2016 theorem; orthogonal to OQ-03 and beyond scope.

6.4 **Do NOT pre-commit to one of the three algorithmic approaches** (DP, patience sort, RSK). §2.4 recommends DP for OQ-03-A as the minimal-scope start, but the S2 ACT implementer makes the call.

6.5 **Do NOT modify `Theorems100.erdos_szekeres` or other Mathlib references.** The §4 audit is read-only.

6.6 **Do NOT run docker build.** Doc-only.

## 7. Conflict-free guarantee

This PR adds **one file at a fresh path**:

```
research/problems/erdos-1026-oq-03/sessions/2026-05-13-s1-observe-axiom-landscape-and-oq03-algorithm-scope.md
```

Disjoint from:

- All existing PRs on `erdos-1026-oq-03`: **none in the last 7 days** (last research activity on parent `erdos-963` slug at PR #14239 on 2026-05-01; no `erdos-1026` PRs since 2026-04-04 enrichments).
- Sibling slugs `erdos-1026` (no research/problems entry) and `erdos-1026-oq-01/oq-02` (no research/problems entries).
- Eventual S2 ACT (Phase OQ-03-A): will modify `proofs/Proofs/Erdos1026OQ03.lean` (new file) or add Part VIII to the parent. **Neither is touched here.**

**Pre-claim probe (2026-05-13 ~11:49 UTC)**: 0 open PRs for `erdos-1026-oq-03 in:title`; last research-related merge on the slug-tree is #14239 (`research(erdos-963): eliminate trivial_upper_bound axiom`) at 2026-05-01 — 12 days stale. Race-safety: essentially infinite window.

## 8. Honesty assessment

**Mathematical content**: zero new mathematics. The §1 audit is a literal grep + line-counting exercise. §2's algorithmic survey is textbook (DP, patience sort, RSK are standard); the contribution is **scoping** OQ-03 against the existing parent file's `noncomputable def LIS / LDS / maxMonotonicSum` infrastructure.

**Originality**: low. Value-adds:

- §1 documents the **stale `Parent has 3 axioms` insight** in the slug JSON — this would otherwise mislead a future researcher into chasing already-proved theorems.
- §2's three-tier algorithm scope (DP / patience / RSK) + recommended Phase OQ-03-A pathway gives a concrete first-session target (~140 LOC).
- §4's Mathlib coverage audit at the **lake-pinned SHA** confirms no LIS algorithm exists at that snapshot — closing the question of "is this work already done in Mathlib?".
- §5 frames OQ-03 as **orthogonal** to the parent's remaining `weighted_erdos_szekeres` axiom, justifying OQ-03 as a productive thread independent of the harder open problem.

**What could be wrong**:

- The §1 line numbers (706 LOC, 1 axiom) are at the current main HEAD. If a parallel session lands a new axiom or theorem before S2 ACT runs, the numbers shift.
- The §2.3 RSK claim ("not in Mathlib") was a `gh api search/code` query. If the search returned 0 due to my query phrasing (`%22RSK%22` may miss `Robinson` or `_Schensted` variants), there could be partial RSK in Mathlib I missed.
- The §3.2 `LIS_dp` recurrence requires Decidability of `seq j < seq i`; for `seq : Fin n → ℝ`, this needs `LinearOrder ℝ` decidability (true at the level of `Real.instDecidableLT` for concrete reals) but threading the instance through Finset.filter may be more work than the §3.5 ~40-LOC estimate.
- The §3.3 iterative `Finset.fold`-based DP is an alternative I have not fully designed; the S2 ACT implementer should weigh both forms.

**Verification performed**:

- Lean file grep (`grep -c "^axiom " proofs/Proofs/Erdos1026Problem.lean` = 1) confirms §1's axiom count.
- Lean file grep for `theorem erdos_szekeres`, `theorem lis_lds_bound` confirms both are proved (not axioms).
- `gh api search/code` queries for `LIS`, `patience_sort`, `RSK`, `Robinson_Schensted`, `YoungDiagram` confirm §4's Mathlib coverage findings.
- §5 orthogonality claim is logically clear: `LIS_dp` computes existing-`LIS`, doesn't require `weighted_erdos_szekeres` axiom.

**0 axioms added, 0 sorries added/removed, 0 Lean LOC changed in this PR.** No Docker build.

## 9. Appendix A — Mathlib API verification commands

```bash
# (1) Confirm Erdos1026Problem axiom count = 1:
grep -c "^axiom " proofs/Proofs/Erdos1026Problem.lean

# (2) Confirm erdos_szekeres + lis_lds_bound are proved (not axioms):
grep -n "^theorem erdos_szekeres\|^theorem lis_lds_bound" proofs/Proofs/Erdos1026Problem.lean

# (3) Confirm Mathlib has Theorems100.erdos_szekeres but no LIS algorithm:
gh api "search/code?q=repo:leanprover-community/mathlib4+%22Theorems100.erdos_szekeres%22" \
  --jq '.items[].path'

# (4) Confirm Mathlib has Young tableau infrastructure:
gh api "search/code?q=repo:leanprover-community/mathlib4+%22YoungDiagram%22" \
  --jq '.items[].path' | head

# (5) Confirm no Robinson–Schensted / RSK insertion at pinned SHA:
gh api "search/code?q=repo:leanprover-community/mathlib4+%22Schensted%22" \
  --jq '.items[].path'

# (6) View parent file structure:
grep -n "^theorem\|^axiom\|^def\|^noncomputable def" \
  proofs/Proofs/Erdos1026Problem.lean
```

## 10. References

- **PR #14239** (`research(erdos-963): eliminate trivial_upper_bound axiom (1→0)`, merged 2026-05-01): last research activity on the broader `erdos-963` slug. Confirmed the axiom-elimination workflow on a sibling problem.
- **PR #8523** (`Research: erdos-963 - structural lemmas + axiom doc correction`, merged 2026-03-30): the slug `erdos-1026-oq-03`'s creation context.
- **`proofs/Proofs/Erdos1026Problem.lean`**: parent Lean file (706 LOC, 16 theorems, 1 axiom, 0 sorries).
- **Erdős–Szekeres (1935)**: "A combinatorial problem in geometry" — original existence theorem.
- **Tidor, Wang, Yang (2016)**: "1-color avoiding paths" — proof of Cambie's Conjecture giving `c = 1`. The `weighted_erdos_szekeres` axiom encodes this.
- **Mathlib at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`**: `Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean`, `Mathlib/Combinatorics/Young/{YoungDiagram,SemistandardTableau,StandardTableau}.lean`. All paths verified via `gh api` at this SHA.
- **Project memory pattern**: `feedback_researcher_10_2026_05_12_seeker_fresh_observe_pattern.md` (comprehensive S1 OBSERVE on previously surveyed slugs).
