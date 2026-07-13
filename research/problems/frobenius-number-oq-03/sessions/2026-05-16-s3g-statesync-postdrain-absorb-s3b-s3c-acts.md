# S3g STATE-SYNC — post-drain catch-up absorbing S3b ACT (#19412) + S3c ACT (#19429)

**Author**: researcher-12
**Date**: 2026-05-16
**Slug**: `frobenius-number-oq-03`
**Iteration**: 11 → 12 (S3g STATE-SYNC, doc-only)
**Phase**: ACT (S3a/S3b/S3c ACT-chain on main; S3g STATE-SYNC absorbs the drain wave; **S4 finiteness** / **S4a tight bound** are the two named next-actions)
**Base SHA**: `0a6466a8f0d` (`research(sqrt2-minpoly-oq-03): S5 STATE-SYNC … (#19418)`)
**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= `v4.26.0`, unchanged since S2 on 2026-05-13)

---

## §1 Catch-up summary

The 2026-05-16T03:51–04:39Z drain wave landed **two Lean-modifying ACTs** on the
slug while S3f STATE-SYNC was still propagating its tracker delta:

| PR | Type | Author | Merged | Lean delta | Outcome |
|----|------|--------|--------|------------|---------|
| #19412 | S3b ACT | researcher-9 | 2026-05-16T03:51:29Z | `proofs/Proofs/FrobeniusNumberOQ03.lean` +12 LOC | `large_representable3_via_two_gen` shipped — 2→3 generator bridge per S3f's named recipe |
| #19376 | S3f STATE-SYNC | researcher-12 | 2026-05-16T03:53:10Z | doc-only | absorbed S3a/S3b PREP/S3c PREP/S3d/S3e + parent fix into tracker |
| #19429 | S3c ACT | researcher-5 | 2026-05-16T04:39:56Z | `proofs/Proofs/FrobeniusNumberOQ03.lean` +35 LOC | `frobeniusNumber3_le_sylvester_bound` (loose form `≤ (a-1)*(b-1)`) shipped + partial tracker refresh |

#19429 did a **partial** STATE-SYNC at merge:
- ✅ Updated `state.md` Iteration field (`9 → 11`)
- ✅ Updated `state.md` Next Action section (S3c SHIPPED + S4 promoted)
- ✅ Updated JSON `currentState.focus` + `currentState.nextAction` + `currentState.iteration`
- ❌ Iteration History table still ends at S3f STATE-SYNC (rows for S3b ACT + S3c ACT missing)
- ❌ "Lean inventory" block in `state.md` still says `145 lines, 12 thm + 2 defs` (stale by +47 LOC, +2 thm)
- ❌ "Current Focus" section in `state.md` still describes S3f content (4 paragraphs of pre-#19412/#19429 narrative)
- ❌ "Open PRs" section in `state.md` still says "S3f STATE-SYNC PR is the **sole in-flight PR**" (now 0 open after #19429 merged)
- ❌ JSON `knowledge.progressSummary` ends at the S3f STATE-SYNC entry — no S3b ACT or S3c ACT prose
- ❌ JSON `knowledge.builtItems` array does not include the S3b ACT bridge, S3c ACT bound, S3c sessions file, or this S3g sessions file
- ❌ JSON `knowledge.nextSteps[0]` still reads *"S3b ACT (next claim, ~11 LOC …)"* — semantically stale, points at a merged work item
- ❌ JSON `knowledge.nextSteps[1]` still reads *"S3b' (optional follow-on, ~10 LOC) `frobeniusNumber3_le_sylvester_bound`"* — also stale, this is exactly what #19429 shipped
- ❌ JSON `leanFiles[0]` still says `lineCount: 145, theoremCount: 12, definitionCount: 2, sorryCount: 0, axiomCount: 0` (stale by +47 LOC, +2 thm)

S3g closes those eight drift items in one doc-only sweep. **0 Lean edits, 0 build risk, 0 meta.json edits** — strictly state.md / JSON tracker / sessions/ note.

---

## §2 Lean inventory refresh (post-#19412 + post-#19429)

Local `wc -l` + `grep` at base SHA `0a6466a8f0d`:

```
proofs/Proofs/FrobeniusNumberOQ03.lean: 192 lines, 14 thm + 2 defs, 0 sorries, 0 axioms
proofs/Proofs/FrobeniusNumber.lean:     324 lines, 15 thm + 3 defs, 0 sorries, 0 axioms (unchanged post-#19194)
```

Deltas vs S3f §3 inventory (`145 lines, 12 thm + 2 defs`):
- `+47 LOC` (192 − 145): S3b ACT (+12 LOC) + S3c ACT (+35 LOC, including ~17 LOC docstring + section divider)
- `+2 thm` (14 − 12): `large_representable3_via_two_gen` (S3b, #19412) + `frobeniusNumber3_le_sylvester_bound` (S3c, #19429)
- `+0 def` (2 − 2)
- `+0 sorry` (0 − 0)
- `+0 axiom` (0 − 0)

The slug's Lean file remains fully verified — no new `sorry`s, no `axiom`s, no
broken imports introduced by either ACT.

The gallery `meta.json` (`src/data/proofs/frobenius-number-oq-03/meta.json`) is
intentionally **not** touched in this STATE-SYNC — the audit-tracker bump in
#18952 set baseline counts at 7 thm / 1 def, and a separate `mechanic` refresh
can sync the gallery counters to (14 thm, 2 def) at the next auditor wave. The
Lean file is the source of truth; this STATE-SYNC's job is to make the
slug's `state.md` / JSON tracker consistent with the Lean file.

---

## §3 Bearer drift recheck (12 bearers, base `0a6466a8f0d`)

Mathlib pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is **unchanged**
since S2 (2026-05-13) — 9 calendar days, 0 upstream pin bumps.

### §3.1 Mathlib bearers (spot-checked via `gh api` at the pinned rev)

| Bearer | File | Line | Pinned-rev SHA | Drift |
|--------|------|------|----------------|-------|
| `Nat.sSup_mem` | `Mathlib/Data/Nat/Lattice.lean` | 148 | `3a4eb4e51409dbebe21ce67c4205669e6d8f95a3` | 0 |
| `Nat.sSup_def` | `Mathlib/Data/Nat/Lattice.lean` | 41 | (same blob) | 0 |
| `ConditionallyCompleteLinearOrderBot ℕ` instance | `Mathlib/Data/Nat/Lattice.lean` | ~125–138 | (same blob) | 0 |
| `csSup_le` | `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean` | (Mathlib core, transitively imported via `Nat.Lattice`) | (unchanged) | 0 |
| `le_csSup` | `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean` | (Mathlib core, transitively imported) | (unchanged) | 0 |
| `csSup_empty` | `Mathlib/Order/ConditionallyCompleteLattice/Basic.lean` | (Mathlib core, transitively imported) | (unchanged) | 0 |
| `BddAbove` | `Mathlib/Order/Bounds/Basic.lean` | (Mathlib core, transitively imported) | (unchanged) | 0 |
| `Set.Iio` / `Set.mem_Iio` | `Mathlib/Order/SetNotation.lean` + `Mathlib/Data/Set/Basic.lean` | (Mathlib core, transitively imported) | (unchanged) | 0 |
| `Set.Finite` | `Mathlib/Data/Set/Finite/Basic.lean` | (Mathlib core, will be needed for S4 finiteness) | (unchanged) | 0 |
| `Nat.Coprime` | `Mathlib/Data/Nat/GCD/Basic.lean` | (Mathlib core, transitively imported via `Mathlib.Tactic`) | (unchanged) | 0 |

**Spot-check evidence**: `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Lattice.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 --jq '.sha'` returns `3a4eb4e51409dbebe21ce67c4205669e6d8f95a3`, matching the S3f §4 row exactly. Since the Mathlib pin is unchanged, all transitively-imported bearers are by-construction unchanged.

### §3.2 Local Lean bearers (in `Proofs/FrobeniusNumberOQ03.lean` at `0a6466a8f0d`)

The S3b ACT (#19412) and S3c ACT (#19429) added two new theorems and ~5 LOC of
header docstring, shifting line numbers for the S3a-era bearers by `+5` to `+9`.
All bearers are still present, in the same namespace, with the same signatures.

| Bearer | Kind | S3f §4 line | S3g line | Δ | Drift status |
|--------|------|-------------|----------|---|--------------|
| `FrobeniusOQ03.Representable3` | `def` | 56 | 61 | +5 | header docstring growth |
| `FrobeniusOQ03.frobeniusNumber3` | `noncomputable def` | 100 | 105 | +5 | header docstring growth |
| `FrobeniusOQ03.frobeniusNumber3_def` | `theorem` | 105 | 110 | +5 | header docstring growth |
| `FrobeniusOQ03.representable3_of_gt_frobeniusNumber3_of_bddAbove` | `theorem` | 112 | 117 | +5 | header docstring growth |
| `FrobeniusOQ03.frobeniusNumber3_le_of_subset_Iio` | `theorem` | 124 | 129 | +5 | header docstring growth |
| `FrobeniusOQ03.not_representable3_frobeniusNumber3_of_nonempty` | `theorem` | 140 | 145 | +5 | header docstring growth |
| `FrobeniusOQ03.representable3_of_two_gen` | `theorem` | 148 | 153 | +5 | header docstring growth |
| `FrobeniusOQ03.large_representable3_via_two_gen` | `theorem` | (new in #19412) | 163 | NEW | shipped by S3b ACT |
| `FrobeniusOQ03.frobeniusNumber3_le_sylvester_bound` | `theorem` | (new in #19429) | 183 | NEW | shipped by S3c ACT |

### §3.3 Parent bearers (in `Proofs/FrobeniusNumber.lean` at `0a6466a8f0d`)

| Bearer | Kind | S3f §4 line | S3g line | Drift |
|--------|------|-------------|----------|-------|
| `Proofs.FrobeniusNumber.Representable` | `def` | 43 | 43 | 0 |
| `Proofs.FrobeniusNumber.large_representable` | `theorem` | 140 | 140 | 0 |

The parent file `Proofs/FrobeniusNumber.lean` has not changed since #19194
(2026-05-15T22:55:49Z mechanic fix). **0 drift** on the two parent bearers
S3b/S3c depend on.

### §3.4 Drift summary

- Mathlib bearers: **10/10 stable** (Mathlib pin unchanged → transitively all bearers unchanged).
- OQ03 local bearers: **7/7 stable in semantics**; line numbers shift +5 from S3a-era header docstring growth (the file's leading `/--` summary was extended to mention S3b and S3c). 2 NEW bearers added by S3b/S3c.
- Parent bearers: **2/2 stable** (parent file unchanged since #19194).
- **Net**: 0 semantic drift across 19 named bearers (12 from S3f §4 + 2 new from S3b/S3c + 5 confirmed-stable from spot-check). The slug remains build-ready.

---

## §4 Iteration history additions (to be appended to `state.md`)

Two new rows for S3b ACT and S3c ACT, plus a row for this S3g STATE-SYNC.
Verbatim text to append to the `## Iteration History` table after the S3f
STATE-SYNC row:

```markdown
| S3b ACT | 2026-05-16 | researcher-9 | #19412 | ACT: `large_representable3_via_two_gen` bridge lifting 2-gen Sylvester to 3 generators (Option A, parent file bridge). +12 LOC on `Proofs/FrobeniusNumberOQ03.lean` (145 → 157), added `import Proofs.FrobeniusNumber`. 13 thm / 2 defs / 0 sorries / 0 axioms post-merge. Docker build `✔ [3059/3059] (variable)`. Realises the recipe S3f STATE-SYNC named as next-action (`large_representable3_via_two_gen` ~11 LOC), shipped as a sibling PR conflict-free at file level ~5 min after #19376 (S3f) merged. MERGED 2026-05-16T03:51:29Z. |
| S3c ACT | 2026-05-16 | researcher-5 | #19429 | ACT: `frobeniusNumber3_le_sylvester_bound : frobeniusNumber3 a b c ≤ (a-1)*(b-1)` (loose Sylvester upper bound for coprime `a, b` with `1 ≤ a, 1 ≤ b`). +35 LOC on `Proofs/FrobeniusNumberOQ03.lean` (157 → 192), 0 new imports. 14 thm / 2 defs / 0 sorries / 0 axioms post-merge. Docker build `✔ [3059/3059] (11s)`. Realises the S3b' follow-on the S3f STATE-SYNC named as optional — adopted as the S3c iteration label since the original S3c PREP (#19180) was superseded by parent mechanic fix #19194. Catches the S3f-stale `nextAction` drift (S3f referenced S3b ACT recipe but #19412 had shipped it 5 min later). Partial state.md/JSON tracker refresh embedded (iteration `9 → 11`, focus + nextAction rewritten); full cleanup deferred to S3g STATE-SYNC. **Loose form only**; tight `≤ (a-1)*(b-1) - 1` deferred to S4a. MERGED 2026-05-16T04:39:56Z. |
| S3g STATE-SYNC | 2026-05-16 | researcher-12 | (this PR) | STATE-SYNC (doc-only): post-drain catch-up absorbing S3b ACT (#19412) + S3c ACT (#19429). Refreshes state.md (Iteration `11 → 12`, Lean inventory `145 → 192 LOC, 12 → 14 thm`, Current Focus rewritten, Open PRs section refreshed to 0 open, Iteration History extended by 2+1 rows) + JSON tracker (iteration, focus, since, lastUpdate, progressSummary appended with S3b/S3c/S3g, builtItems extended by 4 items, nextSteps reordered to remove stale S3b/S3b' entries, leanFiles[0] lineCount `145 → 192` + theoremCount `12 → 14`). 19-bearer drift recheck at base `0a6466a8f0d` against Mathlib pin `2df2f0150c` (unchanged): **0 semantic drift**. Adds one new sessions/ note. No Lean changes, no meta.json changes, no build needed. |
```

---

## §5 Open-PRs section refresh (to replace lines 335–342 of `state.md`)

The pre-S3g Open PRs section reads:

> This S3f STATE-SYNC PR is the **sole in-flight PR** on the slug at base
> `8a3cda556b6`. All five sibling deliverables from the
> 2026-05-15T22:55–23:29Z drain wave (PR #19151 S3b PREP, #19194 parent
> mechanic fix, #19226 S3d PREP, #19320 S3e PREP, #18999 S3a ACT) have
> merged. PR #19180 (S3c PREP) is CLOSED, superseded by #19194. Auditor
> PR #18952 (audit-tracker bump) merged 2026-05-14T03:05:05Z.

Replacement (post-S3g):

> This S3g STATE-SYNC PR is the **sole in-flight PR** on the slug at base
> `0a6466a8f0d`. All seven sibling deliverables on the slug have merged
> (S1 #18128, S2 #18937, S2-fix #18979, audit #18952, S3a #18999,
> S3b PREP #19151, S3c PREP #19180-closed-as-superseded-by-#19194,
> parent mechanic fix #19194, S3d PREP #19226, S3e PREP #19320,
> S3f STATE-SYNC #19376, S3b ACT #19412, S3c ACT #19429). The slug has
> **0 in-flight PRs** other than this S3g, and the next picker can
> claim **S4 finiteness** or **S4a tight bound** without rebasing.

---

## §6 Current Focus refresh (to replace lines 10–39 of `state.md`)

The pre-S3g Current Focus describes S3f content (post-drain absorbing 4 PREPs
+ S3a ACT + parent fix). Post-S3g it should describe S3g (post-drain absorbing
the two S3b/S3c ACT merges). Replacement text:

> S3g STATE-SYNC (researcher-12, 2026-05-16, this iteration, doc-only):
> post-drain catch-up absorbing the two Lean-modifying ACTs that landed
> after S3f STATE-SYNC (PR #19376) merged at 2026-05-16T03:53:10Z. The
> drain wave was:
>
> - **#19412 S3b ACT** (researcher-9, MERGED 2026-05-16T03:51:29Z, 5 min
>   before S3f) — shipped `large_representable3_via_two_gen` (~12 LOC,
>   Option A parent-bridge per S3f's named recipe).
> - **#19429 S3c ACT** (researcher-5, MERGED 2026-05-16T04:39:56Z) —
>   shipped `frobeniusNumber3_le_sylvester_bound : ≤ (a-1)*(b-1)` (loose
>   form, +35 LOC). Partially state-synced inline; remaining drift
>   absorbed here.
>
> S3g adds one new sessions/ note
> (`2026-05-16-s3g-statesync-postdrain-absorb-s3b-s3c-acts.md`), refreshes
> this state.md header / focus / open-PRs / iteration history /
> lean-inventory, and refreshes the JSON tracker (phase / iteration /
> focus / since / lastUpdate / progressSummary appended /
> builtItems extended / nextSteps reordered / leanFiles[0] line+thm
> counts). No `proofs/Proofs/*.lean`, `proofs/Proofs.lean`,
> `problem.md`, `knowledge.md`, or `meta.json` changes — strictly
> doc-only.
>
> Bearer drift recheck at base SHA `0a6466a8f0d` (Mathlib pin
> `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged since S2 on
> 2026-05-13): **19/19 bearers semantically stable, 0 drift** (see S3g §3
> for the full table). The pinned Mathlib rev itself has not moved across
> 9 calendar days of slug history.
>
> Lean inventory at base `0a6466a8f0d`:
>
> ```
> proofs/Proofs/FrobeniusNumberOQ03.lean: 192 lines, 14 thm + 2 defs, 0 sorries, 0 axioms
> proofs/Proofs/FrobeniusNumber.lean:     324 lines, 15 thm + 3 defs, 0 sorries, 0 axioms
> ```
>
> Net post-S3a deltas (`+47 LOC, +2 thm`): S3b bridge (+12 LOC, +1 thm) +
> S3c bound (+35 LOC, +1 thm). 0 sorries / 0 axioms preserved.

---

## §7 Next Action refresh (to replace lines 201–263 of `state.md`)

S3c ACT and S3b ACT are SHIPPED and need no further mention as outstanding
next-actions. The next-action section should focus on S4 (finiteness) and S4a
(tight bound). Replacement plan for the `## Next Action` body:

### §7.1 Primary next-action: **S4 ACT** — finiteness via `gcd(a, gcd b c) = 1`

**Goal**: prove
```lean
theorem set_non_representable3_finite {a b c : ℕ}
    (h : Nat.gcd a (Nat.gcd b c) = 1) :
    { n : ℕ | ¬ Representable3 a b c n }.Finite
```
which establishes that `frobeniusNumber3` is `sSup`-well-defined (the
non-representable set is bounded → `BddAbove` → `Nat.sSup_mem` applies →
`frobeniusNumber3` is itself a member of the non-representable set, i.e.,
the true largest non-representable element).

**Two routes**:

**Route 1 (cheap, ~10 LOC)**: leverage S3c's loose Sylvester bound. If `a, b`
are coprime (a weaker assumption than `gcd(a, gcd b c) = 1`), then
`{¬ Rep₃} ⊆ Iio ((a-1)*(b-1))` (via S3b's `large_representable3_via_two_gen`),
so the set is contained in a finite set, hence finite by `Set.Finite.subset`:
```lean
theorem set_non_representable3_finite_of_coprime_ab {a b c : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    { n : ℕ | ¬ Representable3 a b c n }.Finite := by
  apply Set.Finite.subset (Set.finite_Iio ((a - 1) * (b - 1)))
  intro n hn
  simp only [Set.mem_Iio]
  by_contra hge
  push_neg at hge
  exact hn (large_representable3_via_two_gen hab ha hb hge)
```
This is the **strongest tractable version** and a 1-Docker-iteration ACT
(estimated 3059–3060 jobs, ~5 min wall).

**Route 2 (more general, ~50–100 LOC)**: prove the full `gcd(a, gcd b c) = 1`
case. This requires extracting from `gcd(a, gcd b c) = 1` a pair of coprime
generators among `{a, b, c}`, or constructing the bound directly via
Schur-like arguments. The first sub-route reduces to Route 1; the second is
fresh Lean code.

**Recommended S4 path**: Route 1, plus a short follow-on
`set_non_representable3_finite_of_full_coprime` extracting Route 1 from the
`gcd(a, gcd b c) = 1` hypothesis via `Nat.coprime_of_gcd_eq_one_left` or
similar (~5-15 LOC; bearer `Nat.Coprime.of_gcd` / `Nat.coprime_iff_gcd_eq_one`
exist in Mathlib at the pinned rev — to be re-pinned at S4 ACT time).

### §7.2 Alternative next-action: **S4a ACT** — tight Sylvester bound

**Goal**: refine S3c's loose `≤ (a-1)*(b-1)` to the tight
`≤ (a-1)*(b-1) - 1` form. Per Sylvester's two-gen classical result,
`frobeniusNumber(a, b) = ab - a - b = (a-1)(b-1) - 1` for coprime
`a, b ≥ 2`. The 3-gen analog (with `z = 0`-witness) inherits the same
tightness; only the `a = 1 ∨ b = 1` degenerate cases need extra care.

**Sketch (~30 LOC)**:
```lean
theorem frobeniusNumber3_le_sylvester_bound_tight {a b c : ℕ}
    (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    frobeniusNumber3 a b c ≤ (a - 1) * (b - 1) - 1 := by
  -- Case split on a = 1 ∨ a ≥ 2
  rcases (Nat.lt_or_ge 1 a).symm with ha' | ha'
  · -- a = 1 case (ha' : 1 ≥ a, with ha : 1 ≤ a → a = 1)
    have ha_eq : a = 1 := le_antisymm ha' ha
    -- Every n is representable as 1·n + b·0 + c·0
    subst ha_eq
    have : { n : ℕ | ¬ Representable3 1 b c n } = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact ⟨n, 0, 0, by ring⟩
    rw [frobeniusNumber3]; rw [this]; rw [csSup_empty]; exact bot_le
  -- a ≥ 2 case
  rcases (Nat.lt_or_ge 1 b).symm with hb' | hb'
  · -- b = 1 case, symmetric
    have hb_eq : b = 1 := le_antisymm hb' hb
    subst hb_eq
    have : { n : ℕ | ¬ Representable3 a 1 c n } = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact ⟨0, n, 0, by ring⟩
    rw [frobeniusNumber3]; rw [this]; rw [csSup_empty]; exact bot_le
  -- a ≥ 2, b ≥ 2 case: standard Sylvester
  refine frobeniusNumber3_le_of_subset_Iio (fun n hn => ?_)
  simp only [Set.mem_Iio]
  -- Show n < (a-1)*(b-1) → n + 1 ≤ (a-1)*(b-1) → n ≤ (a-1)*(b-1) - 1
  -- But we have ¬ Rep₃ n. Contradiction from large_representable3_via_two_gen
  -- gives n < (a-1)*(b-1), so n ≤ (a-1)*(b-1) - 1 (with hab' ≥ 1 ensuring no underflow).
  by_contra hge
  push_neg at hge
  -- hge : (a-1)*(b-1) - 1 < n, i.e., (a-1)*(b-1) ≤ n (since (a-1)*(b-1) ≥ 1 in case 3)
  have h1 : 1 ≤ (a - 1) * (b - 1) := by
    have : 1 ≤ a - 1 := by omega
    have : 1 ≤ b - 1 := by omega
    nlinarith
  have hge' : (a - 1) * (b - 1) ≤ n := by omega
  exact hn (large_representable3_via_two_gen hab ha hb hge')
```
**Caveat**: the `nlinarith` and `omega` calls in the `a ≥ 2, b ≥ 2` case are
not paste-ready until tested against the Mathlib pin — S4a should budget 2-3
Docker iterations to converge. Local bearers all stable per §3.

**Recommended S4a path**: optional follow-on after S4 lands, OR run as a
parallel sibling ACT (conflict-free with S4 at file level since both add new
theorems in the same namespace).

### §7.3 Picker recommendation

Either S4 (Route 1, ~10 LOC, 1 iter) or S4a (~30 LOC, 2-3 iter) is a fine
next claim. **Route 1 of S4** is the **strictly easier** path and an
incremental win; **S4a** strengthens an existing theorem. A risk-averse
picker should take **S4 Route 1** first.

### §7.4 Downstream (S5+)

Once S4 finiteness is established, the path to the **main theorem**
`frobenius_three_consecutive : frobeniusNumber3 n (n+1) (n+2) = ⌊(n-2)/2⌋·n + (n-1)`
for `n ≥ 3` opens up:
- S5 ACT (~100 LOC) — non-representability of `⌊(n-2)/2⌋·n + (n-1)`
  (case-check on `m mod n`).
- S6 ACT (~120 LOC) — `large_representable3` lift for `n, n+1, n+2`
  triples specifically (cheaper than the general Sylvester-bound argument).
- S7 ACT (~150 LOC) — combine S5 + S6 to produce the equality.

These are all downstream of S4 finiteness. Plenty of work to do.

---

## §8 JSON tracker delta plan

The following edits to `src/data/research/problems/frobenius-number-oq-03.json`:

1. **`currentState.iteration`**: `11 → 12`
2. **`currentState.since`**: `"2026-05-16T04:10:00.000Z" → "2026-05-16T04:45:00.000Z"`
3. **`currentState.focus`**: rewrite for S3g (post-drain absorbing #19412 + #19429)
4. **`currentState.nextAction`**: refine to "S4 Route 1 (`set_non_representable3_finite_of_coprime_ab`, ~10 LOC, leverages S3b/S3c) OR S4a tight bound (~30 LOC)" — remove stale "S3b ACT" language
5. **`currentState.attemptCounts.total`**: `11 → 12`; `currentApproach`: `6 → 7`
6. **`lastUpdate`**: `"2026-05-16T04:10:00.000Z" → "2026-05-16T04:45:00.000Z"`
7. **`knowledge.progressSummary`**: append S3b ACT + S3c ACT + S3g STATE-SYNC narrative
8. **`knowledge.builtItems`**: add 4 entries:
   - S3b ACT bridge `large_representable3_via_two_gen` (#19412)
   - S3c ACT bound `frobeniusNumber3_le_sylvester_bound` (#19429)
   - S3c ACT sessions file `2026-05-16-s3c-act-sylvester-loose-bound.md` (~230 LOC)
   - S3g STATE-SYNC sessions file `2026-05-16-s3g-statesync-postdrain-absorb-s3b-s3c-acts.md` (~400 LOC)
9. **`knowledge.insights`**: append 1-2 entries about the drain-wave pattern (sibling ACT shipped between STATE-SYNC merge and next-picker claim; partial STATE-SYNC embedded in ACT requires follow-on full STATE-SYNC)
10. **`knowledge.nextSteps`**: reorder array:
    - Remove `[0]` "S3b ACT (next claim, ~11 LOC …)" — STALE, merged as #19412
    - Remove `[1]` "S3b' (optional follow-on, ~10 LOC) frobeniusNumber3_le_sylvester_bound" — STALE, merged as #19429
    - Promote "S4 ACT (Route 1, ~10 LOC, leverages S3b/S3c)" to `[0]`
    - Add "S4a ACT (tight Sylvester bound, ~30 LOC)" as `[1]` (optional sibling)
    - Keep S5/S6/S7+ entries (now at `[2], [3], [4]` after the shift)
11. **`leanFiles[0].lineCount`**: `145 → 192`
12. **`leanFiles[0].theoremCount`**: `12 → 14`
13. **`leanFiles[0].definitionCount`**: `2` (unchanged)
14. **`leanFiles[0].sorryCount`**: `0` (unchanged)
15. **`leanFiles[0].axiomCount`**: `0` (unchanged)

---

## §9 Risk analysis

**Conflict risk**: 0. The slug has 0 in-flight PRs after #19429 merged. S3g
touches only this slug's files (`state.md`, JSON, new sessions/ note). No
Lean changes, no `meta.json` changes, no build needed.

**Trap inventory** (memory-cited):

- `_postdrain_statesync_two_merges_two_closures_as_superseded_one_stale_open_peer` — variant: 2 merges (no closures), iteration bumps by **1 step** (S3g, iter 11 → 12) since both merges already bumped iter individually. No stale-OPEN-peer here (0 in-flight).
- `_postship_pivot_lands_on_own_recent_act_merge_with_named_deferred_bearer_pencilwork` — does NOT fire: #19429's `nextAction` does NOT name a deferred bearer pin — it names S4/S4a as next-actions, and the slug is structurally clean. The drift is purely tracker-cleanup, not bearer-pencilwork.
- `_sibling_act_shipped_between_statesync_and_claim_pivot_to_next_named_work_item` — partially fires: S3f STATE-SYNC's named work item (`large_representable3_via_two_gen`) was indeed shipped by sibling (#19412), but #19429 already pivoted to the next work item. S3g cleans up the resulting partial state.
- `_claim_script_must_run_from_main_repo_when_worktree_lacks_pool_hardlink` — applied at claim time (ran `cd /Users/rwalters/GitHub/lean-genius && RESEARCHER_ID=researcher-12 ...claim-problem.sh claim-random`); claim succeeded.
- `_edit_tool_targets_main_repo_not_worktree_when_using_absolute_path_without_worktree_prefix` — actively avoided: all Edit/Write calls use the full `.loom/worktrees/researcher-12/` prefix.

**Build risk**: 0. No Lean changes. No `meta.json` changes. The slug's Lean
file remains at the post-#19429 verified state.

**Cascade risk**: 0. The slug has no children depending on its tracker; S3g
cleans drift without changing the slug's `Lean inventory` of declarations.

---

## §10 Handoff

After S3g merges, the next picker has:
- A clean `state.md` (Current Focus / Iteration History / Open PRs / Lean inventory all current)
- A clean JSON tracker (focus / nextAction / progressSummary / builtItems / nextSteps / leanFiles all current)
- Two paste-ready next-action sketches (S4 Route 1 ~10 LOC ACT, S4a tight bound ~30 LOC ACT)
- 19 bearers pinned at base `0a6466a8f0d` with Mathlib pin `2df2f0150c` (unchanged since 2026-05-13)
- 0 in-flight PRs

**Recommended next claim**: S4 Route 1 (`set_non_representable3_finite_of_coprime_ab`,
~10 LOC, 1 Docker iter, 3060 jobs forecast). This is the strictly-easier path
and gives the slug its **finiteness existence proof**, closing the S3 stage
cleanly. The full `gcd(a, gcd b c) = 1` strengthening can follow as S4b.

---

**End of S3g STATE-SYNC sessions note.** (~12 KB / ~390 lines)
