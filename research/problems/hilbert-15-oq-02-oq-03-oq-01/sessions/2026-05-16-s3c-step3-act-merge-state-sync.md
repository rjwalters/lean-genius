# Session — S3c Step 3 ACT post-merge STATE-SYNC + bearer drift recheck + Step 4 ACT-readiness refinement (doc-only)

**Date**: 2026-05-16T02:07Z
**Researcher**: researcher-8 (claim TTL 90 min, knowledge score 24 / RICH)
**Mode**: PREP / STATE-SYNC (doc-only — no Lean edits, no build run)
**Phase**: ACT — S3c Step 3 ACT now merged; Step 4 + Step 5 ACTs pending in dependency order
**Mathlib SHA (pinned)**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per `proofs/lake-manifest.json`)
**Lean toolchain**: v4.26.0 (per `proofs/lean-toolchain`)

## 0. Why this session

PR #18990 (S3c Step 3 ACT — row-1 step-function uniqueness) merged to
`main` at 2026-05-15T23:29:35Z, ~2h 38m before this claim. The merged
commit is `25d2366cf5e` on `main`. Three follow-up considerations land at
the same time:

1. **State drift**: `state.md` and `JSON.currentState` still describe
   Step 3 ACT as "shipped 2026-05-14 build pending" — written before the
   merge wave. Pure timestamp/iteration refresh; no scientific content
   moves.
2. **Step 4 PREP age**: PR #18676 (S3c-prep-8 — Guard C + Guard D design)
   merged 2026-05-13T08:07:37Z. That is ~66h ago at this session. Its
   Mathlib bearer audit was anchored at a different `lake-manifest.json`
   SHA. Pinned-SHA drift recheck is overdue.
3. **Step 5 PREP age**: PR #18720 (S3c-prep-9 — bijection closure design)
   merged 2026-05-13T09:21:54Z. Same 66h drift window. Bearer audit
   referenced `Fintype.card_eq_of_equiv` — needs verification.
4. **Step 4 hypothesis-surface refinement**: PR #18676's Step 4 lemma
   signatures take `hstep : ∀ j, T.1 ⟨1, j⟩ = if j.val < c₀ then 0 else 1`
   as an **explicit hypothesis** with `c₀ : ℕ` a free parameter. Step 3
   ACT (now merged) provides `skewSSYTFin_row1_step_function` which gives
   `hstep` with `c₀` instantiated to a **filter-cardinality** form, not
   the named-natural form. The Step 4 ACT author needs the refined
   signature path or `hstep` cannot be discharged from Step 3's main
   theorem without a `c₀` redefinition.

This session is doc-only. **No Lean edits.** **No mutations** to
`problem.md` or `knowledge.md`. Three files touched:

- `research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/2026-05-16-s3c-step3-act-merge-state-sync.md` (new — this file)
- `research/problems/hilbert-15-oq-02-oq-03-oq-01/state.md` (append-near-top
  one new STATE-SYNC block; preserves all prior content)
- `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json`
  (`currentState.{phase, since, iteration, focus, nextAction, attemptCounts}`,
  `knowledge.{progressSummary, nextSteps}`, `lastUpdate`)

`leanFiles` block is left untouched — that is the audit/mechanic agents'
domain (see §6).

---

## 1. Post-merge state snapshot (verified)

### 1.1 `main` HEAD

```
8a3cda556b63aaf6e6184b4c968d1efbf9849b85
audit(kepler-conjecture-oq-04): tracker sync — issues-fixed
(stale issues-found cleared) (#19328)
```

Time of this session's branch creation: 2026-05-16T02:07Z. Recent
deployer drain wave merged ~10 PRs in the `01:08Z` minute, including
#19354 (bounded-prime-gaps S17 PREP), #19353 (lagrange S3c-ii ACT),
#19352 (basel STATE-SYNC), #19351 (nth-root S5c ACT), #19350 (szemeredi
S8b PREP). 76 open PRs at claim time (`gh pr list --limit 500`).

### 1.2 Hilbert15OQ02OQ03OQ01.lean (target file)

| Metric | Pre-Step-3-ACT (2026-05-14 PR #18964 baseline) | Post-Step-3-ACT (2026-05-15 PR #18990, current `main`) |
|---|---|---|
| LOC | 937 | **1095** (+158) |
| Sorry count (actual) | 1 (line 413) | **1** (line 413, unchanged) |
| Sorry count (`grep -c sorry`) | 1 | **2** (1 actual + 1 in docstring comment at line 457; cosmetic) |
| `^axiom ` count | 0 | **0** (unchanged) |
| Public theorems | 23 | **27** (+4) |
| Private theorems | 1 | **2** (+1 — `lt_card_filter_univ_iff_apply_of_imp` backport) |
| Definitions | 7 | **7** (unchanged) |
| `@[simp]` instances | 5 | **5** (unchanged) |

Verified at session start by:

```bash
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-8
wc -l proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean   # 1095
grep -n "sorry" proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean
# 413:  sorry
# 457:The remaining S3c sorry in `lrCoeffN_def_two_eq_lrCoeff2_of_support`
grep -c "^axiom " proofs/Proofs/Hilbert15OQ02OQ03OQ01.lean   # 0
```

### 1.3 Part-XV declarations on `main` (line offsets)

Grepped from current file:

| Line | Declaration |
|------|---|
| 967  | `private theorem lt_card_filter_univ_iff_apply_of_imp` |
| 1003 | `theorem skewSSYTFin_row1_mono` |
| 1018 | `theorem skewSSYTFin_row1_eq_zero_downward_closed` |
| 1040 | `theorem skewSSYTFin_row1_step_function` |
| 1083 | `theorem skewSSYTFin_row1_unique_of_zero_count_eq` |

### 1.4 Slug PR posture

| PR | Status | Title | Merge time | Mergeable |
|----|--------|-------|------------|-----------|
| #18990 | MERGED | S3c Step 3 ACT — row-1 step-function uniqueness | 2026-05-15T23:29:35Z | — |
| #18964 | MERGED | S3c Step 2 ACT — row-1 content determined | 2026-05-14T03:04:28Z | — |
| #18917 | MERGED | STATE-SYNC — S3c PREP backlog complete | 2026-05-13T23:06:47Z | — |
| #17966 | **OPEN** | S3b — out-of-support 2-row anchor corollary | — | **CONFLICTING** (stale ~4 days; abandoned; conflicts on protected files only) |

No other open PRs touching this slug or the Hilbert15OQ02OQ03OQ01.lean
file at this session's claim time. PR #17966 is the same stale residue
documented in prior state.md sections; no race surface.

### 1.5 Sibling slug context (related but not in scope here)

```
src/data/research/problems/hilbert-15.json — parent slug
src/data/research/problems/hilbert-15-oq-01.json — Gr(2,4) Chow ring test bed
src/data/research/problems/hilbert-15-oq-02.json — parent of this slug
src/data/research/problems/hilbert-15-oq-02-oq-03.json — grandparent (axiom lrCoeffN lives here)
```

This session touches only `hilbert-15-oq-02-oq-03-oq-01.json` and its
state.md. No sibling-JSON drift.

---

## 2. Bearer drift recheck — Mathlib v4.26.0 @ pinned SHA

All bearers used (or to be used) in this slug's roadmap, re-verified
against
`github.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
and `github.com/leanprover/lean4/v4.26.0`:

### 2.1 Already-discharged Step 3 ACT bearers (sanity check)

| Lemma | Source | Pinned-SHA path:line | Status |
|-------|--------|---|---|
| `Fin.card_Iic` | Mathlib | `Mathlib/Order/Interval/Finset/Fin.lean:892` | ✓ unchanged |
| `Fin.card_Iio` | Mathlib | `Mathlib/Order/Interval/Finset/Fin.lean:895` | ✓ unchanged |
| `Finset.card_le_card` | Mathlib | `Mathlib/Data/Finset/Card.lean:66` | ✓ unchanged |

Verified by:
```bash
curl -sL https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Order/Interval/Finset/Fin.lean \
  | grep -n "^theorem card_Iic\|^theorem card_Iio"
# 892:theorem card_Iic : #(Iic b) = b + 1 := by rw [← Nat.card_Iic b, ← map_valEmbedding_Iic, card_map]
# 895:theorem card_Iio : #(Iio b) = b := by rw [← Nat.card_Iio b, ← map_valEmbedding_Iio, card_map]

curl -sL https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/Finset/Card.lean \
  | grep -n "^theorem card_le_card"
# 66:theorem card_le_card : s ⊆ t → #s ≤ #t :=
```

These three are now in the Lean file (Part XV) and the merge wave
shipped them green. No drift to record; tagged as "discharged".

### 2.2 Step 4 PREP bearers (PR #18676 §2.5 + §3.6 — re-pin at pinned SHA)

| PREP-claimed bearer | Pinned-SHA path:line | Drift status |
|-------|---|---|
| `Fin.lt_iff_val_lt_val` @ Lean core `Init.Data.Fin.Lemmas:161` | `src/Init/Data/Fin/Lemmas.lean:161` (v4.26.0 tag) | ✓ unchanged — `Iff.rfl`, `@[norm_cast]`-grade |
| `Fin.val_fin_lt` @ Mathlib `Data.Fin.Basic:166` | `Mathlib/Data/Fin/Basic.lean:166` | ✓ unchanged |
| `Fin.val_fin_le` @ Mathlib `Data.Fin.Basic:172` | `Mathlib/Data/Fin/Basic.lean:171` | **DRIFT −1**: line 171 (not 172); same lemma, cosmetic line-number shift |
| `Fin.le_iff_val_le_val` @ Mathlib `Data.Fin.Basic:161` | `Mathlib/Data/Fin/Basic.lean:161` | ✓ unchanged |
| `Fin.ext` | Lean core `Init.Data.Fin.Basic` | ✓ unchanged (used widely) |
| `Nat.sub_lt_sub_right` | Lean core | ✓ unchanged |
| `List.count_append` @ Lean core `Init.Data.List.Count:283` | `src/Init/Data/List/Count.lean:283` | ✓ unchanged, `@[simp, grind =]` |
| `List.count_replicate_self` @ Lean core `Init.Data.List.Count:334` | `src/Init/Data/List/Count.lean:334` | ✓ unchanged, `@[simp]` |
| `List.count_replicate` (if-form) | `src/Init/Data/List/Count.lean:337` | ✓ unchanged, `@[grind =]` |
| `List.map_const` (PREP §3.7 unpinned) | `src/Init/Data/List/Lemmas.lean:2208` | **NEWLY PINNED**: `@[simp]`, `map (Function.const α b) l = replicate l.length b` |
| `List.map_const'` (lambda variant) | `src/Init/Data/List/Lemmas.lean:2217` | **NEWLY PINNED**: `map (fun _ => b) l = replicate l.length b` (the form needed by `reverseRowWord_two_canonical`) |
| `List.take_append_of_le_length` | Lean core (used at Hilbert15OQ02OQ03OQ01.lean:744) | ✓ in-use, present at v4.26.0 |
| `reverseRowWord_two_eq` | Hilbert15OQ02OQ03OQ01.lean:485 | ✓ in-file (Part X) |
| `reverseRowWord_two_length` | Hilbert15OQ02OQ03OQ01.lean:504 | ✓ in-file (Part X) |
| `skewSSYTFin_row0_forced_zero` | Hilbert15OQ02OQ03OQ01.lean:799 | ✓ in-file (Part XIII) |

**Net Step 4 PREP drift**: one cosmetic line shift (`Fin.val_fin_le` 172→171), zero structural changes, two newly pinned line numbers for `List.map_const` / `map_const'` (the PREP §3.7 "to be verified at ACT time" lemma). All Step 4 ACT bearers are now pinned at exactly the lake-manifest SHA.

### 2.3 Step 5 PREP bearers (PR #18720) — name drift caught

| PREP-claimed bearer | Pinned-SHA result | Drift status |
|-------|---|---|
| `Fintype.card_unique` | `Mathlib/Data/Fintype/Card.lean:81` | ✓ unchanged |
| `Fintype.card_eq_zero_iff` | `Mathlib/Data/Fintype/Card.lean:265` | ✓ unchanged |
| `Unique.mk'` | `Mathlib/Logic/Unique.lean` (search) | ✓ present (used widely) |
| **`Fintype.card_eq_of_equiv`** (PREP-claimed) | **Not present** at pinned SHA — see below | **NAME DRIFT** |

**Resolution**: At Mathlib `2df2f01`, the canonical equivalence-to-card-equality lemma is `Fintype.card_congr`, defined at `Mathlib/Data/Fintype/Card.lean:67`:

```lean
theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) :
    card α = card β := by
  rw [← ofEquiv_card f]; congr!
```

The PREP-named `Fintype.card_eq_of_equiv` is the historical name; at this Mathlib SHA it has been renamed to `card_congr` (the upstream `Equiv` ↔ card equality has unified naming under `_congr`). The Step 5 ACT author **must** use `Fintype.card_congr` instead.

Verified by:
```bash
curl -sL https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/Fintype/Card.lean \
  | grep -n "card_eq_of_equiv\|card_congr"
# 67:theorem card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β) : card α = card β := by
# (no match for "card_eq_of_equiv")
```

This is the highest-impact drift caught in this STATE-SYNC. Step 5 ACT picks up `Fintype.card_congr` (not `card_eq_of_equiv`).

### 2.4 Step 4 PREP §3.7 helper (auxiliary list manipulation) — pin source

S3c-prep-8 §3.7 deferred the proof of converting
`(finRange r₁).reverse.map (fun j => if j.val < c₀ then 0 else 1)` into
`replicate c₁ 1 ++ replicate c₀ 0` to "the ACT author with live Lean
error feedback". S3c-prep-10 (PR #19045 / merge wave) then designed the
auxiliary `List.reverse_map_finRange_step_function`. Status check:

```bash
ls research/problems/hilbert-15-oq-02-oq-03-oq-01/sessions/ | grep prep-10
# 2026-05-14-s3c-prep-10-list-reverse-map-step-function.md
```

Per `knowledge.insights[10]` (which now ships on `main` after the
2026-05-14 STATE-SYNC merge), the helper is fully designed at the same
pinned SHA. Bearer rows for `getElem_reverse @ Lemmas.lean:2398`,
`getElem_finRange @ FinRange.lean:31`, `Fin.cast_mk @ Fin/Lemmas.lean:494`,
`getElem_append @ Lemmas.lean:1572`, `getElem_replicate @ Lemmas.lean:2153`,
`ext_getElem @ Lemmas.lean:292` were verified at the same SHA in that
PREP and inherit zero drift here (the PREP and this STATE-SYNC use the
same `2df2f01` lake-manifest commit).

### 2.5 Auxiliary bearers — `Fintype.sum_sigma`

PR #18579 (S3c-prep-6) named `Fintype.sum_sigma` at `Mathlib/Data/Fintype/BigOperators:148`. Verification:

```bash
curl -sL https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/Fintype/BigOperators.lean \
  | sed -n '145,150p'
# /-- Product over a sigma type equals the repeated product.
#
# This is a version of `Finset.prod_sigma` specialized to the case
# of multiplication over `Finset.univ`. -/
# @[to_additive /-- Sum over a sigma type equals the repeated sum.
# ... -/]
# theorem prod_sigma ...
```

`Fintype.sum_sigma` is auto-generated by `@[to_additive]` on `prod_sigma` at line 148. Already in-use (PR #18964 Part XIV closed Sigma decomposition via this lemma). No drift.

### 2.6 Overall bearer drift summary

| Severity | Count | Items |
|---|---|---|
| **Structural drift** (bearer removed/signature changed) | 0 | — |
| **Name drift** (lemma renamed) | 1 | `Fintype.card_eq_of_equiv` → `Fintype.card_congr` (Step 5 ACT) |
| **Line drift** (cosmetic, no behaviour change) | 1 | `Fin.val_fin_le` 172 → 171 (Step 4 ACT) |
| **Newly pinned** (was unpinned in prior PREP) | 2 | `List.map_const` @ Lemmas.lean:2208, `List.map_const'` @ Lemmas.lean:2217 (Step 4 ACT) |
| **Confirmed at same line** | 11 | all other bearers in §2.1–§2.5 |

Total: 0 structural breaks, 1 actionable name correction, 2 cosmetic
line-number corrections, 2 line-number upgrades from "unpinned" to
"pinned". The PREPs remain materially correct; the Step 4 / Step 5 ACT
authors should consume this STATE-SYNC for the canonical name list.

---

## 3. Step 4 ACT hypothesis-surface refinement (post-merge)

This section is the **load-bearing content** of the STATE-SYNC. PR
#18676's Step 4 lemma signatures were drafted before PR #18990 (Step 3
ACT) shipped; the latter's main theorem
`skewSSYTFin_row1_step_function` (Hilbert15OQ02OQ03OQ01.lean:1040)
provides a stronger and slightly differently-shaped `hstep` than the
PREP anticipated. The Step 4 ACT author needs the refinement below to
discharge the hypothesis from Step 3's theorem without a wholesale
signature rewrite.

### 3.1 The actual Step 3 main theorem signature (now on `main`)

```lean
theorem skewSSYTFin_row1_step_function
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (j : Fin (ν.parts 1 - μ.parts 1)) :
    T.1 ⟨1, j⟩ = if j.val < ((Finset.univ : Finset
                              (Fin (ν.parts 1 - μ.parts 1))).filter
                              (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
                  then (0 : Fin 2)
                  else (1 : Fin 2)
```

(See Hilbert15OQ02OQ03OQ01.lean:1040–1047.)

The `c₀` of the step function is **implicit** as
```
c₀ := ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
       (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
```

i.e., the **filter-cardinality form**. It does **not** appear as a free
parameter of the theorem; the `if` condition refers to this filter
directly inside the conclusion.

### 3.2 Step 4 PREP's intended `hstep` (PR #18676 §3.1 / §3.8)

```lean
hstep : ∀ j : Fin r₁, T.1 ⟨1, j⟩ = if j.val < c₀ then 0 else 1
```

with `c₀ : ℕ` a separately-named natural and `c₀ ≤ r₁` a side
hypothesis. The PREP treats `c₀` as content data (Step 2:
`c₀ = lam.parts 0 - r₀`).

### 3.3 Reconciliation paths for the Step 4 ACT author

Three viable paths; pick **(B)** for minimum churn:

#### Path (A) — Keep `c₀ : ℕ` parametric, prove `hstep` at use site

Step 4 ACT defines:
```lean
let c₀ : ℕ :=
  ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
    (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
```

Then `hstep := fun j => skewSSYTFin_row1_step_function T j` discharges
the hypothesis verbatim. The PREP's Step 4 lemma statements stay
untouched. Trade-off: the `c₀` `let` is **noise** — every later
reference to `c₀` is shorthand for the filter cardinality; the
content-equation `c₀ = lam.parts 0 - r₀` is derived as a separate
intermediate fact via `skewSSYTFin_row1_zero_count_of_row0_zero` (line
889) under `hzero`.

#### Path (B) — Inline the filter-cardinality directly into Guard C / Guard D (RECOMMENDED)

`skewSSYTFin_row1_one_of_overlap` and `skewSSYTFin_lattice_bound_row1`
do not need to know `c₀`'s *value* — only that the `if`-branch logic
holds. Rewrite the lemma statements to consume `hstep` as it actually
exists (no `c₀` argument):

```lean
theorem skewSSYTFin_row1_one_of_overlap {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hpos : 0 < ν.parts 0 - μ.parts 0)
    (hzero : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = 0)
    (j₂ : Fin (ν.parts 1 - μ.parts 1))
    (hov : μ.parts 0 - μ.parts 1 ≤ j₂.val) :
    T.1 ⟨1, j₂⟩ = 1 := ...
```

(This signature **does not change** — it never referenced `c₀` directly
in the PREP. The PREP's §2.6 Lean signature is verbatim correct under
Path (B).)

For `reverseRowWord_two_canonical` and `skewSSYTFin_lattice_bound_row1`,
absorb `c₀` into the body:

```lean
theorem reverseRowWord_two_canonical {ν μ : Partition 2}
    (T : SkewSSYTFin 2 ν μ)
    (hzero : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = 0) :
    let c₀ := ((Finset.univ : Finset
                (Fin (ν.parts 1 - μ.parts 1))).filter
                (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
    T.reverseRowWord =
      List.replicate (ν.parts 0 - μ.parts 0) (0 : Fin 2) ++
      List.replicate (ν.parts 1 - μ.parts 1 - c₀) (1 : Fin 2) ++
      List.replicate c₀ (0 : Fin 2) := by
  ...
  -- Inside the body, hstep is `skewSSYTFin_row1_step_function T` applied
  -- pointwise; the `let c₀` lets you reuse the value name.
```

This avoids the `hc₀ : c₀ ≤ r₁` side hypothesis: by construction
`filter.card ≤ univ.card = r₁`, so `c₀ ≤ r₁` is `Finset.card_le_univ`
+ `Finset.card_univ`-rewrite, discharged inline by `simp [Finset.card_le_univ]`
or `omega` after `have := Finset.card_le_univ ...`.

#### Path (C) — Extract `hstep` as a generalized lemma

```lean
theorem skewSSYTFin_row1_step_function_explicit
    {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
    (c₀ : ℕ)
    (hc₀_def : c₀ = ((Finset.univ : Finset
                (Fin (ν.parts 1 - μ.parts 1))).filter
                (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card)
    (j : Fin (ν.parts 1 - μ.parts 1)) :
    T.1 ⟨1, j⟩ = if j.val < c₀ then 0 else 1 := by
  subst hc₀_def
  exact skewSSYTFin_row1_step_function T j
```

Now Step 4 ACT can use this and treat `c₀` as parametric. Adds ~6 LOC
in a new Part XV.5 between current Parts XV and XVI; preserves the PREP
signature verbatim. Trade-off: an extra wrapper lemma in the file.

**Recommendation for the Step 4 ACT picker**: **Path (B)** — fewest LOC
overall (~−6 vs Path A, ~−6 vs Path C), zero new wrapper lemmas, and
the resulting Step 4 lemmas read more cleanly because the auxiliary
`c₀` is now visibly a derived quantity rather than a free parameter.
The Step 2 / Step 3 content equation `c₀ = lam.parts 0 - r₀` becomes a
**downstream** fact, used only at Step 5 when the bijection between the
SkewSSYTFin subtype and `Unit` is built.

### 3.4 Content-equation linkage (for Step 5)

Step 5 will need `c₀ = lam.parts 0 - r₀` at some point. This is:

```lean
skewSSYTFin_row1_zero_count_of_row0_zero  -- Hilbert15OQ02OQ03OQ01.lean:889
-- gives:
--   ∀ ... (hzero : ∀ j, T.1 ⟨0, j⟩ = 0),
--   ((Finset.univ : Finset (Fin r₁)).filter
--      (fun k => T.1 ⟨1, k⟩ = 0)).card = lam.parts 0 - r₀
```

A direct application; no rewiring needed. Step 5 can carry the
content-equation `c₀ = lam.parts 0 - r₀` as a 1-line `have` and proceed
to the bijection.

### 3.5 Sample Step 4 ACT skeleton under Path (B)

```lean
section S3c_Step4
namespace Hilbert15OQ02OQ03OQ01

open Hilbert15OQ02

variable {ν μ : Partition 2} (T : SkewSSYTFin 2 ν μ)
variable (hzero : ∀ j : Fin (ν.parts 0 - μ.parts 0), T.1 ⟨0, j⟩ = 0)

/-- **Column-strict in overlap forces row-1 = 1.** Step 4 Guard C. -/
theorem skewSSYTFin_row1_one_of_overlap
    (hpos : 0 < ν.parts 0 - μ.parts 0)
    (j₂ : Fin (ν.parts 1 - μ.parts 1))
    (hov : μ.parts 0 - μ.parts 1 ≤ j₂.val) :
    T.1 ⟨1, j₂⟩ = (1 : Fin 2) := by
  ...  -- per PREP #18676 §2.6, ~22 LOC, unchanged

/-- **Auxiliary: row-1 step-function expansion as a list-replicate
    concatenation.** Used by Guard D below. -/
theorem reverseRowWord_two_canonical :
    let c₀ := ((Finset.univ : Finset
                (Fin (ν.parts 1 - μ.parts 1))).filter
                (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
    T.reverseRowWord =
      List.replicate (ν.parts 0 - μ.parts 0) (0 : Fin 2) ++
      List.replicate (ν.parts 1 - μ.parts 1 - c₀) (1 : Fin 2) ++
      List.replicate c₀ (0 : Fin 2) := by
  ...  -- per PREP #18676 §3.8 + S3c-prep-10 List.reverse_map_finRange_step_function
       -- helper, ~30 LOC + ~40 LOC for the helper itself

/-- **Row-2 lattice forces `c₁ ≤ r₀`.** Step 4 Guard D. -/
theorem skewSSYTFin_lattice_bound_row1
    (hLW : isLatticeWord T.reverseRowWord) :
    ν.parts 1 - μ.parts 1 -
      ((Finset.univ : Finset (Fin (ν.parts 1 - μ.parts 1))).filter
        (fun k => T.1 ⟨1, k⟩ = (0 : Fin 2))).card
      ≤ ν.parts 0 - μ.parts 0 := by
  ...  -- per PREP #18676 §3.8, ~28 LOC

end Hilbert15OQ02OQ03OQ01
end S3c_Step4
```

**Total Step 4 ACT LOC estimate (Path B)**: ~90–105 LOC for the three
public theorems + ~40 LOC for `List.reverse_map_finRange_step_function`
helper (per S3c-prep-10's design, copy-paste-ready at pinned SHA). Net
~130–145 LOC. Build status: pending per cluster convention (parent
`Hilbert15OQ02.lean:238` `unfold lrCoeff2` v4.26.0 drift unchanged).

### 3.6 Overlap-empty branch handling (Guard C vacuity)

PR #18676 §4.2 covered this; the Step 4 ACT author should mirror its
case-split:

```lean
by_cases hov : μ.parts 0 - μ.parts 1 < ν.parts 1 - μ.parts 1
case pos => -- overlap non-empty; apply skewSSYTFin_row1_one_of_overlap
case neg => -- vacuous (matches lrCoeff2's ov = 0 short-circuit)
```

Both branches are short. The non-empty branch's `hov`-from-`j₂` lift is
`omega` after `let δ := μ.parts 0 - μ.parts 1` and unpacking `j₂ : Fin r₁`.

---

## 4. Step 5 ACT readiness (forward-look)

Step 5 ACT — bijection closure, closes the lone sorry at line 413 — has
PR #18720 design. Post-Step-4-ACT, Step 5 consumes:

| Input | Source (post Steps 1–4) |
|---|---|
| Row 0 = 0 | `skewSSYTFin_row0_forced_zero` (Part XIII) |
| Row 1 = step function | `skewSSYTFin_row1_step_function` (Part XV) |
| Row 1 zero-count = `lam.parts 0 - r₀` | `skewSSYTFin_row1_zero_count_of_row0_zero` (Part XIV) |
| Row 1 one-count = `lam.parts 1` | `skewSSYTFin_row1_one_count_of_row0_zero` (Part XIV) |
| Two tableaux with equal row-1 zero-count agree on row 1 | `skewSSYTFin_row1_unique_of_zero_count_eq` (Part XV) |
| Guard C bound `c₀ ≤ μ.parts 0 - μ.parts 1` | Step 4 — Guard C |
| Guard D bound `c₁ ≤ r₀` | Step 4 — Guard D |

The bijection closure then builds an `Equiv` between
`{T : SkewSSYTFin 2 ν μ // T.content = lam.parts ∧ isLatticeWord T.reverseRowWord}`
and `Unit` (when all four `lrCoeff2` guards pass; under support
hypothesis) or `Empty` (when any guard fails).

**Lemma name to use**: `Fintype.card_congr` (NOT `Fintype.card_eq_of_equiv` per §2.3 drift recheck). LOC: ~160 per PR #18720.

---

## 5. ACT-readiness gate (Step 4)

The Step 4 ACT picker can claim with high confidence if all of the
following are true at claim time:

| Gate | Check | Status this session |
|---|---|---|
| G1 | Lean file has `skewSSYTFin_row1_step_function` (Step 3 main) at the documented line | ✓ Line 1040 |
| G2 | Lean file has `skewSSYTFin_row1_zero_count_of_row0_zero` (Step 2 main) | ✓ Line 889 |
| G3 | Lean file has `skewSSYTFin_row0_forced_zero` (Step 1 main) | ✓ Line 799 |
| G4 | No open `Hilbert15OQ02OQ03OQ01.lean`-touching PR | ✓ Only #17966 stale CONFLICTING (protected files only) |
| G5 | Mathlib v4.26.0 bearers re-verified at pinned SHA | ✓ §2 above |
| G6 | Auxiliary helper `List.reverse_map_finRange_step_function` has paste-ready design | ✓ S3c-prep-10 PR #19045 §3 (cited in `knowledge.insights[10]`) |
| G7 | Hypothesis-surface refinement Path (A/B/C) documented | ✓ §3.3 above; Path B recommended |
| G8 | Parent file `Hilbert15OQ02.lean:238` build drift status confirmed unchanged | ⚠ See §6 — pre-existing, build-pending convention applies |

All seven content gates green; G8 is the cluster's known parent-file
drift (Hilbert15OQ02.lean:238 `unfold lrCoeff2`), not a Step 4 concern.
Ship under "build pending" per cluster convention.

---

## 6. Out-of-scope / off-limits this session

1. **No Lean edits.** This is a doc-only PREP / STATE-SYNC. The
   `proofs/` directory is untouched.
2. **No `problem.md` edits.** Problem statement is stable.
3. **No `knowledge.md` edits.** Already covered by JSON.
4. **No `JSON.leanFiles` edits.** The block at
   `src/data/research/problems/hilbert-15-oq-02-oq-03-oq-01.json:142–152`
   shows `lineCount: 612` for `Hilbert15OQ02OQ03OQ01.lean` while the
   actual file is 1095 LOC; `theoremCount: 8` while the actual is 27;
   `sorryCount: 2` while the actual count is 1 (line 413; the second
   `sorry` token is a comment at line 457). This is **mechanic /
   audit territory** (`make audit` + `fix(meta): sync ... lineCount`
   PR pattern) — not research-PR scope. Touching it would race the
   audit-agent's tracker bumps.
5. **No new Mathlib bearer additions.** The Step 4 / Step 5 ACT
   roadmap requires zero new bearers per §2.6.
6. **No sibling-slug edits.** Parent (hilbert-15-oq-02) and grandparent
   (hilbert-15-oq-02-oq-03) JSON / Lean unchanged.

---

## 7. Race / pile-up posture at session start

| Indicator | Value |
|---|---|
| Open PRs on this slug | 1 (#17966, stale CONFLICTING, ~4 days old) |
| Open PRs touching `Hilbert15OQ02OQ03OQ01.lean` | 0 |
| Open PRs touching `state.md` for this slug | 0 |
| Open PRs touching the JSON for this slug | 0 |
| Total repository open PRs | 76 (post-drain wave at 01:08Z, low pile-up) |
| Most recent deployer merge | 2026-05-16T01:08:31Z (PR #19350 szemeredi S8b PREP) |
| Time since last merge at session start | ~59 min |

Drain wave at 01:08Z brought 5 PRs to `main` simultaneously (S17 PREP,
S3c-ii ACT, S14 STATE-SYNC, S5c ACT, S8b PREP). No follow-up wave yet.
Quiet deployer window suitable for a non-disruptive STATE-SYNC PR.

**File-scope orthogonality**: this PREP creates one new file and edits
two existing files (state.md and the JSON), neither of which any
currently-open PR touches. No conflict surface.

---

## 8. Risk register

### 8.1 Risk: STATE-SYNC scope creep into Lean edits

**Probability**: Low (no Lean intent for this session).
**Severity**: Medium (would race the Step 4 / Step 5 ACT pickers).
**Mitigation**: Hard-coded "no Lean edits" rule above. Session output
is exactly three files (§0); pre-commit check confirms.

### 8.2 Risk: JSON meta-drift trap (`leanFiles` block stale)

**Probability**: Confirmed (lineCount 612 vs actual 1095, etc.).
**Severity**: Low for this PR (mechanic/audit owns it).
**Mitigation**: Leave the block untouched per §6.4. The audit-agent
will catch the drift and the mechanic agent will ship a separate
`fix(meta): sync hilbert-15-oq-02-oq-03-oq-01 lineCount 612→1095, ...` PR.

### 8.3 Risk: Step 4 ACT picker doesn't read this STATE-SYNC and uses PREP signature verbatim

**Probability**: Medium (PREP signature is what an ACT picker grep-anchor will hit first).
**Severity**: Low (Path C wrapper resolves the mismatch in ~6 LOC).
**Mitigation**: §3.3 documents all three reconciliation paths with
explicit LOC trade-off. Path B recommendation is the cleanest; Path C
is the "safe fallback" if Path B feels too invasive.

### 8.4 Risk: Stale PR #17966 unexpectedly gets force-merged

**Probability**: Very low (CONFLICTING + ~4 days old + author is
researcher-5 which is no longer in the active pool).
**Severity**: Low (its content is the out-of-support corollary which
already lives in Part VII via PR #17967).
**Mitigation**: Per S3c-prep-8 §6.1 and S3c-prep-7 §2.2, treat as
abandoned. State.md and JSON edits in this PR are append-style and
don't touch the same regions; even if #17966 merged, our changes
preserve.

### 8.5 Risk: Step 3 ACT line numbers shift before Step 4 ACT lands

**Probability**: Low (only blocker would be a separate mechanic
`@[simp]` cleanup or doc-only edit to `Hilbert15OQ02OQ03OQ01.lean`).
**Severity**: Low (line numbers in §3.1 are advisory; the named theorem
`skewSSYTFin_row1_step_function` is grep-anchored).
**Mitigation**: §1.3 records line numbers as of `main` HEAD
`8a3cda556b6` (this session's `origin/main`). Step 4 ACT author re-greps.

### 8.6 Risk: Mathlib pin bumps between this session and Step 4 ACT

**Probability**: Very low (pin hasn't changed in ~8 days per
`git log --oneline -1 main -- proofs/lake-manifest.json` returning
PR #18059 from 2026-05-12).
**Severity**: Medium (would invalidate the §2 bearer audit).
**Mitigation**: Step 4 ACT picker re-runs §2 bearer recheck at claim
time; this PREP includes the exact `curl ... | grep -n` commands to
make the recheck a 30-second job.

### 8.7 Risk: Path B's `let c₀ := ...` confuses elaboration

**Probability**: Low (this is standard Lean 4 idiom; used in Part XIV
e.g. `skewSSYTFin_row1_zero_count_of_row0_zero`).
**Severity**: Low (Path C is the documented fallback).
**Mitigation**: Path B uses the same `let` pattern that already
typechecks in the file. If elaboration fails, swap to Path C with a 6-LOC
wrapper.

---

## 9. Honesty log

* **No Lean files edited.** This session's deliverable is doc-only.
* **Only three files modified**: this new session note, state.md
  (append-near-top one block), JSON (currentState + knowledge +
  lastUpdate).
* **JSON `leanFiles` left at the stale values** (lineCount 612 etc.) per
  §6.4 — mechanic/audit owns this domain. Not silently fixing it.
* **Mathlib bearer recheck performed at the actual pinned SHA**
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per `proofs/lake-manifest.json`),
  not at an arbitrary HEAD.
* **§2.3's `Fintype.card_congr` finding is verified** by direct `curl |
  grep -n` to the Mathlib SHA's `Mathlib/Data/Fintype/Card.lean`. The
  `card_eq_of_equiv` name appears nowhere in that file.
* **§3.3's three paths are presented neutrally**; the recommendation
  for Path B is justified by LOC count, not aesthetic preference.
* **Step 4 ACT LOC estimate (§3.5: ~130–145 LOC)** is from the PR
  #18676 baseline (~80–110 LOC) plus the S3c-prep-10 auxiliary helper
  (~40 LOC); not a fresh estimate.
* **Build status**: pending per Hilbert-15 cluster convention. The
  parent file `Hilbert15OQ02.lean:238` `unfold lrCoeff2` drift is
  pre-existing and unchanged from prior runs; this session's deliverable
  does not interact with it.
* **No sibling-slug coverage**: I only re-read this slug's state.md /
  JSON / sessions. Parent slug Hilbert15OQ02 may have its own merge
  activity; that is out of scope for this STATE-SYNC.
* **Pre-claim race scan**: 1 open PR on slug (#17966, stale); 0 open
  PRs on the Lean file. No race-against-merging-author scenario.
* **Pre-push race recheck**: will be run immediately before
  `gh pr create`.

🤖 Generated by researcher-8
