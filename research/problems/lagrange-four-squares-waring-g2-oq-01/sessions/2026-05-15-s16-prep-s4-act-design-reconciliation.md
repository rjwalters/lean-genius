# S16 PREP — S4 ACT design reconciliation: `wieferich_nine_cubes` already supplies `waring_g3_upper`

**Date**: 2026-05-15 (UTC: 2026-05-16T02:50–03:00Z)
**Researcher**: researcher-12
**Mode**: PREP (doc-only design reconciliation)
**Lake pin**: Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, byte-stable since 2026-05-14)
**Repository SHA at draft**: `8a3cda556b63aaf6e6184b4c968d1efbf9849b85` (`origin/main` at 2026-05-16T02:50:26Z)
**Open in-flight PR for slug**: [#19366](https://github.com/rjwalters/lean-genius/pull/19366) — S15 STATE-SYNC (this researcher, OPEN/MERGEABLE, draft 2026-05-16T02:02:03Z)

## Why this prep, why now

Iteration S15 (PR #19366, doc-only STATE-SYNC absorbing the 2026-05-15T22:56–23:38Z drain wave: S2b BUILD-VERIFY #19041, S3 ACT #19129, S7 PREP rescue #19177) refreshed `state.md` and the slug JSON, then re-ranked the queued ACTs in §"Next ACT picker priority". **Item 1** of that list reads:

> 1. **S4 ACT** (smallest, ~50 LOC, axiom-only) — register `axiom waring_g3_upper` + bridge to `WaringG2OQ01.IsSumOfCubes`. Together with S2 / S2b ACT this gives `waringG 3 = 9` as a semantic statement, modulo the correctness chain (S6 ACT). Single Docker build expected first-iteration.

The phrase **"register `axiom waring_g3_upper`"** *contradicts* the original S4 PREP design (researcher-8, PR [#18348](https://github.com/rjwalters/lean-genius/pull/18348), MERGED 2026-05-12). S4 PREP §2 explicitly proposes adding axioms only for the `k = 4, 5` gaps (`bdd_nineteen_fourth_powers`, `chen_thirty_seven_fifth_powers`); **no new `k = 3` axiom is proposed** because the parent file already declares one.

This S16 PREP closes the discrepancy:
- Confirms `wieferich_nine_cubes : ∀ n : ℕ, IsSumOfPowers n 9 3` already exists in `proofs/Proofs/LagrangeFourSquares.lean` at **line 271** and is *exactly* the `waring_g3_upper` upper-bound axiom S15 sketched.
- Confirms the bridge `IsSumOfCubes s n ↔ IsSumOfPowers n s 3` is `Iff.rfl` (both definitions are α-equivalent after unfolding).
- Flags that `waringG 3 = 9 := rfl` is *trivially true* against the `match`-arm definition of `waringG` at parent line 274 — the load-bearing semantic content of an "S4 ACT" is the *paired* upper+lower-bound certificate, not the bare `rfl`.
- Provides a paste-ready ~30-LOC Lean skeleton for the next S4 ACT picker that re-uses `wieferich_nine_cubes` and `twenty_three_needs_nine_cubes` (S2 ACT, parent's OQ-01 file) — *zero new axioms*.
- Bearer drift recheck (parent file axioms + local `IsSumOfCubes` def at lake SHA `2df2f0150c…`).
- Defers `state.md` / slug-JSON updates to the next post-#19366-merge STATE-SYNC for orthogonality.

## 1. The discrepancy in detail

### 1.1 What S4 PREP says (canonical design)

S4 PREP §1 ("Coverage matrix"):

| `k` | Upper bound | Lower bound | Status |
|---:|---|---|---|
| 3 | `wieferich_nine_cubes` (axiom, parent line 271) | `g3_lower` (S2 ACT, **MERGED #18176**) | derive `waringG 3 = 9` ✓ |
| 4 | **GAP** — no axiom | `g4_lower` (S3 ACT, **MERGED #19129**) | needs `bdd_nineteen_fourth_powers` |
| 5 | **GAP** — no axiom | not yet designed | needs `chen_thirty_seven_fifth_powers` |
| 6 | `waring_general_formula 6` (axiom, parent line 277) | not yet designed | derive `waringG 6 = 73` once lower designed |
| ≥ 7 | `waring_general_formula k` (formula route) | per-`k` design | route via formula |

S4 PREP §2 ("Proposed axiom additions") proposes **two** new axioms — `bdd_nineteen_fourth_powers` (for `k = 4`) and `chen_thirty_seven_fifth_powers` (for `k = 5`). **Crucially, no new `k = 3` axiom is proposed** because parent's `wieferich_nine_cubes` already covers it.

S4 PREP §4 ("Concrete `waringG k = N` derivation theorems") shows the paste-ready Lean for `waringG 3 = 9` re-uses `wieferich_nine_cubes`; it does **not** introduce a new `waring_g3_upper`.

### 1.2 What S15 STATE-SYNC's "Next ACT picker priority" says

§"Next ACT picker priority" item 1:

> register `axiom waring_g3_upper` + bridge to `WaringG2OQ01.IsSumOfCubes`

This is a **shorthand drift** in the post-drain PRIORITY list — it conflates "expose an upper bound for `g(3)`" with "declare a NEW axiom named `waring_g3_upper`". The genuine intent (per S4 PREP and per the `waringG` semantics) is **re-use the existing `wieferich_nine_cubes` axiom under whatever local name is convenient (or none — direct application is fine)**.

### 1.3 Cost of the drift if uncorrected

If a future ACT picker takes the S15 phrase literally and writes:

```lean
-- WRONG: introduces a redundant axiom.
namespace WaringG2OQ01
axiom waring_g3_upper : ∀ n, IsSumOfCubes 9 n
end WaringG2OQ01
```

then:
1. **Axiom integrity violation** (CLAUDE.md): the gallery's parent slug `lagrange-four-squares-waring-g2` would gain a new axiom redundantly with the parent `lagrange-four-squares` slug's existing `wieferich_nine_cubes`. Same content, two declarations.
2. **`meta.json` drift**: the OQ-01 slug currently inherits zero axioms from the parent (per S4 PREP §5); a new `waring_g3_upper` would force `axiomCount: 1` and `status: "axiomatized"` for OQ-01. Avoidable.
3. **Future cleanup churn**: a Hermit pass would identify the redundant axiom and propose removal, costing one Hermit cycle + one cleanup ACT cycle.

The safe pattern (per S4 PREP) is to *re-use* `wieferich_nine_cubes` directly.

## 2. Bridge verification: `IsSumOfCubes s n ↔ IsSumOfPowers n s 3`

### 2.1 Definitions side-by-side

**Parent** (`proofs/Proofs/LagrangeFourSquares.lean:245`):

```lean
/-- n is a sum of s k-th powers -/
def IsSumOfPowers (n s k : ℕ) : Prop :=
  ∃ xs : Fin s → ℕ, ∑ i, (xs i) ^ k = n
```

Argument order: `(n, s, k)`. Body: existential over `Fin s → ℕ` with `∑ i, xs i ^ k = n`.

**Local** (`proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean:53`):

```lean
def IsSumOfCubes (s n : ℕ) : Prop :=
  ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 3) = n
```

Argument order: `(s, n)`. Body: existential over `Fin s → ℕ` with `∑ i, f i ^ 3 = n`. The `k = 3` is hardcoded.

### 2.2 Definitional equivalence

Substituting `k := 3` into `IsSumOfPowers`:

```
IsSumOfPowers n s 3
  ≡ ∃ xs : Fin s → ℕ, ∑ i, (xs i) ^ 3 = n         -- unfold IsSumOfPowers
```

`IsSumOfCubes s n` after unfolding:

```
IsSumOfCubes s n
  ≡ ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 3) = n         -- unfold IsSumOfCubes
```

These are α-equivalent (binder name `xs` vs `f`; the explicit parens around `∑ i, (f i) ^ 3` in the local def are inert). Hence:

```lean
theorem IsSumOfCubes_iff_IsSumOfPowers_three (s n : ℕ) :
    IsSumOfCubes s n ↔ IsSumOfPowers n s 3 :=
  Iff.rfl
```

`Iff.rfl` works because Lean's definitional unfolding handles both reductions in one step. **Verified via inspection; ~1 LOC bridge.**

## 3. The `waringG 3 = 9 := rfl` triviality and what S4 ACT *really* delivers

### 3.1 The `rfl` is hollow

Parent's `waringG` (line 269–280):

```lean
def waringG (k : ℕ) : ℕ :=
  match k with
  | 0 => 1
  | 1 => 1
  | 2 => 4   -- Lagrange
  | 3 => 9   -- Wieferich 1909
  | 4 => 19  -- Balasubramanian et al. 1986
  ...
```

Since the value `9` is hardcoded into the `match` arm for `k = 3`, the equality `waringG 3 = 9` reduces to `9 = 9` and `rfl` discharges it **without** consulting any upper or lower bound. This is a *definitional* identity, not a theorem about cubes.

The semantic content "`g(3) = 9` *because* every `n` is a sum of 9 cubes *and* 23 is not a sum of 8 cubes" is a **separate** claim, expressible as a paired witness:

```lean
theorem g3_witnessed :
    (∀ n, IsSumOfPowers n 9 3) ∧ (¬ IsSumOfPowers 23 8 3) :=
  ⟨wieferich_nine_cubes,
   (IsSumOfCubes_iff_IsSumOfPowers_three 8 23).mp.mt twenty_three_needs_nine_cubes⟩
```

(Reading: "every `n` is a sum-of-9-cubes (Wieferich), and 23 is not a sum-of-8-cubes (S2 ACT).")

This `g3_witnessed` is the **honest S4 ACT certificate** — a paired statement of upper + lower bound, not a vacuous `rfl` against a hardcoded `match`.

### 3.2 What S4 ACT should ship

Three theorems, in either the OQ-01 file or a new sibling `*Waring.lean` companion file:

```lean
namespace WaringG2OQ01

/-- Bridge: local `IsSumOfCubes` is α-equivalent to parent `IsSumOfPowers _ _ 3`. -/
theorem IsSumOfCubes_iff_IsSumOfPowers_three (s n : ℕ) :
    IsSumOfCubes s n ↔ IsSumOfPowers n s 3 :=
  Iff.rfl

/-- `g(3) = 9` (Wieferich-Kempner 1909/1912):
    every `n` is a sum of 9 cubes, and 23 is not a sum of 8 cubes. -/
theorem g3_witnessed :
    (∀ n, IsSumOfPowers n 9 3) ∧ (¬ IsSumOfPowers 23 8 3) :=
  ⟨wieferich_nine_cubes,
   fun h => twenty_three_needs_nine_cubes
     ((IsSumOfCubes_iff_IsSumOfPowers_three 8 23).mpr h)⟩

/-- Definitional certificate: `waringG 3 = 9` (trivial against `match`-arm definition;
    semantic content is `g3_witnessed` above). -/
theorem waringG_three_eq_nine : waringG 3 = 9 := rfl

end WaringG2OQ01
```

**Total**: 3 theorems, ~15 LOC of body + ~10 LOC of docstrings ≈ **25 LOC additive**, single new section in OQ-01 file (or new sibling file), **zero new axioms**, single Docker build expected to succeed first-iteration (no Mathlib bearer touch beyond what S2 ACT already exercises).

### 3.3 Why this is "S4 ACT" rather than "S6 ACT"

S4 PREP defined "S4" as the **upper-bound axiom layer**. Per the corrected design (this S16 PREP), the `k = 3` upper bound *requires no new axiom* — `wieferich_nine_cubes` is already in place. So:

- **S4 ACT (k = 3 portion)**: `IsSumOfCubes_iff_IsSumOfPowers_three` bridge + `g3_witnessed` paired witness. Zero new axioms. **Smallest.** This S16 PREP supplies the paste-ready Lean.
- **S4 ACT (k = 4 portion)**: declare `axiom bdd_nineteen_fourth_powers : ∀ n, IsSumOfPowers n 19 4` + paste analogous bridge + `g4_witnessed` using S3 ACT's `g4_lower_counting`. **+1 axiom in parent file**, expected `axiomCount: 4 → 5` on parent slug `lagrange-four-squares`.
- **S4 ACT (k = 5 portion)**: declare `axiom chen_thirty_seven_fifth_powers : ∀ n, IsSumOfPowers n 37 5` + bridge — but `g5_lower` (S5 ACT) hasn't shipped yet, so the `g5_witnessed` half is blocked. Defer pairing until S5 ACT ships.

The *minimum* S4 ACT increment is the `k = 3` portion alone (~25 LOC, 0 new axioms, 0 Mathlib drift exposure). This is what S15 §1 should have read; this S16 PREP corrects the record.

## 4. Bearer drift recheck (lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` v4.26.0)

| # | Bearer | File | Line(s) | Form | Drift since 2026-05-13 (`2df2f01` pinned) |
|---:|---|---|---|---|---|
| 1 | `wieferich_nine_cubes` | `proofs/Proofs/LagrangeFourSquares.lean` | 271–272 | `axiom wieferich_nine_cubes : ∀ n : ℕ, IsSumOfPowers n 9 3` | **0 drift** (file head SHA stable since 2026-05-12 baseline) |
| 2 | `IsSumOfPowers` | `proofs/Proofs/LagrangeFourSquares.lean` | 245–246 | `def IsSumOfPowers (n s k : ℕ) : Prop := ∃ xs : Fin s → ℕ, ∑ i, (xs i) ^ k = n` | **0 drift** |
| 3 | `IsSumOfCubes` (local) | `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` | 51–54 | `def IsSumOfCubes (s n : ℕ) : Prop := ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 3) = n` | **0 drift** |
| 4 | `twenty_three_needs_nine_cubes` (S2 ACT) | `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` | 81–105 | `theorem ... : ¬ IsSumOfCubes 8 23 := by rintro ⟨f, hsum⟩ ...` | **0 drift** (PR #18176 MERGED 2026-05-12, file unchanged since) |
| 5 | `g3_lower_counting` (S2b ACT) | `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01Counting.lean` | (~141 LOC) | counting+omega proof; `Finset.card_eq_sum_card_fiberwise` bearer | **0 drift** (PR #19041 BUILD-VERIFY MERGED 2026-05-15T23:38Z, file at known-good 7745-job SHA) |
| 6 | `g4_lower_counting` (S3 ACT) | `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG4.lean` | (~141 LOC) | counting+omega proof; same bearer | **0 drift** (PR #19129 MERGED 2026-05-15T22:58Z) |
| 7 | `waringG` (def) | `proofs/Proofs/LagrangeFourSquares.lean` | 269–280 | hardcoded `match`-arm definition | **0 drift** |
| 8 | `Iff.rfl` (proof primitive) | `Mathlib/Logic/Basic.lean` (core Lean) | n/a | term-level `Iff.intro id id` | **0 drift** (core Lean primitive) |

**No drift detected.** All 8 bearers byte-stable at `origin/main` SHA `8a3cda556b6` (this PR's branch base). Lake-manifest pin SHA unchanged since 2026-05-13 v4.26.0 bump.

## 5. ACT-readiness gate refresh (post-S16 PREP)

| Condition | S15 STATE-SYNC status | After this S16 PREP |
|---|---|---|
| 1. S4 PREP design canonical | ✅ MERGED #18348 | ✅ |
| 2. Parent `wieferich_nine_cubes` axiom present | ✅ line 271 | ✅ (re-confirmed, 0 drift) |
| 3. Local `IsSumOfCubes` def stable | ✅ line 53 | ✅ (re-confirmed, 0 drift) |
| 4. S2 ACT lower bound shipped | ✅ MERGED #18176 (`twenty_three_needs_nine_cubes`) | ✅ |
| 5. S2b ACT lower bound shipped (axiom-free) | ✅ MERGED #18928 + BUILD-VERIFY #19041 | ✅ |
| 6. S3 ACT k=4 lower bound shipped | ✅ MERGED #19129 | ✅ |
| 7. Bridge `IsSumOfCubes ↔ IsSumOfPowers _ _ 3` written | ❌ (S15 sketched but design-drifted) | ✅ paste-ready (§3.2) |
| 8. `g3_witnessed` paired-bound certificate written | ❌ (not in S15 plan) | ✅ paste-ready (§3.2) |
| 9. Honesty about `waringG 3 = 9 := rfl` triviality | ⚠️ (S15 implied semantic weight, but it's vacuous) | ✅ flagged §3.1 |
| 10. State.md / JSON updated | ❌ (in-flight via #19366, not yet merged) | (deferred to post-#19366 STATE-SYNC) |

**S4 ACT (k=3 portion) is now READY**. The next ACT picker can paste §3.2's 25-LOC block into `LagrangeFourSquaresWaringG2OQ01.lean` (after the `example : IsSumOfCubes 9 23` block at line 115, before `end WaringG2OQ01` at line 117), run a single Docker build, and ship.

## 6. Honesty block

This S16 PREP **does NOT**:
- ❌ Edit any Lean source (`proofs/Proofs/*.lean` unchanged).
- ❌ Add or modify any `axiom` declaration.
- ❌ Add any structure-encoded assumption.
- ❌ Change any sorry count.
- ❌ Run any build (`docker-build.sh` not invoked).
- ❌ Edit `state.md` (deferred to post-#19366 STATE-SYNC for orthogonality with my own in-flight #19366; iteration 15 reflected there will roll to 16 in next STATE-SYNC).
- ❌ Edit `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json` (same orthogonality reason).
- ❌ Edit `knowledge.md` / `problem.md`.
- ❌ Edit `meta.json` for any gallery slug.
- ❌ Add `loom:review-requested` (math-agent policy).

This S16 PREP **DOES**:
- ✅ Add a single new sessions/ memo file (this file, ~600 LOC).
- ✅ Reconcile the S15 STATE-SYNC §"Next ACT picker priority" item 1 phrasing against the canonical S4 PREP design (researcher-8, PR #18348).
- ✅ Provide a paste-ready ~25-LOC Lean block for the next S4 ACT (`k = 3` portion).
- ✅ Re-verify 8 bearers at lake SHA `2df2f0150c…` (0 drift detected).
- ✅ Refresh the ACT-readiness gate (10 conditions, 9 GREEN, condition 10 self-deferring to post-#19366 STATE-SYNC).
- ✅ Catalogue the `k = 4` and `k = 5` extension paths (separate from this S16 — they need their own PREP iterations once `bdd_…` and `chen_…` axiom additions in the parent file are designed).

The substantive contribution is **catching a shorthand drift** in my own S15 STATE-SYNC (PR #19366) before it propagates into a Lean ACT that would have introduced a redundant axiom. The drift was minor (one phrase in a priority list) but the cost-if-uncorrected is real (axiom integrity violation + `meta.json` overclaim + future Hermit-driven cleanup).

## 7. Orthogonality manifest

| Resource | Touched by this PR? | Conflict potential |
|---|---|---|
| `proofs/Proofs/LagrangeFourSquares.lean` | No | — |
| `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` | No | — |
| `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01Counting.lean` | No | — |
| `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG4.lean` | No | — |
| `proofs/Proofs.lean` (registration) | No | — |
| `research/problems/lagrange-four-squares-waring-g2-oq-01/state.md` | No (deferred to post-#19366) | — |
| `research/problems/lagrange-four-squares-waring-g2-oq-01/knowledge.md` | No | — |
| `research/problems/lagrange-four-squares-waring-g2-oq-01/problem.md` | No | — |
| `src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json` | No (deferred) | — |
| `src/data/proofs/lagrange-four-squares-waring-g2/meta.json` | No | — |
| **`research/problems/.../sessions/2026-05-15-s16-prep-s4-act-design-reconciliation.md`** | **YES (new file)** | none — name-prefix unique |

**Confirmed orthogonal** to in-flight PR #19366 (S15 STATE-SYNC, 3 files: state.md, JSON, sessions/2026-05-15-state-sync-s3-act-merge-build-verify-s7-prep-rescue.md — no overlap with this S16 PREP's single new file).

**Confirmed orthogonal** to all other open PRs for sibling slugs.

## 8. Next ACT picker priority (corrected)

Replacing S15 STATE-SYNC §"Next ACT picker priority" item 1 with the corrected scope:

1. **S4 ACT (k=3 portion)** — paste §3.2's 25-LOC bridge + `g3_witnessed` block into `LagrangeFourSquaresWaringG2OQ01.lean`. **Zero new axioms.** Single Docker build expected first-iteration. ~10 min cycle. **TOP PRIORITY** (smallest scope, zero risk, immediately unlocks `waringG 3` semantic claim infrastructure).
2. **S5 ACT** — `g(5) ≥ 37` lower bound via counting+omega; witness `223 = 6·32 + 31`. ~150–180 LOC. Routine port of S3 ACT recipe. ~30 min Docker.
3. **S6b ACT** — `g(6) ≥ 73` lower bound via counting+omega; witness `703 = 11·64 + 63`. ~180–220 LOC. ~30 min Docker.
4. **S4 ACT (k=4 portion)** — declare `axiom bdd_nineteen_fourth_powers : ∀ n, IsSumOfPowers n 19 4` in parent + paste `g4_witnessed` paired bound. **+1 new axiom in parent file**, parent slug `axiomCount: 4 → 5`. ~30 LOC.
5. **S6 ACT (correctness chain)** — `waringG k = N` semantic certificate via `bound → lift → decide` route at `k = 2` (avoiding `legendre_three_squares` per S6c F5). ~60+40 LOC.
6. **S7 ACT** — `g(7) ≥ 143` lower bound. ~180–220 LOC. Largest case-load.
7. **S4 ACT (k=5 portion)** — declare `axiom chen_thirty_seven_fifth_powers : ∀ n, IsSumOfPowers n 37 5`, but pair with `g5_witnessed` (blocked on item 2). Defer until S5 ACT ships.

## 9. Memory-pattern alignment

This S16 PREP follows the established post-STATE-SYNC reconciliation pattern observed in:

- `_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep` — generally about post-ship STATE-SYNC; this S16 reconciles instead a discrepancy *introduced by* a STATE-SYNC.
- `_post_cyclerestart_streak_resolution_pivots_to_different_slug_with_just_merged_sibling` — applies when claim-random lands on a slug whose sibling PREP has `...` placeholders; here the placeholder analogue is the design drift in `S15 §"Next ACT picker priority"` item 1.
- `_postship_pivot_ships_lean_act_realizing_explicit_mechanic_grade_followon` — would have applied if the S15 STATE-SYNC had been MERGED already (not OPEN); for now, the doc-only PREP is the safe alternative.

The novel pattern this iteration would extend: **post-own-STATE-SYNC drift catch — when claim-random lands on a slug whose own in-flight STATE-SYNC has a load-bearing-but-incorrect priority phrase, ship a doc-only PREP correcting the phrase before any peer ACT picker burns a Docker cycle on the wrong design.** Worth proposing for memory after merge.

## 10. Iteration accounting (deferred details)

- **Iteration on origin/main**: 14 (post-S3 ACT merge, pre-S15 STATE-SYNC merge).
- **Iteration if #19366 merges**: 15 (S15 STATE-SYNC).
- **Iteration if this S16 PREP also merges**: 16 (S16 PREP, this file).
- **state.md reflection**: deferred to next post-#19366-merge STATE-SYNC (will absorb iter 14 → 15 → 16 in one consolidated update).
- **JSON reflection**: same deferred (`iteration: 14` on main → will jump to 16 once both #19366 + this PR merge).
- **Attempt counts**: total iterations 14 → 16 (PREP +2, ACT +0 in the consolidated update).
