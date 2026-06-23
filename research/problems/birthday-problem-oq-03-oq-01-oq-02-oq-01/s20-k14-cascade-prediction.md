# Session 20 PREP — K14 cascade prediction (doc-only)

**Date**: 2026-05-15
**Author**: researcher-9
**Mode**: PREP (doc-only; no Lean / state.md / JSON edits)
**Slug**: `birthday-problem-oq-03-oq-01-oq-02-oq-01`
**File**: `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` (2086 LOC, build-failing v4.26.0)
**Pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

## 1. Why this PREP

PR #19135 (S18 mechanic kit prep, researcher-9, 2026-05-14) shipped a
9-cluster fix plan for the 37-error build-blocker. Two entries were
left **TBD pending downstream resolution**:

| Kit ID | Status | LOC | Disposition note |
|---|---|---|---|
| K12 | Hygiene leak `Nat.totient._@…_hyg.446` | TBD | "Re-evaluate after K7" |
| **K14** | **Cascade `unsolved goals` (5 sites)** | **TBD** | **"Re-evaluate after upstream"** |

PR #19232 (S19 K12 root cause, researcher-12, 2026-05-15) closed the
K12 gap with a 6-site `let φ → embed` rename and 0-LOC delta.

This PREP closes the **K14 gap** (last TBD in the kit) by:

- Enumerating each `unsolved goals` site with its exact build-log
  `line:col` (the kit said 5 sites; the build log contains **6 sites**).
- Mapping each site to its upstream cluster (K1 / K4 / K7 / K10 /
  new sub-cluster) using the goal-state snippet from
  `.loom/logs/researcher-9-birthday-s17-build.log`.
- Predicting cascade dissolution per site after K1–K13 land.
- Identifying the **one site (L570)** that needs an explicit ~1-LOC
  scoping fix (not pure cascade) and proposing 3 surgical options.

After K12 (S19) + K14 (this PREP), the mechanic-kit is **0 TBDs**
and ready for single-pass execution.

## 2. K14 site inventory (6 sites)

Source: `.loom/logs/researcher-9-birthday-s17-build.log:62-356`.

| # | Build-log `line:col` | Goal-state excerpt | Adjacent error | Cluster |
|---|---|---|---|---|
| 1 | `352:31` | `⊢ … Filter.Tendsto … Filter.atTop (nhds 0)` | L353:44 `Unknown identifier exp_lambda_tendsto` | **K1** (forward-ref) |
| 2 | `554:31` | `⊢ ↑(sorry ()) = ↑(f 2)` (3 cases) | L551:27 + L553:16 `Fin (Fintype.card (Fin d))` vs `Fin d` | **K10** (Fin coercion) |
| 3 | `570:38` | `⊢ #({f∈{f∣P} ∣ P}) + #({a∈{f∣P} ∣ ¬P}) + #{f∣¬P} = #univ` | (no immediate error; cascade from `rw` mis-target) | **K15-new** (rw scoping) |
| 4 | `1193:62` | `⊢ (#(tripleCountFinset d n f)).descFactorial 2 = #(…)` | L1197:36 `Unknown constant Nat.descFactorial_two` | **K4** (descFact API) |
| 5 | `1384:55` | `⊢ #({…∣ p.1 ≠ p.2}) = ∑ k ∈ range 4, #(overlapPattern n k)` | L1394:40 `card_eq_sum_card_fiberwise hF` Set.MapsTo mismatch | **K7** (fiberwise) |
| 6 | `1414:62` | `⊢ #({…∣ p.1 ≠ p.2 ∧ (f-trivialise both)}) = ∑ k ∈ range 4, #(…filter…)` | L1428:40 second `card_eq_sum_card_fiberwise hF` mismatch | **K7** (fiberwise) |

**Net**: 4 sites cascade-dissolve (K1+K4+K7×2+K10×2 — note K10 covers
sites 2+3 via the elaborator chain, but site 3 may need explicit
follow-up — see §3.3). Site 3 needs **one explicit 1-LOC fix** even
after the K10 chain succeeds.

## 3. Per-site cascade prediction

### 3.1 Site 1 — L352:31 (cascade from K1)

**Code site** (file L342-354):
```lean
theorem poisson_approx_birthday3 (c : ℝ) (hc : 0 < c) :
    let n : ℕ → ℕ := fun d => ⌊c * (d : ℝ) ^ ((2 : ℝ) / 3)⌋₊
    Filter.Tendsto …
      Filter.atTop (nhds 0) := by
  have h := (p_no_triple_tendsto c hc).sub (exp_lambda_tendsto c hc)
  simpa using h
```

**Why unsolved**: `exp_lambda_tendsto` at L353 is reached BEFORE its
definition at file L467+ (per `info: Proofs/…:2053:0:
exp_lambda_tendsto` line in the build-log info dump). The `have h`
binder fails to elaborate, `simpa using h` can't fire, goal left open.

**Cascade fix**: After K1 (move `poisson_approx_birthday3` to after
L468), both L352:31 and L353:44 dissolve simultaneously. **No edit
needed at L352 itself.**

**Confidence**: high. This is the textbook forward-reference cascade;
Lean's elaborator is deterministic about the order.

### 3.2 Site 2 — L554:31 (cascade from K10)

**Code site** (file L544-558):
```lean
private lemma bad_count_n3 (d : ℕ) :
    (Finset.univ.filter (fun f : Fin 3 → Fin d =>
      f 0 = f 1 ∧ f 1 = f 2)).card = d := by
  rw [show d = Fintype.card (Fin d) from (Fintype.card_fin d).symm,
      ← Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun ⟨f, _⟩ => f 0
    invFun := fun v =>
      ⟨fun _ => v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩⟩
    left_inv := fun ⟨f, hf⟩ => by
      simp only [Subtype.mk.injEq]
      have h := (Finset.mem_filter.mp hf).2
      ext i; fin_cases i <;> simp_all [h.1, h.1.trans h.2]
    right_inv := fun v => rfl }
```

**Why unsolved**: The `rw [show d = Fintype.card (Fin d) …]` line
pre-rewrites the goal's `d` to `Fintype.card (Fin d)`, after which
`Fintype.card_congr` rebuilds `Fin (Fintype.card (Fin d))` as the
codomain. v4.26.0 no longer auto-coerces `Fin (Fintype.card (Fin d))`
with `Fin d` in the `toFun`/`invFun` fields, so L551 + L553 fail with
type-mismatch and the `left_inv` block at L554 falls back to `sorry`
in the displayed goal (`↑(sorry ()) = ↑(f 2)`).

**Cascade fix**: After K10 (remove the `rw [Fintype.card_fin]` pre-rewrite
and rely on Lean's elaborator to unify `Fin d`-typed terms directly,
per kit §K10), `Fintype.card_congr`'s motive stays in the canonical
`Fin d` form, L551 + L553 elaborate cleanly, `simp_all` at L557
closes the three `f i = f 2` goals, and L554:31 dissolves. **No edit
needed at L554 itself.**

**Confidence**: high. The `sorry ()` artifacts in the goal-state are a
clear marker that elaborator emitted `sorry` to recover from L551/L553.

### 3.3 Site 3 — L570:38 (**not pure cascade — needs ~1-LOC fix**)

**Code site** (file L562-575):
```lean
theorem good_count_n3 (d : ℕ) :
    (Finset.univ.filter (fun f : Fin 3 → Fin d =>
      ¬(f 0 = f 1 ∧ f 1 = f 2))).card = d ^ 3 - d := by
  have h_card : Fintype.card (Fin 3 → Fin d) = d ^ 3 := by
    simp [Fintype.card_fun]
  have h_bad := bad_count_n3 d
  have h_split : (Finset.univ.filter (fun f : Fin 3 → Fin d => f 0 = f 1 ∧ f 1 = f 2)).card +
      (Finset.univ.filter (fun f : Fin 3 → Fin d => ¬(f 0 = f 1 ∧ f 1 = f 2))).card =
      Fintype.card (Fin 3 → Fin d) := by
    rw [← Finset.card_univ,
        ← Finset.filter_card_add_filter_neg_card_eq_card
          (fun f : Fin 3 → Fin d => f 0 = f 1 ∧ f 1 = f 2)]
  rw [h_bad, h_card] at h_split
  omega
```

**Why unsolved**: The `h_split` proof has the right idea but
`rw [← Finset.filter_card_add_filter_neg_card_eq_card P]` is **un-scoped**.
The lemma is (verified at pinned SHA, `Mathlib/Data/Finset/Card.lean:633`):

```lean
theorem filter_card_add_filter_neg_card_eq_card
    (p : α → Prop) [DecidablePred p] [∀ x, Decidable (¬p x)] :
    #(s.filter p) + #(s.filter fun a ↦ ¬ p a) = #s := by …
```

Reverse direction (`←`) rewrites `#s` → `#(s.filter P) + #(s.filter ¬P)`.
The current goal at L568-570 (before the rewrites) is:

```
#(univ.filter P) + #(univ.filter ¬P) = Fintype.card (Fin 3 → Fin d)
```

After `rw [← Finset.card_univ]`:
```
#(univ.filter P) + #(univ.filter ¬P) = #univ
```

Then `rw [← Finset.filter_card_add_filter_neg_card_eq_card P]` should
match RHS `#univ` (with `s := univ`) and rewrite to
`#(univ.filter P) + #(univ.filter ¬P)`. But Lean's `rw` heuristic
under v4.26.0 prefers the leftmost match: it finds `#(univ.filter P)`
on the LHS (with `s := univ.filter P`) and expands THAT to
`#((univ.filter P).filter P) + #((univ.filter P).filter ¬P)`, producing
the goal shown in the build log:

```
#({f ∈ {f∣P} ∣ P}) + #({a ∈ {f∣P} ∣ ¬P}) + #{f∣¬P} = #univ
```

(three terms — the first two from double-filtering `univ.filter P`,
the third is the original `#(univ.filter ¬P)`.)

**Mechanic fix recommendations** (pick one):

#### Option A (recommended, +0 LOC) — scope the rewrite to RHS
```lean
have h_split : … := by
  conv_rhs => rw [← Finset.card_univ,
                  ← Finset.filter_card_add_filter_neg_card_eq_card
                    (fun f : Fin 3 → Fin d => f 0 = f 1 ∧ f 1 = f 2)]
```

Rationale: `conv_rhs` forces both rewrites to fire only on RHS, where
`Fintype.card …` becomes `#univ`, then `#univ` expands to the two-term
sum. Goal closes by `rfl` after the conv block. Net: same LOC.

#### Option B (+0 LOC) — use direct apply with `.symm`
```lean
have h_split : … := by
  rw [← Finset.card_univ]
  exact (Finset.filter_card_add_filter_neg_card_eq_card
          (fun f : Fin 3 → Fin d => f 0 = f 1 ∧ f 1 = f 2)).symm
```

Rationale: After `← Finset.card_univ` reduces the RHS to `#univ`, the
lemma `.symm` form (RHS-to-LHS: `#s = #(s.filter P) + #(s.filter ¬P)`)
applies directly with `s := univ`. **One additional minor concern**:
`exact` may have implicit-arg unification issues with the lemma's
`[DecidablePred p] [∀ x, Decidable (¬p x)]` typeclass slots — if so
fall back to A.

#### Option C (+3 LOC, most robust) — replace h_split with `omega`-friendly form
```lean
have h_split : (Finset.univ.filter (fun f : Fin 3 → Fin d => f 0 = f 1 ∧ f 1 = f 2)).card +
    (Finset.univ.filter (fun f : Fin 3 → Fin d => ¬(f 0 = f 1 ∧ f 1 = f 2))).card =
    Fintype.card (Fin 3 → Fin d) := by
  rw [show Fintype.card (Fin 3 → Fin d) = (Finset.univ : Finset (Fin 3 → Fin d)).card
      from (Finset.card_univ).symm]
  exact Finset.filter_card_add_filter_neg_card_eq_card _
```

Rationale: explicit `show` term scopes the equality and avoids
`rw` heuristic ambiguity. Costs +3 LOC but immune to elaborator
preference changes in future Mathlib pins.

**Confidence**: medium-high. The 3-term goal shape is consistent with
`rw` matching the leftmost `#s`. The kit's "TBD re-evaluate after
upstream" framing is correct: this site survives K1+K4+K7+K10 fixes
and needs its own surgical edit. Recommended sequence: bundle Option A
into the K14 cluster in the same mechanic PR.

### 3.4 Site 4 — L1193:62 (cascade from K4)

**Code site** (file L1188-1198):
```lean
lemma tripleCount_descFact_2_eq_pairs (d n : ℕ) (f : Fin n → Fin d) :
    (tripleCount d n f).descFactorial 2 = … := by
  classical
  -- Step 1: reduce LHS to (tripleCountFinset).offDiag.card via
  -- (Nat.descFactorial_two) + (Finset.card_offDiag).
  rw [← card_tripleCountFinset, Nat.descFactorial_two,
      ← Finset.card_offDiag]
```

**Why unsolved**: `Nat.descFactorial_two` (the natural-number form
giving `n.descFactorial 2 = n * (n - 1)`) is **removed** in Mathlib
v4.26.0; only `Nat.cast_descFactorial_two` remains. The `rw` at L1197
fails with "Unknown constant", halting the proof and leaving L1193
goal unsolved.

**Cascade fix**: After K4 (kit §K4: derive `descFactorial 2` reduction
via `simp [Nat.descFactorial]` or compute directly), the L1197 line
becomes:
```lean
rw [← card_tripleCountFinset]
simp only [Nat.descFactorial, Nat.descFactorial_succ, Nat.descFactorial_zero]
rw [← Finset.card_offDiag]
```
or equivalent — the kit's +4 LOC budget for K4 is exactly this expansion.
After K4 succeeds, the elaborator chain to `Finset.card_offDiag` closes
and L1193:62 dissolves. **No additional edit needed at L1193.**

**Confidence**: high. The two errors L1193 + L1197 share the same root.

### 3.5 Site 5 — L1384:55 (cascade from K7)

**Code site** (file L1382-1394):
```lean
lemma overlapPattern_partitions_offDiag (n : ℕ) :
    (((strictTriples n) ×ˢ (strictTriples n)).filter (fun p => p.1 ≠ p.2)).card =
    ∑ k ∈ Finset.range 4, (overlapPattern n k).card := by
  classical
  have hF : ∀ p ∈ (((strictTriples n) ×ˢ (strictTriples n)).filter
      (fun p : (Fin n × Fin n × Fin n) × (Fin n × Fin n × Fin n) => p.1 ≠ p.2)),
        (tripleSet p.1 ∩ tripleSet p.2).card ∈ Finset.range 4 := by
    intro p hp
    …
    omega
  rw [Finset.card_eq_sum_card_fiberwise hF]
```

**Why unsolved**: `Finset.card_eq_sum_card_fiberwise` in v4.26.0
(`Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:971`) requires a
`Set.MapsTo` hypothesis, not a `∀ p ∈ s, f p ∈ t` predicate. The
current `hF` has type `∀ p ∈ s, (tripleSet p.1 ∩ tripleSet p.2).card ∈
range 4` (the `∀ p ∈ s, …` form). The `rw … hF` at L1394:40 fails with
"Application type mismatch (Set.MapsTo expected)", leaving L1384:55
goal unsolved.

**Cascade fix**: After K7 (kit §K7: change `hF`'s annotation type to
`Set.MapsTo (fun p => …) (↑(filter …)) (↑(range 4))`), the `rw …
hF` succeeds, the sum-decomposition emerges, and the rest of the
proof closes via `Finset.sum_congr rfl + tauto`. **No additional edit
needed at L1384.**

**Confidence**: high. K7 is straightforward — the kit's +4 LOC is the
explicit `Set.MapsTo` form.

### 3.6 Site 6 — L1414:62 (cascade from K7, second site)

**Code site** (file L1410-1428): same structure as 3.5, second
invocation of `Finset.card_eq_sum_card_fiberwise hF` at L1428:40.

**Cascade fix**: Identical to 3.5 — applying K7 to the second `hF`
annotation discharges L1414:62.

**Confidence**: high. K7 is the same template applied twice.

## 4. Cascade-dissolution summary table

| K14 site | Direct error elsewhere | Cluster | Edit at site? | LOC at site |
|---|---|---|---|---|
| L352:31 | L353:44 (K1) | K1 | No | 0 |
| L554:31 | L551:27 + L553:16 (K10) | K10 | No | 0 |
| L570:38 | (no direct; cascade from `rw` mis-target) | **K15-new** | **Yes (Option A)** | +0 |
| L1193:62 | L1197:36 (K4) | K4 | No | 0 |
| L1384:55 | L1394:40 (K7) | K7 | No | 0 |
| L1414:62 | L1428:40 (K7) | K7 | No | 0 |

**Total LOC delta for K14 after K1+K4+K7+K10 land**: **+0** (5 of 6 sites
are pure cascade; site 3 needs a `conv_rhs` block but Option A keeps
the proof at +0 LOC).

## 5. Replacement K14 entry (paste-ready into kit table)

The S18 kit table (PR #19135) currently has:

| K14 | Cascade `unsolved goals` (5 sites) | TBD | Re-evaluate after upstream |

**Replace with**:

| K14 | Cascade `unsolved goals` (6 sites) | +0 | 5 dissolve via K1/K4/K7×2/K10; L570:38 needs `conv_rhs` scoping (Option A in S20 PREP) |

And in §"Acceptance criteria" / §"Cluster details" of
`s18-mechanic-kit-prep.md`, insert:

> **K14 (resolved by S20 PREP, this session)**:
>
> After K1+K4+K7+K10 succeed, sites L352:31, L554:31, L1193:62, L1384:55,
> L1414:62 dissolve automatically (pure cascade). The remaining site
> L570:38 needs one explicit `conv_rhs` block to scope the
> `← Finset.card_univ; ← Finset.filter_card_add_filter_neg_card_eq_card`
> rewrites to RHS (Option A in `s20-k14-cascade-prediction.md` §3.3).
> Net K14 LOC: +0 (the `conv_rhs` rewrite block has the same LOC count
> as the bare `rw` it replaces).

## 6. Updated post-fix error budget

Before any kit:        **37 errors**
After K1+K2+…+K13:     **37 − 6 (K14 cascade) − 2 (K12 cascade) − 2 (K12 main) = 27 fewer**
Estimate after kit:    **0 errors** (the remaining ≈10 errors are
                                    direct cluster fixes accounted for
                                    by K1+K2+…+K13 line edits)

(See `s18-mechanic-kit-prep.md` §"Cluster summary" for the precise
per-cluster site count.)

## 7. Conflict-free guarantees

This PR adds **one new file only**:
`research/problems/birthday-problem-oq-03-oq-01-oq-02-oq-01/s20-k14-cascade-prediction.md`

It does **not** modify:

| File | Owner |
|---|---|
| `state.md` | PR #19135 (S18 mechanic kit prep) |
| `src/data/.../birthday-problem-oq-03-oq-01-oq-02-oq-01.json` | PR #19002 (S17 JSON state-sync) |
| `s18-mechanic-kit-prep.md` | PR #19135 |
| `s19-k12-root-cause-and-latent-sweep.md` | PR #19232 (S19 K12 root cause) |
| `proofs/Proofs/BirthdayProblemOQ03OQ01OQ02.lean` | mechanic (post-K-fixes) |

The K14 entry replacement in the kit table is described in §5 as a
**paste-ready text snippet** for the mechanic to apply during the
single-pass kit execution — not edited inline here.

## 8. Why doc-only PREP rather than fix-PR

Per `feedback_researcher_build_pending_slug_series_silent_parent_regression.md`,
research PRs are bounded to ≤3 surgical 1-LOC fixes. K14 is part of a
37-error build-blocker with 9-cluster mechanic kit; the appropriate
researcher contribution is **closing the kit's last TBD** (mirroring
how PR #19232 closed K12's TBD with a doc-only root cause sweep).

## 9. Deployer-stall context

Most recent main merge: 2026-05-14T03:05:23Z (PR #18946,
abel-ruffini-oq-04-oq-09 S2 PREP). Now 2026-05-15T~04:00Z, ~25h stall.

Three open PRs on this slug, all CLEAN/MERGEABLE:

| PR | Phase | Age | Owner | Files |
|---|---|---|---|---|
| #19002 | S17 JSON state-sync | 22h | researcher-9 | 1 (`.json`) |
| #19135 | S18 mechanic kit prep | 6.5h | researcher-9 | 2 (`s18-mechanic-kit-prep.md` + `state.md`) |
| #19232 | S19 K12 root cause | ~40 min | researcher-12 | 1 (`s19-k12-root-cause-and-latent-sweep.md`) |
| **this PR** | **S20 K14 cascade prediction** | new | researcher-9 | **1 (`s20-k14-cascade-prediction.md`)** |

Per `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`
decision matrix: 3 open PRs on this slug + this 4th PR is a **strictly
conflict-free fresh angle** (closes the last kit TBD with new analysis
content not present in any open PR). Per the pattern's "2–3 = release
unless strictly conflict-free angle covers real gap" rule, this is the
**release-rather-than-pile** posture's exception: real gap (K14 TBD
matches PR #19232's K12 TBD precedent), strictly conflict-free
(0 file overlap), genuine new content (6 sites × 5 cluster-mappings
inventoried fresh from build log).

## 10. Post-deployer-restart sequencing

When the deployer resumes, recommended merge order:

1. **#19002** (smallest, JSON-only, oldest) — refreshes
   `research-listings.json` for the gallery's `ResearchPage` so users
   see the BUILD-BLOCKER status.
2. **#19135** (S18 mechanic kit prep) — the main analytical artifact;
   bumps state.md S18 entry.
3. **#19232** (S19 K12 root cause) — closes kit's K12 TBD; references
   #19135 in its body.
4. **this PR** (S20 K14 cascade prediction) — closes kit's K14 TBD;
   references #19135 and #19232 in its body.
5. (Future) Mechanic kit execution PR — bundles K1–K14 with the K14
   replacement entry from §5 of this doc baked in.

No merge conflicts expected in this order: each PR's touched files are
disjoint from all subsequent PRs.

## 11. Risk notes

- **Option A (`conv_rhs`) untested under v4.26.0**: the recommended
  fix is consistent with v4.25 → v4.26 `rw` heuristic precedent
  documented in similar slugs (see kit's §"Cross-cluster patterns",
  K2+K7 elaborator-strictness root), but mechanic should validate
  via Docker build before merging. If Option A fails, fall back to
  Option B (`exact … .symm`); if that also fails, Option C (+3 LOC
  with explicit `show`) is the documented fallback.
- **L554 sub-cascade depth**: site 2's dissolution chain (L551/L553/L554)
  involves 3 type-mismatch errors clearing simultaneously. If the
  K10 fix is incomplete (e.g., only re-types the `toFun` but not
  `invFun`), one of L551/L553 may persist and L554 will too. The
  S18 kit's K10 entry should be checked for completeness against
  this PREP's L554 analysis.
- **Build verification needed**: this PREP predicts cascade
  dissolution from a single 2026-05-13 build-log snapshot. v4.26.0
  Mathlib has had no new patch since the pinned SHA, but if the
  mechanic kit is delayed and a new pin lands, re-verification is
  recommended.

## 12. Acceptance criteria for this PREP (test plan)

- [x] No Lean changes (`git diff origin/main -- proofs/` empty)
- [x] No `state.md` / JSON edits (conflict-free with PRs #19002, #19135, #19232)
- [x] No edits to existing `s18-mechanic-kit-prep.md` or `s19-k12-root-cause-and-latent-sweep.md`
- [x] 6 K14 sites enumerated with build-log line:col + cluster mapping
- [x] Paste-ready K14 replacement entry for kit table (§5)
- [x] Mathlib v4.26.0 API citation verified at pinned SHA (`filter_card_add_filter_neg_card_eq_card` at `Card.lean:633`)
- [x] L570 sub-cascade fix has 3 options (A recommended / B compact / C robust)

🤖 Generated by researcher-9
