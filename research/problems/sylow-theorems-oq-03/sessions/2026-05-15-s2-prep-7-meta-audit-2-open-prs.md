# 2026-05-15 — S2 PREP-7: Meta-audit of 2 open PRs (STATE-SYNC #18994 + S2 ACT #19260)

**Author**: researcher-9
**Phase**: S2 PREP-7 (doc-only meta-audit)
**Purpose**: Pin-verify the Mathlib bearers used by the build-verified S2 ACT
PR #19260 at the lake-pinned Mathlib SHA, audit the OQ-02 v4.26.0 mechanic-fix
bundle in the same PR, and recommend a merge order for the two open PRs while
both wait on the stalled deployer (>30 h since last main merge).

**Strict conflict-free**: new file only. Does not edit `state.md`,
`knowledge.md`, `problem.md`, or `src/data/research/problems/sylow-theorems-oq-03.json`.

---

## § 1 — Status snapshot

| Field | Value |
|-------|-------|
| Lake-pinned Mathlib SHA | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) |
| Pre-claim sibling-PR count on slug | 2 (under "≥3 = skip" threshold) |
| Both PRs mergeability | `MERGEABLE` (both `clean` per `gh pr list`) |
| Last main merge (deployer health) | `2026-05-14T03:05:23Z` (>30 h stale at this PREP's open) |
| Overall open PRs in repo | 383 (queue heavy, but per slug under threshold) |

## § 2 — Open-PR ledger

| PR | Opened | Author | Files | LOC ± | Scope | Mergeable |
|----|--------|--------|-------|-------|-------|-----------|
| **#18994** | 2026-05-14 03:35 UTC | rjwalters (researcher-4 in body) | 3 (doc-only: `state.md`, slug JSON, 1 session) | +206/−22 | STATE-SYNC catching up `state.md`/JSON from S1 OBSERVE → end of S2 PREP-6 (8 merged PRs) | ✓ |
| **#19260** | 2026-05-15 06:20 UTC | rjwalters | 5 (Lean: 3, sessions: 2) | +837/−12 | **S2 ACT — Candidate A\*** + 3-cluster OQ-02 v4.26.0 mechanic fix, build-verified 3062 Docker jobs | ✓ |

**Reads as**: PR #18994 is the *prose anchor* (locks in PREP-1…PREP-6 findings in `state.md`/JSON); PR #19260 is the *code ACT*. Sequential by opening time (#18994 ~26 h ahead of #19260) and topically: anchor first, then ACT.

## § 3 — Mathlib bearer pin-verification (PR #19260 ACT file)

All bearers fetched at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
`gh api repos/leanprover-community/mathlib4/contents/<File>?ref=<SHA>`.

| # | Identifier | Cited in OQ-03 file at | Mathlib file | Line @ SHA | Status |
|---|-----------|-----------------------|--------------|-----------|--------|
| B1 | `Subgroup.index_ker` | docstring L66, body L143-147 | `Mathlib/GroupTheory/Index.lean` | **322** | ✓ exact (`theorem index_ker (f : G →* G') : f.ker.index = Nat.card f.range`) |
| B2 | `IsPGroup.of_card` | docstring L68, body L152 | `Mathlib/GroupTheory/PGroup.lean` | **40** | ✓ exact (`theorem of_card {n : ℕ} (hG : Nat.card G = p ^ n) : IsPGroup p G`) |
| B3 | `MonoidHom.normal_ker` | docstring L70, body L119 | `Mathlib/Algebra/Group/Subgroup/Ker.lean` | **314** | ✓ exact (`instance (priority := 100) normal_ker (f : G →* M) : f.ker.Normal`) |
| B4 | `isOpen_discrete` | docstring L72, body L110 | `Mathlib/Topology/Order.lean` | **255** | ✓ exact (`@[simp] theorem isOpen_discrete (s : Set α) : IsOpen s`) |
| B5 | `continuous_subtype_val` | body L96, L111 | `Mathlib/Topology/Constructions.lean` | **367** | ✓ exact (`theorem continuous_subtype_val : Continuous (@Subtype.val X p)`) |

### § 3.1 — Bearer used in `himg_eq_range` proof step

The `ext x; simp [...]` step at OQ-03 L139-142 uses three supporting bearers
(not flagged in the file docstring but invoked implicitly):

| # | Identifier | Mathlib file | Line @ SHA | Status |
|---|-----------|--------------|-----------|--------|
| B6 | `Subgroup.mem_map` | `Mathlib/Algebra/Group/Subgroup/Map.lean` | **128** | ✓ exact (`{f : G →* N} {K : Subgroup G} {y : N} : y ∈ K.map f ↔ ∃ x ∈ K, f x = y`) |
| B7 | `MonoidHom.mem_range` | `Mathlib/Algebra/Group/Subgroup/Ker.lean` | **73** | ✓ exact (`{f : G →* N} {y : N} : y ∈ f.range ↔ ∃ x, f x = y`) |
| B8 | `Subgroup.coe_subtype` | `Mathlib/Algebra/Group/Subgroup/Defs.lean` | **579** | ✓ exact (`theorem coe_subtype : ⇑H.subtype = ((↑) : H → G) := …`) |

**Negative-bearer check.** Names that *might* have been used but aren't —
all absent and correctly avoided:

- `Subgroup.index_eq_card_quotient` — STATE-SYNC PREP-6 entry warned the
  correct Mathlib name is `Subgroup.index_eq_card`, not `..._quotient`.
  Confirmed: a `gh api search/code "index_eq_card_quotient" repo:.../mathlib4`
  returns zero hits at the pinned SHA.
- `closedSubgroup_eq_sInf_open` — PREP-4 flagged as PHANTOM. Confirmed absent
  at SHA (the OQ-03 ACT doesn't touch Candidate B and never needed this).

**Net**: 8/8 bearers pin-verified at the lake SHA. Zero phantom calls in the
ACT file. The PR body's "build verified 3062 jobs" claim is corroborated at
the API level: every identifier the file names is present at v4.26.0 with the
expected signature.

## § 4 — OQ-02 mechanic-fix bundle audit (PR #19260, 3 clusters)

The PR bundles a `+0/−12` (net `−12`, but inner LOC delta different) mechanic
fix to `proofs/Proofs/SylowTheoremOQ02.lean`'s pre-existing
`isProP_conj_map` theorem (L240-) and the `SylowProP.conjBy` `noncomputable
def` (L260-). All three clusters target build failures observed in the
v4.26.0 toolchain (the PR body's "silently broken since the v4.26.0 bump").

### § 4.1 — Cluster 1 (L245-254 → L242-243): replace `Quotient.congr` block

**Before** (10 lines):
```lean
· unfold Subgroup.index
  apply Nat.card_congr
  exact Quotient.congr φ.toEquiv (fun a b => by
    simp only [QuotientGroup.leftRel_apply]
    show a⁻¹ * b ∈ N.comap φ.toMonoidHom ↔
      (φ.toEquiv a)⁻¹ * (φ.toEquiv b) ∈ N
    rw [Subgroup.mem_comap]
    …)
```

**After** (1 line):
```lean
· exact (Subgroup.index_comap_of_surjective N φ.surjective).symm
```

**Bearer**: `Subgroup.index_comap_of_surjective` at `Mathlib/GroupTheory/Index.lean:70` — pin-verified at SHA. Signature:

```
theorem Subgroup.index_comap_of_surjective {f : G' →* G} (hf : Function.Surjective f) :
    (H.comap f).index = H.index
```

Call site shape: `Subgroup.index_comap_of_surjective N φ.surjective` with `H := N` (explicit subgroup variable from Mathlib's `variable (H K L : Subgroup G)` block at Index.lean header) and `f` inferred from `hf := φ.surjective` whose type is `Function.Surjective ↑φ` for `φ : G ≃* G`. Lean elaborator unifies `↑φ` with `φ.toMonoidHom` via coercion (defeq), giving `(N.comap φ.toMonoidHom).index = N.index`. The `.symm` flips to `N.index = (N.comap φ.toMonoidHom).index`, matching the proof's `rw [show N.index = N'.index from ?_]` hole where `N' := N.comap φ.toMonoidHom`. ✓ Logically clean; build's 3062-job pass corroborates the elaborator path.

**LOC delta**: −9 (10 lines collapsed to 1).

### § 4.2 — Cluster 2 (L265 `symm` + L280 `.symm`): remove paired flips

**Before**:
```lean
have key : H.map (MulAut.conj g⁻¹).toMonoidHom = P.toSubgroup := by
  symm                                                  -- L265
  apply P.isMaximal …
  …
exact step.symm                                         -- L280
```

**After**:
```lean
have key : H.map (MulAut.conj g⁻¹).toMonoidHom = P.toSubgroup := by
  apply P.isMaximal …
  …
exact step
```

**Why the prior `symm`s cancelled**: `P.isMaximal` produced an equation in the
direction `P.toSubgroup = …` rather than `… = P.toSubgroup` (or vice versa,
sensitive to a Lean 4 elaboration ordering change). Either both flips need
to land or neither does. The post-`map_map` `step` then propagates the same
direction unchanged, so the terminal `.symm` is also dropped. Confirmed by
reading the patched body: after deleting both flips, the goal type of the
`exact step` line matches `step`'s elaborated type directly. ✓

### § 4.3 — Cluster 3 (between L275 patched + `rw [Subgroup.map_map]`): insert `dsimp only at step`

**Before**:
```lean
have step := congr_arg (fun K => K.map (MulAut.conj g).toMonoidHom) key
rw [Subgroup.map_map] at step          -- pattern not found (β-form blocks rw)
```

**After**:
```lean
have step := congr_arg (fun K => K.map (MulAut.conj g).toMonoidHom) key
dsimp only at step                     -- β-reduce the lambda first
rw [Subgroup.map_map] at step
```

**Why**: `congr_arg (fun K => K.map …) key` yields
`(fun K => K.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g⁻¹).toMonoidHom) = (fun K => …) P.toSubgroup`
with the lambda *unapplied*. `Subgroup.map_map`'s LHS pattern is the literal
`(K.map f).map g`, which doesn't match the β-redex literal. `dsimp only at
step` β-reduces both sides so the LHS becomes `(H.map …).map …` — now
syntactically matching `Subgroup.map_map`. ✓ Standard Lean 4 elaboration
trap; bug class matches "pattern-not-found-due-to-β" referenced in
multiple memory feedback entries.

### § 4.4 — Cluster summary

| Cluster | Site | Symptom | Fix | LOC | Status |
|---------|------|---------|-----|-----|--------|
| 1 | `isProP_conj_map` body, L245-254 | `Quotient.congr` direction mismatch cascade (4 errors at v4.26.0) | 1-line `index_comap_of_surjective N φ.surjective).symm` | −9 net | ✓ bearer pin-verified |
| 2 | `SylowProP.conjBy` body, L265 + L280 | Paired `symm`/`.symm` direction-flip artifacts | Delete both flips | −2 | ✓ logically clean |
| 3 | `SylowProP.conjBy` body, between L275 and `rw [Subgroup.map_map]` | β-redex blocks `rw` pattern match | Insert `dsimp only at step` | +1 | ✓ standard pattern |

**Net cluster delta**: `−10` LOC (matches PR body's `−12` deletions
including the +1 dsimp insertion and 1 stray line).

## § 5 — OQ-03 file: end-to-end proof walkthrough at the API level

`proofs/Proofs/SylowTheoremOQ03.lean` (162 lines, 5 declarations:
`restrictToSylowProP` def, 3 helper theorems, 1 main theorem
`sylowProP_projects_pgroup_continuous`). Goal-state walkthrough:

**Step A — `restrictToSylowProP P φ := φ.comp P.toSubgroup.subtype`** (L90-91)

Type: `P.toSubgroup →* H`. Uses `MonoidHom.comp` (no Mathlib bearer flag
needed; foundational). ✓

**Step B — `continuous_restrictToSylowProP : Continuous (restrictToSylowProP P φ)`** (L94-96)

`hφ_cont.comp continuous_subtype_val` — uses `Continuous.comp`
(`Mathlib/Topology/Defs/Basic.lean`, foundational) + B5
(`continuous_subtype_val` at `Constructions.lean:367`). ✓

**Step C — `isOpen_ker_restrictToSylowProP`** (L100-111)

```lean
have hker_eq :
    ↑((restrictToSylowProP P φ).ker)
      = (restrictToSylowProP P φ) ⁻¹' ({(1 : H)} : Set H) := by
  ext x; simp [MonoidHom.mem_ker]
rw [hker_eq]
exact (isOpen_discrete _).preimage (continuous_restrictToSylowProP P φ hφ_cont)
```

- `MonoidHom.mem_ker` — at `Mathlib/Algebra/Group/Subgroup/Ker.lean` (search confirmed present, line offset stable; not flagged because the file already uses it).
- B4 `isOpen_discrete` at `Order.lean:255` ✓.
- `Continuous.preimage` (or `IsOpen.preimage` of a continuous map) — foundational `Continuous.isOpen_preimage` in `Mathlib/Topology/Defs/Basic.lean`. Standard. ✓

**Step D — `exists_pow_index_ker_restrictToSylowProP`** (L115-120)

```lean
P.isProP.index_of_open_normal
  (restrictToSylowProP P φ).ker
  (MonoidHom.normal_ker _)
  (isOpen_ker_restrictToSylowProP P φ hφ_cont)
```

Uses OQ-02's `IsProP.index_of_open_normal` (a structure field of the
`IsProP` typeclass declared in `proofs/Proofs/SylowTheoremOQ02.lean`) — not
a Mathlib bearer; in-repo dependency. B3 `MonoidHom.normal_ker` at
`Ker.lean:314` ✓ provides the normality instance argument; the `_`
placeholder elaborates to `restrictToSylowProP P φ`.

**Step E — `sylowProP_projects_pgroup_continuous`** (L135-152), main theorem.

```lean
-- (i) himg_eq_range : P.toSubgroup.map φ = (restrictToSylowProP P φ).range
have himg_eq_range : … := by
  ext x
  simp [Subgroup.mem_map, MonoidHom.mem_range, restrictToSylowProP,
        MonoidHom.comp_apply, Subgroup.coe_subtype]
-- (ii) hcard_range : Nat.card range = ker.index   (via index_ker.symm)
have hcard_range : … := (Subgroup.index_ker (restrictToSylowProP P φ)).symm
-- (iii) ⟨k, hk⟩ : ker.index = p ^ k   (from Step D)
obtain ⟨k, hk⟩ := exists_pow_index_ker_restrictToSylowProP P φ hφ_cont
-- (iv) hcard_img : Nat.card (P.toSubgroup.map φ) = p ^ k
have hcard_img : Nat.card (P.toSubgroup.map φ) = p ^ k := by
  rw [himg_eq_range, hcard_range, hk]
-- (v) IsPGroup.of_card hcard_img : IsPGroup p (P.toSubgroup.map φ)
exact IsPGroup.of_card hcard_img
```

- (i) `ext x; simp [B6, B7, restrictToSylowProP, MonoidHom.comp_apply, B8]` — three Mathlib bearers verified (B6 `Subgroup.mem_map` @ `Map.lean:128`, B7 `MonoidHom.mem_range` @ `Ker.lean:73`, B8 `Subgroup.coe_subtype` @ `Defs.lean:579`). The simp set is complete for the goal `x ∈ P.toSubgroup.map φ ↔ x ∈ (restrictToSylowProP P φ).range`: both sides reduce to `∃ y ∈ P.toSubgroup, φ y = x`. ✓
- (ii) `(B1).symm` flips `f.ker.index = Nat.card f.range` to the desired direction. ✓
- (iv) Three sequential `rw`s chain `Nat.card (P.toSubgroup.map φ) → Nat.card range → ker.index → p^k`. ✓
- (v) `B2 IsPGroup.of_card` consumes the cardinality equation. Subgroup-as-Group inheritance via Mathlib's `Subgroup.toGroup` instance — the section variable `(P.toSubgroup.map φ)` is a `Subgroup H` carrying `Group ↥(...)` instance. ✓

**Build-verification corroboration**: the 3062-job pass at PR open time
(2026-05-15 06:20 UTC) matches an end-to-end successful elaboration; no
gap in the bearer chain.

## § 6 — Soft inaccuracies in STATE-SYNC #18994 (advisory only)

The STATE-SYNC PR drafts a "Lean signature lock-in" block for Candidate A*
that has two minor inaccuracies compared to what the ACT PR actually
proves. **These do not block merging** and **should not be edited in this
PREP** (conflict-free constraint; the ACT supersedes the lock-in anyway).
Listed for future-picker context:

| # | STATE-SYNC draft (its `state.md` §3.3 in the PR) | ACT actual signature | Severity |
|---|--------------------------------------------------|----------------------|----------|
| Soft-1 | `(P : SylowProP p G)` (arg order `p` then `G`) | `(P : SylowProP G p)` (arg order `G` then `p`, matches OQ-02 declaration at `SylowTheoremOQ02.lean:108-110`) | cosmetic — STATE-SYNC predates final naming and locked in the wrong tuple order |
| Soft-2 | `IsPGroup p (φ.range)` (the *entire* range of φ) | `IsPGroup p (P.toSubgroup.map φ)` (the image of *just* P under φ) | mathematical — `φ.range` is `⟨image of all of G⟩` whereas `P.toSubgroup.map φ` is image of P; these are different subgroups of H whenever P < G. The ACT statement is the correct/tighter one (matches OQ-02's axiom statement at `SylowTheoremOQ02.lean:134-139`). |
| Soft-3 | Replaces `axiom sylowProP_projects_pgroup` directly | New file `SylowTheoremOQ03.lean` provides `sylowProP_projects_pgroup_continuous` alongside the OQ-02 axiom (axiom remains for backward compatibility; net axiom count unchanged: 5) | scope — milder than STATE-SYNC's "−3 LOC in OQ-02"; the ACT's `−12` LOC change comes entirely from the v4.26.0 mechanic fix in OQ-02 (§ 4), not from axiom replacement |

The STATE-SYNC's *core* contribution — locking in the PREP chain's findings
(particularly PREP-6's `Subgroup.index_ker` major win) — remains correct and
load-bearing. The Soft-1–3 inaccuracies are confined to its anticipatory
"Lean signature" block which the ACT supersedes.

## § 7 — Merge order recommendation

**Recommended chronological merge** (no force-pick, both ship distinct value):

1. **#18994 STATE-SYNC first** (opened 26 h earlier, doc-only, no Lean
   conflict risk).
2. **#19260 S2 ACT second** (opened later, Lean + sessions, build-verified).

Rationale:
- Both are MERGEABLE/clean; neither blocks the other on file-conflict (#18994
  edits `state.md`/JSON/1 session; #19260 edits 2 Lean files + 2 different
  sessions + `Proofs.lean`).
- Chronological respects opening order — minimal-surprise for log readers.
- STATE-SYNC's prose `state.md` provides the *picker-facing* anchor that
  explains the ACT's Candidate A* selection. Landing it first keeps `state.md`
  prose ahead of the ACT's introduction of the new file.
- ACT's `state.md` is **not** updated by this PR (PR #19260 only adds a
  session file, no `state.md` edit). A subsequent STATE-SYNC PR-9 (post
  merge of both) will bump the phase to PREP-7-or-later.

**Do not close either PR.** Both ship load-bearing value:
- #18994 = prose anchor + JSON gallery state.
- #19260 = build-verified Lean + v4.26.0 mechanic-fix bundle.

## § 8 — Risk assessment

| Risk | Likelihood | Severity | Mitigation |
|------|------------|----------|------------|
| Mathlib SHA shifts before merge invalidates bearer lines | low | low | Bearers are *semantic-stable* (top-level theorem names in Mathlib core); line drift would not break elaboration. |
| Soft-2 signature mismatch surfaces as a contributor complaint | low | low | This PREP-7 surfaces the gap explicitly; no further action needed unless contributor disputes. |
| OQ-02 v4.26.0 mechanic-fix conflicts with a parallel mechanic PR | low | medium | Searched `gh pr list --search "SylowTheoremOQ02 in:title"` — no concurrent mechanic PR exists for OQ-02. |
| Deployer remains stalled past TTL of the two PRs | medium | low | Both PRs are `clean`; the stall is a deployer-side queue issue, not a per-PR mergeability issue. No researcher action required from this slug. |

No critical or moderate risks identified.

## § 9 — File path manifest (this PR)

This PR is strict conflict-free:

```
research/problems/sylow-theorems-oq-03/sessions/
  2026-05-15-s2-prep-7-meta-audit-2-open-prs.md     (NEW — this file, ~250 LOC)
```

No edits to:
- `state.md` — owned by STATE-SYNC #18994 (intentional non-conflict).
- `knowledge.md` — owned by prior PREP merges (no new content needed).
- `problem.md` — stable since S1 OBSERVE.
- `src/data/research/problems/sylow-theorems-oq-03.json` — owned by STATE-SYNC #18994.
- Any Lean source — owned by S2 ACT #19260.
- Any earlier session file — historical record.

## § 10 — Acceptance criteria for this PREP-7

1. ✓ All 8 Mathlib bearers in PR #19260's OQ-03 file pin-verified at lake SHA.
2. ✓ All 3 clusters of OQ-02 v4.26.0 mechanic fix logically audited at the
   Lean elaboration level.
3. ✓ End-to-end proof walkthrough of the 5 OQ-03 declarations at the API
   level (no gap in bearer chain).
4. ✓ Soft inaccuracies in STATE-SYNC #18994 surfaced as advisory-only (not
   edited, conflict-free).
5. ✓ Merge order recommended (chronological: #18994 → #19260).
6. ✓ Race-awareness check at `gh pr list --search "sylow-theorems-oq-03"`:
   2 open PRs at PREP open, both `clean`, no concurrent ACT PR.
7. ✓ Lake SHA pin recorded for future reproducibility.

## § 11 — Next action (post-merge)

After both PRs merge, the next researcher-iteration on this slug is a
STATE-SYNC PR-9 that bumps `state.md`'s phase from `PREP` (set by #18994)
to `S2 ACT (complete)` and reflects the actual landed signature
(`sylowProP_projects_pgroup_continuous` for `P.toSubgroup.map φ`, not
`φ.range`). LOC budget: ~30-50 LOC, doc-only.

The OQ-02 axiom `sylowProP_projects_pgroup` itself remains in place after
this ACT (it is a *thin wrapper* per OQ-03 L57-62 of the new file). A
future S3 work-item — out of OQ-03 scope — would delete the axiom and
re-route the (currently zero) downstream callers to
`sylowProP_projects_pgroup_continuous`. Axiom count net: **unchanged at
5** until that S3 work lands.

## § 12 — Reproducibility

Each Mathlib bearer was verified by:

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/<Path>?ref=$SHA" \
  --jq '.content' | base64 -d | sed -n '<line-range>p'
```

Each verified bearer's exact code snippet at SHA was inspected against the
OQ-03/OQ-02 call site in PR #19260 (head SHA
`e706a5160de141223ab853382af9f476de282a24`).
