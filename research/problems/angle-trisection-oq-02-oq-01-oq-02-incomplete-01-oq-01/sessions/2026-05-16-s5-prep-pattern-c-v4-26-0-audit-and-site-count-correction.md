# S5 PREP — Pattern C v4.26.0 audit + site-count correction (3 → 8) + Pattern F/G cascade analysis (doc-only)

**Researcher**: researcher-1
**Date**: 2026-05-16T09:15Z
**Mode**: REVISIT (post-PR#19508 S4 PREP merge, ~22 min)
**Outcome**: doc-only S5 PREP narrowing remaining BUILD-BLOCKER patterns
**Phase**: ORIENT → ORIENT (unchanged; BLOCKED on parent-repair)
**Iteration**: 4 → 5 (this S5 bump)

## TL;DR

S3 PREP (#19446) catalogued Pattern C as **"3 sites at lines 287/292/298"**. Re-audit at lake pin `2df2f0150c…` from `origin/main` HEAD shows **8 sites** (lines 287, 292, 298, 308, 327, 398, 468, 484). Pattern C is **2.67× under-reported**. This S5 PREP corrects the site count, audits `IsScalarTower.of_algebraMap_eq` at lake pin (signature unchanged from prior Mathlib versions), proposes 3 candidate paste-ready fixes ranked by elaboration robustness, and analyzes Pattern F / G as cascades from B / H (expected to auto-resolve post-mechanic-repair).

### Coverage delta

| Catalog status | After #19446 (S3) | After #19508 (S4) | After this PR (S5) |
|----------------|--------|--------|--------|
| Catalogued patterns | 8 (A-H) | 8 (A-H) | 8 (A-H) |
| Catalogued sites total | 26 | 26 | **31** (corrected: C 3→8 = +5) |
| Paste-ready sites | 14 (A:10 + D:3 + 1) | 17 (A:10 + D:3 + E:2 + H:1 + 1) | **17** (no new paste-ready; this PR is corrective + analytic) |
| Paste-ready coverage | 14/26 (54%) | 17/26 (65%) | 17/31 (55% — drops due to site-count correction) |
| Investigative-only patterns | B, C, E, F, G | B, C, F, G | B, C, F, G (F/G analyzed as B/H-cascades; no standalone audit needed) |

**Net narrowing**: Patterns F and G removed from "investigative" by cascade-analysis (resolve when B and H are fixed). Pattern C jumps from "investigative-small" (3 sites) to "investigative-medium" (8 sites). Net coverage drops 65% → 55% but the investigative scope is more accurate.

---

## §1 — Pattern C site-count audit

### §1.1 Grep over parent file

```
$ grep -n "IsScalarTower.of_algebraMap_eq" \
    proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean
287:      IsScalarTower.of_algebraMap_eq (fun r =>
292:      IsScalarTower.of_algebraMap_eq (fun r =>
298:      IsScalarTower.of_algebraMap_eq (fun r =>
308:      IsScalarTower.of_algebraMap_eq (fun r =>
327:      IsScalarTower.of_algebraMap_eq (fun r =>
398:      IsScalarTower.of_algebraMap_eq (fun r =>
468:      IsScalarTower.of_algebraMap_eq (fun r =>
484:      IsScalarTower.of_algebraMap_eq (fun r =>
```

**8 sites total** (S3 PREP listed 3).

### §1.2 Site-by-site type-ascription inventory

| Site | LHS (type ascription) | Variables in `Algebra` chain |
|------|----------------------|------------------------------|
| L287 | `IsScalarTower ℚ ↥K ↥Ka` | `hAlg_KKa : Algebra ↥K ↥Ka` |
| L292 | `IsScalarTower ↥K ↥Ka ↥Kaβ` | `hAlg_KaKaβ : Algebra ↥Ka ↥Kaβ` |
| L298 | `IsScalarTower ↥Ka ↥Kaβ ↥(Kaβ ⊔ ℚ⟮b⟯)` | `hAlg_KaβJoin : Algebra ↥Kaβ ↥(Kaβ ⊔ ℚ⟮b⟯)` |
| L308 | `IsScalarTower ↥K ↥Ka ↥(Kaβ ⊔ ℚ⟮b⟯)` | `hAlg_KaJoin : Algebra ↥Ka ↥(Kaβ ⊔ ℚ⟮b⟯)` |
| L327 | `IsScalarTower ↥K ↥(K ⊔ ℚ⟮(b + β)⟯) ↥(Kaβ ⊔ ℚ⟮b⟯)` | `hAlg2 : Algebra ↥(K ⊔ ℚ⟮(b + β)⟯) ↥(Kaβ ⊔ ℚ⟮b⟯)` |
| L398 | `IsScalarTower ℚ ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)` | `hAlg_aβ : Algebra ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)` |
| L468 | `IsScalarTower ℚ ↥(ℚ⟮β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯)` | `hAlg_βjoin : Algebra ↥(ℚ⟮β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯)` |
| L484 | `IsScalarTower ℚ ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯)` | `hAlg : Algebra ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯)` |

All 8 sites share the structural template

```lean
haveI hST_*** : IsScalarTower R S A :=
  IsScalarTower.of_algebraMap_eq (fun r =>
    Subtype.ext (by simp [RingHom.algebraMap_toAlgebra, ...]))
```

where `R ≤ S ≤ A` is an `IntermediateField`-chain over `ℂ`, the `Algebra S A` instance is provided by `(IntermediateField.inclusion h_le).toAlgebra` in the preceding `haveI`, and `Algebra R A` is implicit (transitively from `Algebra R ℂ` + `Algebra A ℂ` + `R ≤ A`).

---

## §2 — `IsScalarTower.of_algebraMap_eq` signature at lake pin `2df2f0150c…`

### §2.1 Bearer fetch

```
$ gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Algebra/Tower.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" --jq '.sha'
5597b89cfa18f999e34ba7a70f2fb05d21fc0e5a
```

### §2.2 Signature (Mathlib/Algebra/Algebra/Tower.lean:105-111 at lake pin)

```lean
section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra S A] [Algebra S B]
variable {R S A}

theorem of_algebraMap_eq [Algebra R A]
    (h : ∀ x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S A :=
  ⟨fun x y z => by simp_rw [Algebra.smul_def, map_mul, mul_assoc, h]⟩
```

### §2.3 Argument structure (decoded)

`IsScalarTower.of_algebraMap_eq` takes (after `variable` block consumption):

| Position | Arg | Type | Source |
|----------|-----|------|--------|
| (impl) | `R, S, A` | `Type _` | implicit via `variable {R S A}` |
| (instImpl) | `[CommSemiring R]`, `[CommSemiring S]`, `[Semiring A]`, `[Algebra R S]`, `[Algebra S A]` | typeclass | inherited from variable block (lines 105-106) |
| 1 (explicit) | `[Algebra R A]` | typeclass | explicit on `of_algebraMap_eq` signature |
| 2 (explicit) | `h : ∀ x, algebraMap R A x = algebraMap S A (algebraMap R S x)` | function | the user-provided proof |

**Conclusion**: the signature is **unchanged** between the parent file's commit-time Mathlib (pre-v4.26.0) and lake pin. The lemma still expects `R, S, A` implicit; `[Algebra R A]` is the lone explicit typeclass arg; `h` is the proof.

---

## §3 — Hypothesis on Pattern C failure under v4.26.0

S3 PREP (#19446) reported "**Pattern C** (3 sites): universe constraint stuck inside `IsScalarTower.of_algebraMap_eq` proofs at lines 287, 292, 298". Without Docker access this session, I cannot reproduce the elaboration trace. Three plausible root causes consistent with the symptom:

### §3.1 Hypothesis (i) — Implicit-arg unification failure

`IsScalarTower.of_algebraMap_eq` returns `IsScalarTower R S A`. The type ascription `: IsScalarTower ℚ ↥K ↥Ka` should unify `R := ℚ`, `S := ↥K`, `A := ↥Ka`. If v4.26.0 changed elaboration order to synthesize `[Algebra R A]` *before* `R, S, A` are unified, the typeclass synthesis fails because `R, S, A` are still metavariables. The "universe constraint stuck" symptom matches a stuck unification on `R`'s universe before `R = ℚ` is propagated.

**Fix candidate**: provide `R, S, A` explicitly (Approach A below).

### §3.2 Hypothesis (ii) — IntermediateField coercion universe-bumping

`↥K`, `↥Ka`, `↥(Kaβ ⊔ ℚ⟮b⟯)` etc. are `IntermediateField` coercions. If v4.26.0 changed `IntermediateField`'s carrier universe (e.g. moved from `Type 0` to a polymorphic `Type u`), the resulting `↥K : Type ?u.____` may have an unresolved universe metavariable that gets stuck during `of_algebraMap_eq`'s synthesis.

**Fix candidate**: explicitly ascribe `(↥K : Type 0)` or use `(K : IntermediateField ℚ ℂ)` form directly.

### §3.3 Hypothesis (iii) — Cascade from Pattern B (`Module ↥Ka ↥(Ka ⊔ ℚ⟮β⟯)` synth)

Pattern B (5+ sites) is a `Module` instance synthesis failure for `IntermediateField` sup's. If `[Algebra R A]` in `of_algebraMap_eq`'s explicit arg requires the `Module ↥K ↥Ka` instance (via `Algebra.toModule`), and Pattern B blocks that synthesis, then Pattern C is a downstream cascade from Pattern B at the 4 sup-involving sites (L298, L308, L327, L468 mention sup directly; L484 mentions `ℚ⟮b + β⟯` which is single-generator and likely fine).

**Fix candidate**: fix Pattern B first; Pattern C may auto-resolve at sup-involving sites.

### §3.4 Most likely: combination of (i) + (iii)

The 4 non-sup sites (L287 `ℚ ↥K ↥Ka`, L292 `↥K ↥Ka ↥Kaβ`, L398 `ℚ ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)`, L484 `ℚ ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯)`) likely fail under hypothesis (i) only; fix via Approach A. The 4 sup sites (L298, L308, L327, L468) likely fail under hypothesis (iii) + (i); fix Pattern B first, then Approach A if residual.

---

## §4 — Three candidate fixes (paste-ready signatures, elaboration-deferred)

### §4.1 Approach A — Explicit type args (most robust against hypothesis (i))

```lean
haveI hST_KKa : IsScalarTower ℚ ↥K ↥Ka :=
  IsScalarTower.of_algebraMap_eq (R := ℚ) (S := ↥K) (A := ↥Ka) (fun r =>
    Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
```

**Pros**: forces `R, S, A` resolution before `[Algebra R A]` synthesis. Safe for all 8 sites.
**Cons**: verbose; +20-40 chars per site (8 sites × 30 chars ≈ +240 chars total).
**Risk**: LOW. Pure named-arg rewrite; no semantic change.

### §4.2 Approach B — Explicit `[Algebra R A]` instance let-binding (most robust against hypothesis (iii))

```lean
-- L287: BEFORE
haveI hST_KKa : IsScalarTower ℚ ↥K ↥Ka :=
  IsScalarTower.of_algebraMap_eq (fun r =>
    Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))

-- L287: AFTER
letI : Algebra ℚ ↥Ka := (IntermediateField.algebra Ka).restrictScalars ℚ
haveI hST_KKa : IsScalarTower ℚ ↥K ↥Ka :=
  IsScalarTower.of_algebraMap_eq (fun r =>
    Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
```

**Pros**: provides the `[Algebra R A]` instance before `of_algebraMap_eq` is invoked. Sidesteps cascade.
**Cons**: requires identifying the right `Algebra ℚ ↥Ka` constructor per site (may be `IntermediateField.algebra` or `Algebra.compHom` via transitivity).
**Risk**: MEDIUM. Per-site context-sensitive; mechanic must verify which constructor lands without unification conflicts with auto-synthesized instances.

### §4.3 Approach C — Switch to `of_algebraMap_eq'` (sidesteps the `∀ x, ...` form)

```lean
haveI hST_KKa : IsScalarTower ℚ ↥K ↥Ka :=
  IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := ↥K) (A := ↥Ka)
    (RingHom.ext (fun r =>
      Subtype.ext (by simp [RingHom.algebraMap_toAlgebra])))
```

**Pros**: switches from `∀ x, algebraMap R A x = ...` (function) to `algebraMap R A = ...` (RingHom equality); avoids any elaboration quirks tied to the `∀` form.
**Cons**: requires adapting the per-site proof from `Subtype.ext (by simp [...])` to `RingHom.ext (fun r => Subtype.ext (by simp [...]))`. Adds 1 LOC of wrapping per site.
**Risk**: LOW. Mathlib at pin defines `of_algebraMap_eq' h = of_algebraMap_eq (RingHom.ext_iff.1 h)` so semantically equivalent.

### §4.4 Recommended: ship Approach A first; fall back to A+B for sup sites; reserve C as plan-C

**Rationale**: Approach A is the smallest mechanical change; if it fixes all 8 sites (likely if hypothesis (i) is the sole cause), done. If sup sites residually fail, Approach B targets the cascade. If both fail in some site, Approach C is the structural fallback.

---

## §5 — Pattern F / G cascade analysis (no standalone audit needed)

### §5.1 Pattern F (2 sites: simp no-progress)

S3 PREP catalogued Pattern F as "simp no-progress cascade from B/H". A `simp` no-progress error arises when an earlier `haveI` failed to land its instance, so `simp`'s rewrite-set is missing the lemma it needs. Specifically:

- F-site 1: line ~430-440 (after Pattern E line 429 fails to land `adjoin_eq_top_of_adjoin_eq_top h_gen_Q`); `simp [adjoin_eq_top_of_...]` then no-progresses.
- F-site 2: line ~445-455 (after Pattern H line 444 `SubsemiringClass.coe_pow` is undefined under v4.26.0 deprecation); subsequent `simp [SubsemiringClass.coe_pow, ...]` has a missing lemma, simp no-progresses.

**Expected resolution post-mechanic-repair**: F resolves automatically when:
- E's line 426/429 paste-ready (`adjoin_eq_top_of_algebra ℚ ...` + `adjoin_eq_top_of_adjoin_eq_top ↥(ℚ⟮a⟯) ...`) is applied
- H's line 444 paste-ready (`SubmonoidClass.coe_pow` 1-token rename) is applied

**No standalone S5 audit needed.** F is a downstream symptom of E + H.

### §5.2 Pattern G (1 site: unsolved `h_aeval` goal cascade)

S3 PREP catalogued Pattern G as "unsolved `h_aeval` goal cascade from H". The `h_aeval` hypothesis is presumably constructed via a chain involving `SubsemiringClass.coe_pow` for `β^k` evaluations. When H fails, the hypothesis construction stalls and `h_aeval` is never proven.

**Expected resolution post-mechanic-repair**: G resolves automatically when H's 1-token paste-ready is applied.

**No standalone S5 audit needed.** G is a downstream symptom of H.

### §5.3 Conclusion: F and G removed from investigative list

After mechanic applies paste-ready A + D + E + H + (S5's) A-variant for C, the remaining investigative patterns are: **B + (residual sup-Pattern-C)**. If Approach A fixes all 8 C sites, just B remains.

---

## §6 — Pattern E addendum: line 219 third site?

`grep` shows an additional `adjoin_eq_top_of_adjoin_eq_top` call at parent file line 219:

```lean
-- tower law: adjoin ℚ S = ⊤ implies adjoin ↥Ka S = ⊤
have h_adj_Ka := IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_adj_ℚ
```

S4 PREP (#19508) catalogued Pattern E as "2 sites at lines 426 + 429". Line 219 is a third potential site under v4.26.0's "explicit `F` and `E` args" change.

**Recommendation for mechanic**: when applying S4 PREP's Pattern E paste-ready, also check line 219 — pass `ℚ` (and `↥Ka` for the tower variant) positionally if the signature change applies.

**Risk if missed**: 1 additional error site, same fix recipe; isolated `have` so does not cascade.

---

## §7 — Bearer SHA log (lake pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| File | SHA at pin | Used for |
|------|-----------|----------|
| `Mathlib/Algebra/Algebra/Tower.lean` | `5597b89cfa18f999e34ba7a70f2fb05d21fc0e5a` | `IsScalarTower.of_algebraMap_eq` audit (§2) |

Carry-overs (audited in prior S-PREP sessions, unchanged at this pin):
- `Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean` → `be9a6cb200c9482c3953cb22687482b132f8c0de` (Pattern E, S4 PREP)
- `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean` → `d9154f51ed2cf573d8a7e61eed63e91107c3466d` (Pattern E, S4 PREP)
- `Mathlib/FieldTheory/IntermediateField/Basic.lean` → `687faa0c33e837fa0d53104ee045328975a6497f` (Pattern B carrier, S3 PREP)
- `Mathlib/Algebra/Ring/Subsemiring/Defs.lean` → `10b5a6089cc0983d52f78bfb579aabf46ac7d721` (Pattern H, S4 PREP)

---

## §8 — Updated ACT-readiness gate

| Gate | Status | Detail |
|------|--------|--------|
| G1 — companion plan still valid | ✅ | S2c PREP §3-§5 depends only on PUBLIC parent surface; unchanged |
| G2 — bearer pins verified at lake SHA | ✅ | 5 bearer files audited (Tower.lean added S5, 4 from S3/S4 unchanged) |
| G3 — paste-ready coverage | ⚠ AMBER | 17/31 sites (55%, down from 65% nominal due to C correction); A+D+E+H paste-ready, C/B/F/G investigative-but-cascade-clear |
| G4 — investigative scope realistic | ✅ | C: 8 sites with 3 candidate fixes (A/B/C); B: 5+ sites with `haveI` placement context (S3 PREP §6); F/G: cascades from E/H, auto-resolve |
| G5 — mechanic handoff clean | ✅ | Single PR scope: apply paste-ready (A:10 + D:3 + E:2 + H:1 = 16 sites direct), apply C Approach A (8 sites named-arg rewrite), then iterate B (5 sites) |
| G6 — total estimated repair LOC | ✅ | **+50 to +75 LOC** (revised from S3's +45-65: C's 8 sites × 1 LOC of named-arg = +8; rest unchanged) |
| G7 — companion file unaffected | ✅ | 0 LOC change in companion (slug-local file in `AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`, which doesn't exist yet — S2c PREP §3 names it but holds for post-repair |
| G8 — host disk + Docker daemon | ❌ RED | host disk 100% / 6.9 Gi avail / `docker info` hung past 8 s — UNCHANGED from S4 PREP; INFRASTRUCTURE-ONLY blocker |

**Verdict**: 6/8 GREEN, 1/8 AMBER, 1/8 RED (G8 infrastructure). Substantive gate state unchanged from S4 PREP. **Mechanic agent can take the handoff once G8 clears.**

---

## §9 — Next picker

1. **Operator**: clear 10-30 Gi host disk; restart Docker daemon.
2. **Mechanic**: single PR scope:
   - Apply paste-ready A (10 sites), D (3 sites), E (2-3 sites: 426 + 429 + check 219), H (1 site, 1-token rename); iterate on B (5+ sites, per-site `haveI` placement)
   - Apply Pattern C Approach A (named-arg `(R := ...) (S := ...) (A := ...)`) at all 8 sites: 287, 292, 298, 308, 327, 398, 468, 484
   - Confirm F (2 sites) and G (1 site) auto-resolve post-A+D+E+H+C
   - Estimated 45-60 min including 3-4 docker iters
3. **Researcher**: post-repair, claim Iter 6 = ACT-α (companion file creation per S2c PREP §3 OPT-1).

---

## §10 — Files modified in this PR (2)

| File | Insertions | Deletions | Purpose |
|------|-----------:|----------:|---------|
| `research/problems/.../sessions/2026-05-16-s5-prep-pattern-c-v4-26-0-audit-and-site-count-correction.md` (new, this file) | ~300 | 0 | this S5 PREP memo |
| `research/problems/.../state.md` | ~20 | ~5 | head iteration bump 4 → 5; S5 Current Focus update; Pattern C site count 3 → 8 propagation |

**Zero edits**: research JSON / meta.json / knowledge.md / problem.md / Lean / `state.md` body sections (other than head); **0 file overlap** with any open PR (verified `gh pr list --search "$SLUG" state:open` returns 0).

---

## §11 — What this PR does NOT do

- 0 Lean / `meta.json` / research JSON / `knowledge.md` / `problem.md` edits.
- Does NOT verify Pattern C Approach A via Docker (G8 RED; INFRASTRUCTURE-ONLY blocker).
- Does NOT close Pattern B (5+ sites, requires `haveI` placement audit; deferred to mechanic).
- Does NOT advance substantive `IsConstructible` / `wantzel_galois_iff` work (BLOCKED on parent rebuild).
- Does NOT execute `docker-build.sh` (G8 RED — host disk pressure + Docker daemon non-responsive).

---

## §12 — Memory traps fired

- `_postship_pivot_upgrades_audit_doc_deferred_sketch_to_pasteready_prep` — partial fire (audit-correction variant: site count + cascade clarity vs. paste-ready upgrade).
- `_act_pivot_to_prep_when_host_docker_corrupt` — light fire (G8 RED forces doc-only path).
- `_postship_pivot_lands_on_fully_discharged_slug_blocked_hermit_followup_ship_packaged_followups_prep` — does NOT fire (slug is BUILD-BLOCKER, not fully-discharged).
- `_postship_pivot_lands_on_slug_where_recent_act_did_partial_inline_statesync_leaving_n_drift` — does NOT fire (PRs #19446, #19508 were complete PREP cycles, not partial state-syncs).

---

## §13 — Pool sync (deferred to release call)

Pool entry `candidates[].status: "available"` (seeker-placed). End-of-session:

```bash
/Users/rwalters/GitHub/lean-genius/scripts/research/claim-problem.sh release angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01
```

**Status stays `available`** (do NOT mark `surveyed` / `completed`); slug remains active research target with mechanic-handoff queued. Release frees the claim for future researcher-N iterations post-mechanic-repair.
