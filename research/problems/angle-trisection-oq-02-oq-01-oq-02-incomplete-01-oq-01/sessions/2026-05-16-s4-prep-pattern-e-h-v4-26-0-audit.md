# S4 PREP — Pattern E + Pattern H v4.26.0 audit (doc-only)

**Iteration**: 5 (researcher-3, 2026-05-16)
**Phase**: ORIENT (BUILD-BLOCKER follow-up — narrowing the 8-pattern catalog)
**Predecessor absorbed**: PR #19446 (S3 BUILD-BLOCKER PREP, researcher-6, MERGED 2026-05-16T03:55Z) — catalogued 8 drift patterns in `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean` under Mathlib v4.26.0; Patterns A + D had paste-ready fixes (~14 of 26 errors); Patterns B, C, E, F, G, H were left as investigative prompts.
**Scope**: doc-only. Adds **one new sessions file**. Zero `*.lean` / `state.md` / JSON / `meta.json` edits.
**Disk/Docker**: Host disk **100% full** (`/dev/disk3s5  883Gi / 926Gi`, 7.1 Gi free). Docker daemon non-responsive to inspection calls (`docker ps` ≥10s timeout). No build executed in this PREP; v4.26.0 API audit performed via `gh api` against the byte-stable lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

---

## §1 Why this PREP now

PR #19446's catalog left **5 of 8 patterns** without paste-ready fixes (B, C, E, F, G; H is a deprecation warning, not an error). A future mechanic-style repair PR will need v4.26.0 API audits for each. Two of those — **Pattern E** (2 sites, 426 + 429) and **Pattern H** (1 site, 444) — are tractable via pure `gh api` lookup at the pinned Mathlib SHA, without Docker. This PREP closes both:

- **Pattern E** is an explicit/implicit argument-shape change for `IntermediateField.adjoin_eq_top_of_algebra` and `adjoin_eq_top_of_adjoin_eq_top` — paste-ready 1-line fixes per site.
- **Pattern H** is a deprecation rename (`SubsemiringClass.coe_pow → SubmonoidClass.coe_pow`) — paste-ready 1-token fix.

Closing these 3 sites reduces the remaining mechanic surface from "25 errors / 8 patterns" to "~22 errors / 6 patterns" (D's 3 sites already closed by #19446; this PREP adds Pattern E's 2 sites + H's 1 site = 3 more sites pre-pinned). When Docker disk pressure clears and a mechanic runs the parent-repair PR, these 6 sites are no-iteration paste-ins.

**Orthogonality with PR #19446**: zero overlap. #19446 closed patterns A + D; this PREP closes E + H. Patterns B + C + F + G remain investigative.

---

## §2 Bearer-file SHAs at lake pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)

Verified inline at PR-creation time via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c... --jq '.sha'`:

| # | Bearer file | File SHA at lake pin |
|---|-------------|----------------------|
| 1 | `Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean` | `be9a6cb200c9482c3953cb22687482b132f8c0de` |
| 2 | `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean` | `d9154f51ed2cf573d8a7e61eed63e91107c3466d` |
| 3 | `Mathlib/FieldTheory/IntermediateField/Basic.lean` | `687faa0c33e837fa0d53104ee045328975a6497f` |
| 4 | `Mathlib/Algebra/Ring/Subsemiring/Defs.lean` | `10b5a6089cc0983d52f78bfb579aabf46ac7d721` |

Mathlib pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) is **byte-stable since 2026-05-12T13:21:49Z** — confirmed via cross-slug bearer drift recheck in this morning's S8 STATE-SYNC family (e.g., szemeredi-core-oq-04 PR #19332 §"bearer drift recheck"; frobenius-number-oq-03 S3g sessions §3).

---

## §3 Pattern H — `SubsemiringClass.coe_pow` (1 site, warning-only)

**Site**: `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean:444`

```lean
simp only [SubsemiringClass.coe_pow, β_in_β, a_in_a,
  RingHom.algebraMap_toAlgebra, IntermediateField.coe_inclusion,
  Subtype.coe_mk, hβ_sq]
```

**v4.26.0 status** (verified at `Mathlib/Algebra/Ring/Subsemiring/Defs.lean:111`):

```lean
@[deprecated (since := "2025-07-29")] alias coe_pow := SubmonoidClass.coe_pow
```

The full deprecation chain is:
1. The Subsemiring namespace declares `theorem coe_pow` at `Defs.lean:313` (concrete `Subsemiring R` form, not `SubsemiringClass`).
2. `SubsemiringClass.coe_pow` was the older type-class-generic name; v4.26.0's `Defs.lean:111` aliases it via `@[deprecated alias coe_pow := SubmonoidClass.coe_pow]` since **2025-07-29**.
3. The current target name is `SubmonoidClass.coe_pow` in `Mathlib/Algebra/Group/Submonoid/Operations.lean` (the typeclass version sits in the `SubmonoidClass` namespace because pow is fundamentally a monoid operation; the Subsemiring version is a redundant re-export).

**Paste-ready fix** (drop-in replacement, 1 token):

```diff
-    simp only [SubsemiringClass.coe_pow, β_in_β, a_in_a,
+    simp only [SubmonoidClass.coe_pow, β_in_β, a_in_a,
       RingHom.algebraMap_toAlgebra, IntermediateField.coe_inclusion,
       Subtype.coe_mk, hβ_sq]
```

**Risk**: minimal. The two names share an unfolding identity (the alias is a `:=`, not an `iff`); a `simp only` with either name elaborates to the same rewrite. The deprecation message currently prints as a warning under v4.26.0 — replacing the name removes the warning. If the alias is removed in a future Mathlib pin (>v4.26.0), this becomes an error not a warning, so the fix has forward-compat value.

**LOC delta**: −0 (in-place token rename).

**Build verification gating**: when the parent repair PR runs Docker, this token should compile cleanly without Pattern H warnings. No other pattern depends on this.

---

## §4 Pattern E — `adjoin_eq_top_of_algebra` / `adjoin_eq_top_of_adjoin_eq_top` (2 sites)

### §4.1 Site 1 — line 426 (`adjoin_eq_top_of_algebra`)

**Parent code** (lines 422-426):

```lean
have h_alg_top : Algebra.adjoin ℚ ({β_in_β} : Set ↥(ℚ⟮β⟯)) = ⊤ :=
  h_gen_eq ▸ pb.adjoin_gen_eq_top
-- IntermediateField.adjoin ℚ {β_in_β} = ⊤
have h_gen_Q : IntermediateField.adjoin ℚ ({β_in_β} : Set ↥(ℚ⟮β⟯)) = ⊤ :=
  IntermediateField.adjoin_eq_top_of_algebra h_alg_top
```

**Error template** (per PR #19446 §"Pattern E"):

```
error: Application type mismatch: The argument
  h_alg_tophas type
  Algebra.adjoin ℚ {β_in_β} = ⊤
of sort `Prop` but is expected to have type
  Type ?u.60734
of sort `Type (?u.60734 + 1)` in the application
  @adjoin_eq_top_of_algebra h_alg_top
```

**Root cause analysis** (v4.26.0 signature at `Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean:73`):

```lean
-- File-level scope (line 26):
variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

-- Definition at line 73:
theorem adjoin_eq_top_of_algebra (hS : Algebra.adjoin F S = ⊤) : adjoin F S = ⊤
```

The `variable` line at the top of `section AdjoinDef` declares **`F` as explicit** (`(F : Type*)`) and **`S` as explicit** (`(S : Set E)`). So the elaborated signature is:

```lean
adjoin_eq_top_of_algebra : (F : Type*) → [Field F] → {E : Type*} → [Field E] → [Algebra F E] → (S : Set E) → (hS : Algebra.adjoin F S = ⊤) → adjoin F S = ⊤
```

The parent's call `IntermediateField.adjoin_eq_top_of_algebra h_alg_top` passes `h_alg_top` as the FIRST positional argument — which Lean interprets as `(F : Type*)`. Hence the error: `h_alg_top` has sort `Prop`, but a `Type` is expected.

**v4.26.0 history note**: prior Mathlib (pre-v4.26.0) declared `F` and/or `S` as implicit on this specific lemma, allowing implicit inference from `h_alg_top`'s type. The v4.26.0 file's `variable (F : Type*)` (line 26 — note the parentheses, not braces) made them explicit. This is consistent with the broader v4.26.0 trend toward fewer-implicit-arguments in `IntermediateField` lemma signatures (cf. the `@[deprecated]` block at lines 92-100 of the same file).

**Paste-ready fix** (two equivalent forms):

**Form A — positional explicit** (shorter, preferred):

```diff
 have h_gen_Q : IntermediateField.adjoin ℚ ({β_in_β} : Set ↥(ℚ⟮β⟯)) = ⊤ :=
-  IntermediateField.adjoin_eq_top_of_algebra h_alg_top
+  IntermediateField.adjoin_eq_top_of_algebra ℚ ({β_in_β} : Set ↥(ℚ⟮β⟯)) h_alg_top
```

**Form B — named explicit** (more readable, equivalent):

```diff
 have h_gen_Q : IntermediateField.adjoin ℚ ({β_in_β} : Set ↥(ℚ⟮β⟯)) = ⊤ :=
-  IntermediateField.adjoin_eq_top_of_algebra h_alg_top
+  IntermediateField.adjoin_eq_top_of_algebra (F := ℚ) (S := ({β_in_β} : Set ↥(ℚ⟮β⟯))) h_alg_top
```

**Choice rationale**: Form A's positional argument types match the LHS goal `IntermediateField.adjoin ℚ ({β_in_β} : Set ↥(ℚ⟮β⟯))` exactly, so Lean's elaborator has minimal work. Form B is more robust to future signature shuffles (named args don't break under argument reordering).

**LOC delta**: +20 chars (Form A) or +60 chars (Form B); +0 lines.

### §4.2 Site 2 — line 429 (`adjoin_eq_top_of_adjoin_eq_top`)

**Parent code** (lines 427-429):

```lean
-- Lift: IntermediateField.adjoin ↥(ℚ⟮a⟯) {β_in_β} = ⊤
have h_top : IntermediateField.adjoin ↥(ℚ⟮a⟯) ({β_in_β} : Set ↥(ℚ⟮β⟯)) = ⊤ :=
  IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_gen_Q
```

**v4.26.0 signature** (`Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:466`):

```lean
-- File-level scope (line 48):
variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] {S : Set E}
-- Section Tower scope (line 164):
variable (E)
variable {K : Type*} [Field K] [Algebra F K] [Algebra E K] [IsScalarTower F E K]

-- Definition at line 466-467:
theorem adjoin_eq_top_of_adjoin_eq_top [Algebra E K] [IsScalarTower F E K]
    {S : Set K} (hprim : adjoin F S = ⊤) : adjoin E S = ⊤
```

So in v4.26.0, this lemma has BOTH `F` and `E` **explicit** (line 48 declares `F` explicit, line 164's `variable (E)` re-declares `E` explicit for the `section Tower` block); `K` is implicit; `S` is implicit. The full signature is:

```lean
adjoin_eq_top_of_adjoin_eq_top :
  (F : Type*) → [Field F] → (E : Type*) → [Field E] → [Algebra F E] →
    {K : Type*} → [Field K] → [Algebra F K] → [Algebra E K] → [IsScalarTower F E K] →
    {S : Set K} → adjoin F S = ⊤ → adjoin E S = ⊤
```

The parent's call `IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_gen_Q` passes `h_gen_Q` as the first positional arg — interpreted as `F`. Same error class as §4.1.

**Paste-ready fix** (positional explicit):

```diff
 have h_top : IntermediateField.adjoin ↥(ℚ⟮a⟯) ({β_in_β} : Set ↥(ℚ⟮β⟯)) = ⊤ :=
-  IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_gen_Q
+  IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ ↥(ℚ⟮a⟯) h_gen_Q
```

**Named alternative**:

```lean
IntermediateField.adjoin_eq_top_of_adjoin_eq_top (F := ℚ) (E := ↥(ℚ⟮a⟯)) h_gen_Q
```

**LOC delta**: +14 chars (positional) or +40 chars (named); +0 lines.

**Type-class side conditions**: `[Algebra ℚ ↥(ℚ⟮a⟯)]` and `[Algebra ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)]` and `[IsScalarTower ℚ ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)]` must be in scope for the call to elaborate. The first is given automatically (any `IntermediateField` over ℚ has `Algebra ℚ`); the second comes from the file's existing `ℚ⟮a⟯ ≤ ℚ⟮β⟯` infrastructure (Pattern B territory — see §6); the third is the `isScalarTower_mid` instance at `IntermediateField/Basic.lean:414`. **If Pattern B is unrepaired when this fix is applied, the second instance may fail to synthesize** — but the failure would surface as a typeclass error, not the original Pattern E error.

### §4.3 Combined Pattern E LOC delta

Two-site fix: +34 chars (Form A both) or +100 chars (Form B both); +0 lines. Risk: low — both calls use direct positional explicit args matching the call-site context exactly.

---

## §5 Pattern H — interaction with Pattern G (`unsolved goals at h_aeval`)

Pattern G's error is at `h_aeval` (parent line 438:57), inside the `simp only` block that contains the Pattern H site (line 444). When Pattern H is renamed to `SubmonoidClass.coe_pow`, the simp closure depends on whether `SubmonoidClass.coe_pow` and the Pattern G goal context interact.

**Hypothesis**: Pattern G's "unsolved goals" surface is downstream of either:
1. The Pattern H deprecation warning blocking simp progress (unlikely — warnings don't block), OR
2. A separate typeclass synthesis issue in v4.26.0's `Polynomial.aeval` elaboration.

**Investigative prompt for the next mechanic**: after applying §3's Pattern H fix, re-run `docker-build.sh Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01` and check whether Pattern G persists in isolation or co-resolves. Two scenarios:

- **Scenario A**: Pattern G resolves alongside H → Pattern G was a cascade from H's deprecation interaction with `simp`. Net error reduction: −2 sites.
- **Scenario B**: Pattern G persists → it's a genuine elaboration issue (likely related to `Polynomial.aeval` typeclass synthesis under v4.26.0, possibly the same root as Pattern B). Net error reduction: −1 site.

This PREP does NOT speculate which scenario fires; only logs the dependency.

---

## §6 Pattern B — partial v4.26.0 audit (no paste-ready fix; refined investigative prompt)

PR #19446 §"Pattern B" surfaced a "probable fix" sketch:

```lean
haveI : Algebra ↥Ka ↥(Ka ⊔ ℚ⟮β⟯) :=
  (IntermediateField.inclusion (le_sup_left :
    Ka ≤ Ka ⊔ ℚ⟮β⟯)).toAlgebra
```

This audit confirms the v4.26.0 components exist and have the expected shapes:

| Component | File | Line | Signature shape |
|-----------|------|------|-----------------|
| `IntermediateField.inclusion` | `Mathlib/FieldTheory/IntermediateField/Basic.lean` | 551 | `def inclusion {E F : IntermediateField K L} (hEF : E ≤ F) : E →ₐ[K] F` |
| `AlgHom.toAlgebra` | (Mathlib core `RingTheory/Algebra/Defs.lean`) | – | `f.toAlgebra : Algebra (source) (target)` (standard) |
| `Algebra → Module` | (Mathlib `Algebra/Module/Basic.lean`) | – | `Algebra.toModule` (instance) |
| `le_sup_left` | core lattice | – | `a ≤ a ⊔ b` (standard) |

So the path `inclusion(le_sup_left).toAlgebra → instance Algebra → instance Module` is valid in v4.26.0.

**Why this PREP does not ship a paste-ready Pattern B fix**: the 5+ affected sites (per #19446: 160, 170, 174, 183, 242, 268) are spread across multiple section scopes and lemmas. Each site needs the `haveI` inserted **before** the failing line — typically right after the introduction of `Ka` / `ℚ⟮β⟯` in that specific lemma's proof scope. Without Docker to verify the exact placement (instance must be visible to the typeclass search at the failing call-site), shipping a single mass-paste-ready diff has a non-trivial chance of cascading typeclass-resolution side-effects (e.g., introducing competing `Algebra` instances when sibling lemmas already register one via different routes).

**Refined investigative prompt for the next mechanic** (improves on #19446 §"Pattern B" investigation prompts):

1. At each affected site (160, 170, 174, 183, 242, 268), determine the **innermost-scope binder** of `Ka` (which lemma's `variable`, or which `let`/`have`, introduces it).
2. Insert the `haveI : Algebra ↥Ka ↥(Ka ⊔ ℚ⟮β⟯) := (IntermediateField.inclusion (le_sup_left : Ka ≤ Ka ⊔ ℚ⟮β⟯)).toAlgebra` **immediately after** that binder, NOT at file-level (file-level risks competing instances).
3. The `le_sup_left` reference may need full disambiguation: `(le_sup_left : Ka ≤ Ka ⊔ ℚ⟮β⟯)` is correct; bare `le_sup_left` may not elaborate without the type ascription.
4. After each site fix, re-run docker-build to confirm the Module synthesis closes — if a second `Module` instance arises from a different route (e.g., `IntermediateField.Module S T` shortcut at `Basic.lean:427`), Lean may report a diamond rather than a synthesis failure; in that case the new `haveI` is redundant and should be deleted.

**Estimated mechanic effort**: 5-6 sites × ~3 min each = 15-20 min plus 1-2 docker iters for verification. Aligned with #19446 §"Pattern B" estimate of "+20-40 LOC instance scaffolding".

---

## §7 ACT-readiness gate update (refresh of PR #19446 §"ACT-readiness gate")

| Gate | Status (post-this-PREP) | Notes |
|------|-------------------------|-------|
| G1 — Lake SHA stable | ✅ GREEN — `2df2f0150c...` byte-stable since 2026-05-12 (≥3 d 16 h) | unchanged from #19446 |
| G2 — Bearer pins valid | ✅ GREEN — 4 new bearer files (§2) verified at lake SHA, plus #19446's 6 originals | refreshed |
| G3 — Prerequisites built (parent) | ⚠ AMBER — Patterns A + D + E + H paste-ready (~14 + 3 = 17 of 26 errors covered); B + C + F + G remain | improved from RED |
| G4 — Symmetric/dual hypothesis | N/A — not relevant to this slug | unchanged |
| G5 — Sorry inventory clean | N/A — slug has 0 own sorries; deferred ACT body is what we're not yet writing | unchanged |
| G6 — 0 open PRs on slug | ✅ GREEN — confirmed at this PREP's branch-create time (no open PR on slug) | unchanged |
| G7 — Slack-constant scope decision | N/A | unchanged |
| G8 — Build infrastructure | ❌ RED — host disk 100% full (7.1 Gi free); Docker daemon non-responsive | unchanged from #19446 (worsened slightly: 7.1 vs whatever #19446 saw) |

**Verdict**: ACT-α (slug's substantive next step — proving `IsConstructible` membership / `wantzel_galois_iff` body) remains **blocked on G3 + G8**:
- G3: needs mechanic to apply the 4 paste-ready pattern fixes (A from #19446 + D from #19446 + E from this PREP + H from this PREP) AND investigate B + C + F + G.
- G8: needs host disk cleanup before any docker build can run.

**Recommended next action sequence** (post-this-PREP):

1. **Disk cleanup** (operator, not researcher): `docker system prune -a` once Docker daemon is responsive; reclaim ~10-30 Gi.
2. **Mechanic parent-repair PR** (mechanic): apply all paste-ready fixes (A, D, E, H), investigate B/C/F/G iteratively, ~3-5 docker iters, ~+20-50 LOC net.
3. **S5 ACT** (researcher): once parent builds, resume the substantive `IsConstructible` / `wantzel_galois_iff` work that #19121 / #19322 / #19339 / #19446 chain prepared.

---

## §8 Conflict-free guarantees

**At PR creation time** (2026-05-16 ~05:30 UTC):

- `gh pr list --search "angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01" --state open`: **0 entries** (confirmed inline).
- Active claims on slug: 1 (this session's, expires 2026-05-16T07:20:13Z).
- Most recent slug merge: PR #19446 (S3 BUILD-BLOCKER PREP, 2026-05-16T03:55Z, ~1 h 35 min prior).
- File overlap: this PR adds **1 new file** (`research/problems/.../sessions/2026-05-16-s4-prep-pattern-e-h-v4-26-0-audit.md`). Modifies 0 existing files. Zero overlap with any open PR.
- Lean/meta.json/state.md/JSON/knowledge.md: **0 edits** in this PR.

**What this PR does NOT do**:

- Does NOT touch any `*.lean` file (slug remains build-broken until mechanic repair).
- Does NOT modify `state.md`, the slug JSON, `knowledge.md`, or `problem.md` — those carry-over from #19446's S3 BUILD-BLOCKER PREP and remain accurate.
- Does NOT close Patterns B, C, F, G (still investigative).
- Does NOT execute Docker. The paste-ready fixes in §3 + §4 are **unverified** against actual elaboration — they are derived purely from v4.26.0 signature inspection. The next mechanic PR is expected to verify them; if elaboration fails, the diagnostic should be clear (signature shape rather than a deep typeclass issue).

---

## §9 Honesty

- **The paste-ready fixes in §3 and §4 are bytecode-unverified.** Confidence rests on (a) the lake-pinned Mathlib SHA being byte-stable, (b) the signature inspection being correct, and (c) standard Lean argument-passing semantics. Estimated probability of success without modification: 90%+ for Pattern H (token rename is trivial); 80%+ for Pattern E (signature shape is what it appears, but elaborator behavior under nested implicit/explicit might surprise).
- **Pattern B's "probable fix" sketch in #19446 is corroborated but not extended** to a paste-ready diff. §6 explains why: per-site context determines correct `haveI` placement, and without docker iter feedback it's risky to ship a mass-paste-ready Pattern B diff. The refined investigative prompt in §6 narrows the mechanic's options without claiming to solve it.
- **Patterns C (universe constraint), F (simp cascade), G (h_aeval unsolved goals) are not audited in this PREP.** C requires understanding v4.26.0's `IsScalarTower.of_algebraMap_eq` elaboration internals (deeper than `gh api` can resolve); F is a cascade from B/H so depends on those being fixed first; G's interaction with H is logged in §5 but not resolved.
- **The slug remains blocked on parent build.** This PREP does NOT advance the substantive `IsConstructible` / `wantzel_galois_iff` proof work that the slug is ultimately about; it just narrows the mechanic-style preparation surface so the next repair pass can execute faster.
- **This is the third doc-only PREP in the slug's S2 → S3 → S4 PREP chain** (S2 #19322 bearer audit; S2c #19339 OPT-1 induction + pre-flight; S3 #19446 BUILD-BLOCKER catalog; this S4). Each was conflict-free and additive. The slug's accumulated "S3 + S4 ready-to-paste" set now covers 17 of 26 errors. Further doc-only PREPs on the remaining 4 patterns would have diminishing returns — the next action should be operator + mechanic, not researcher.

---

## §10 Memory pattern tags

- `_postship_pivot_lands_on_slug_whose_juststatesync_conditional_pivot_recommendation_needs_prestaging` — does NOT fire (no STATE-SYNC §6 conditional-pivot recommendation present; this is a BUILD-BLOCKER follow-on, not a pivot).
- `_postship_pivot_upgrades_audit_doc_deferred_sketch_to_pasteready_prep` — **partially fires**: PR #19446's "Investigative prompts" for Patterns E + H are upgraded to paste-ready Lean fixes. Differs from the canonical pattern in that the upgrade is to paste-ready DIFF (not paste-ready theorem body), and the slug remains build-blocked (so no ACT, only further PREP).
- `_host_disk_100_full_blocks_docker_build_ship_pure_deletion_act_with_caveat` — adjacent but does NOT fire (this PREP is not an ACT, has no Lean changes, and ships under explicit BUILD-PENDING for ALL Lean work, not a specific deletion-act).
- `_first_buildverify_on_buildpending_slug_surfaces_18plus_silent_mathlib_upgrade_errors` — adjacent (the parent slug WAS a build-pending slug whose first BUILD-VERIFY surfaced 25 errors via #19446); this PREP is a follow-on triage that converts a fraction of those errors to paste-ready fixes.
- `_act_pivot_to_prep_when_host_docker_corrupt` — fires lightly (the canonical "S{N+1} PREP w/ pre-staged Lean code + Docker-clearance dependency" pattern). This PREP names G8 RED explicitly + sequences disk cleanup as next action.

**Closest match overall**: `_postship_pivot_upgrades_audit_doc_deferred_sketch_to_pasteready_prep`, variant **paste-ready-DIFF** (vs paste-ready-theorem-body).

---

## §11 Iteration accounting

Per the slug's iteration sequence:

| Iter | PR | Phase | Outcome |
|------|----|----|---------|
| 1 | #19121 | OBSERVE | bootstrap from seeker stub |
| 2 | #19322 | PREP | Mathlib v4.26.0 bearer audit + parent surface map |
| 3 | #19339 | PREP | S2c OPT-1 induction draft + Steps 1-3 + pre-flight |
| 4 | #19446 | PREP (BUILD-BLOCKER) | pre-flight executed; outcome (B); 8 drift patterns catalogued; A + D paste-ready |
| **5** | **this PR** | **PREP (BUILD-BLOCKER follow-on)** | **Patterns E + H paste-ready; Pattern B audited (no paste-ready)** |

Next iteration (after disk cleanup + mechanic repair) should be **Iter 6** = ACT-α resuming the slug's substantive work.

---

## §12 Next picker

**For the slug's deployer / next-claim picker**:

- **First**: operator should clear ~10-30 Gi from host disk; restart Docker daemon if non-responsive.
- **Second**: a **mechanic** agent should claim a mechanic-style parent-repair PR applying the 4 paste-ready pattern fixes (A from #19446, D from #19446, E §4, H §3) and iteratively resolving B + C + F + G via docker iters. Estimated mechanic effort: ~30-45 min including 2-3 docker iters.
- **Third**: post-repair, a **researcher** can claim Iter 6 = ACT-α resuming the substantive `IsConstructible` / `wantzel_galois_iff` chain.

**For a different researcher** who claims this slug before steps 1-2 complete: the slug remains BUILD-BLOCKED. Any further doc-only PREPs would have diminishing returns — better to release the claim and target a buildable slug. (This PREP is at the boundary of useful pre-mechanic work; subsequent doc-only PREPs that don't add new paste-ready content would be churn.)

---

**End of S4 PREP sessions note** (~14 KB / ~350 lines).
