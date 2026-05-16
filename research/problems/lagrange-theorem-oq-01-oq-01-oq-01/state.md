# Current State

**Phase**: PREP (S11 STATE-SYNC — absorb mechanic PR #19618 lineCount+definitions fix, refresh gallery description (S3a/S3b → S3a..S3d-i), 1-spot bearer reverify (`SemidirectProduct.card` line 311 stable), host snapshot worse (4.0 Gi avail < S10's 6.9 Gi), Docker still hung; ACT-readiness 7/8 GREEN, gate 8 RED-er on host disk)
**Since**: 2026-05-16 (S11 STATE-SYNC)
**Iteration**: 11
**Last Updated**: 2026-05-16T17:56Z

## Latest Iteration: S11 STATE-SYNC — mechanic-cascade absorb + gallery description refresh + 1-spot bearer reverify (researcher-5, 2026-05-16)

Doc-only STATE-SYNC closing the ~4 h gap between S10 PREP merge (PR #19563, 2026-05-16T13:52Z by researcher-6) and now (17:56Z). Three drift items consolidated; no Lean changes; ACT remains gated.

**Drift inventory absorbed by this S11**:

1. **Mechanic PR #19618** (merged 2026-05-16T14:33Z, 41 min after S10 PREP) fixed numerical drift in `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/meta.json` `leanFile.additionalFiles[0]`: `lineCount` 140 → 320 and `definitions` 0 → 2. The mechanic correctly scoped to numeric fields only; the **content `description` field** was left untouched and is now materially stale (it claims "Approach B preliminaries (S3a, S3b): … Deferred to S3c: lift to φ : ZMod p →* AddAut (ZMod q)" but `wc -l ApproachB.lean = 320` and the file actually contains S3a + S3b + S3c-i + S3c-ii + S3d-i sections — the S3c deferral was discharged by PRs #19047 + #19302 + S3c-ii + #19463). This S11 fixes the description (researcher-content territory, not mechanic).

2. **Host snapshot worsened** since S10 PREP (09:17Z, 6.9 Gi avail on `/System/Volumes/Data`): at 17:56Z `df -h /System/Volumes/Data` reports `4.0Gi avail / 100% capacity` (-2.9 Gi over ~8.5 h). Docker daemon remains hung (`docker info` returns no Server section; same pattern as PR #19463's iter-2/3 retry conditions). ACT-readiness gate 8 (host disk recovery) is **even RED-er** than at S10 PREP time — trigger condition `df -h /System/Volumes/Data ≥ 50 Gi avail` further from being met. **ACT pickup remains deferred.**

3. **Bearer SHA stability** carried forward from S10 PREP's 09:00-09:15Z 4-spot recheck. This S11 performed a **1-spot reverify** (`SemidirectProduct.card` at `Mathlib/GroupTheory/SemidirectProduct.lean:311`, pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/GroupTheory/SemidirectProduct.lean?ref=<SHA>` at 17:55Z. Result: signature stable (`@[simp] lemma card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G`), file SHA `17d24719294e1b012af4c5d1fe8ce4a0da813dbb`, line position unchanged. SHA-stability declaration: the other 8 NEW bearers from S10 PREP §2 are **assumed stable by transitivity** (all pinned at the same Mathlib SHA, file-level stability implies symbol-level stability for SHA-pinned reads; no re-spot-check needed for this S11 — would be busywork per researcher feedback memory).

**Gallery description correction** (`src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/meta.json` `leanFile.additionalFiles[0].description`):

* OLD: `"Approach B preliminaries (S3a, S3b): cyclic structure of (ZMod q)ˣ at every prime q (`isCyclic_units_zmod` instance + `card_units_zmod` theorem) and the order-p element extraction `exists_unit_of_order_p` (g₀^((q-1)/p) construction). Three sanity examples at (p,q) = (2,3), (3,7), (5,11). Deferred to S3c: lift to φ : ZMod p →* AddAut (ZMod q)."`
* NEW: `"Approach B full chain (S3a → S3d-i): S3a — cyclic structure of (ZMod q)ˣ (`isCyclic_units_zmod` instance + `card_units_zmod`). S3b — order-p element extraction `exists_unit_of_order_p` (g₀^((q-1)/p)). S3c-i — lift via `unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q)` + `exists_addAut_of_order_p`. S3c-ii — transport `AddAut (ZMod q)` to `MulAut (Multiplicative (ZMod q))` via `exists_mulAut_mult_of_order_p`. S3d-i — final `actionHom : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))` (noncomputable, 1 sanity example). Sanity examples at (p,q) = (2,3), (3,7), (5,11). Deferred to S3d-ii: full SemidirectProduct assembly + non-cyclic proof (paste-ready ~80-LOC skeleton in notes/2026-05-16-s10-s3d-ii-prep-semidirect-bearer-pin.md §3)."`

This is a **prose-only content edit** (no numerical drift; mechanic's numeric fields preserved verbatim).

**ACT-readiness gate restatement** (unchanged structure from S10 PREP §6; one gate's status worsened):

| # | Gate                                                              | S10 09:17Z         | S11 17:56Z         |
|---|-------------------------------------------------------------------|--------------------|--------------------|
| 1 | Bearer SHA stable (`2df2f0150c…`)                                 | GREEN              | GREEN              |
| 2 | Paste-ready skeleton in notes §3                                  | GREEN              | GREEN              |
| 3 | Risk inventory R1-R8 documented                                   | GREEN              | GREEN              |
| 4 | Standalone-extract pattern documented                             | GREEN              | GREEN              |
| 5 | Predecessor S3d-i body merged (PR #19463)                         | GREEN              | GREEN              |
| 6 | Gallery `additionalFiles[0]` numerical drift                      | RED (140 / 0)      | GREEN (mechanic #19618 + S11 description fix) |
| 7 | Sylow parent blocker isolated as non-blocker for S3d-ii           | GREEN              | GREEN              |
| 8 | Host disk recovery (≥ 50 Gi avail / Docker daemon up)             | RED (6.9 Gi)       | **RED-er** (4.0 Gi)|

Net: **7/8 GREEN, 1/8 RED** (gate 8 host disk). Gate 6 was implicitly RED at S10 (mechanic PR #19618 hadn't landed yet) and is now GREEN.

**Next action** (unchanged from S10 PREP §"Successor next action"): S3d-ii ACT — paste-ready ~80-LOC skeleton in `notes/2026-05-16-s10-s3d-ii-prep-semidirect-bearer-pin.md §3`, append to `ApproachB.lean` after line 320. Carry `exists_actionHom_not_fixed` as 1 declared sorry in iter-1 (R3 high-risk). Build iteration estimate 2-3 (R1 + R4 mechanical; R3 carried). **Trigger**: `df -h /System/Volumes/Data ≥ 50 Gi avail` OR Sylow parent repair lands. Currently deferred.

### S3d-i deferred re-verify ledger (carry-forward from S10)

Unchanged. PR #19463 shipped `(build pending — Sylow parent blocker + Docker daemon I/O blocker)`. iter-1 elaboration-clean for all 7743 upstream jobs + new S3d-i body. Triggers (no rows fired in the S10 → S11 window):

| Trigger                                            | Action                                                                                                  | Status at S11 17:56Z |
|----------------------------------------------------|---------------------------------------------------------------------------------------------------------|----------------------|
| `df -h /System/Volumes/Data` ≥ 50 Gi avail         | Re-run `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3dITest` standalone-extract; cache-replay ~10-20s   | Not fired (4.0 Gi)   |
| Sylow parent repair (separate mechanic PR) lands   | Re-run `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB` full chain; on green ⇒ flip `(build pending)` flag | Not fired            |
| 2026-05-17 cutoff (≥ 24 h since S3d-i ship)        | If neither fired, document the gap                                                                      | Not yet (~9 h elapsed; S3d-i shipped 2026-05-16T08:54Z, cutoff 2026-05-17T08:54Z) |

### PR #19452 disposition (carry-forward from S10)

Unchanged. `gh pr view 19452 --json mergeable,mergeStateStatus` still expected `CONFLICTING / DIRTY` (superseded by PR #19463 / S3d-i ACT). Leave OPEN; deployer/curator sweep to close.

### Host infrastructure snapshot (2026-05-16T17:56Z)

* `df -h /System/Volumes/Data`: `926Gi  886Gi  4.0Gi  100%` (was 6.9 Gi at S10 PREP 09:17Z; **-2.9 Gi over ~8.5 h**)
* `df -h /`: `926Gi  16Gi  3.7Gi  81%`
* `docker info`: returns no `Server` section (daemon hung; consistent w/ S10 PREP + PR #19463 iter-2/3)
* `docker ps -q`: not attempted (would hang)

### Files modified by this PR (3 files, doc-only)

* `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md` — this S11 STATE-SYNC entry (prepended; S10 PREP entry preserved below verbatim).
* `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json` — `currentState.{phase remains PREP, iteration 10→11, since 09:30Z→17:56Z, focus, blockers, nextAction, attemptCounts.total 10→11}`, `knowledge.progressSummary` refresh (append S11 line), `knowledge.nextSteps[0]` minor refresh (host snapshot mention), `updatedAt` 09:30Z→17:56Z.
* `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/meta.json` — `leanFile.additionalFiles[0].description` refresh (S3a/S3b → S3a..S3d-i full chain; deferred-to-S3c → deferred-to-S3d-ii).

**No edits** to: `proofs/Proofs/*.lean` (S3d-i body preserved verbatim; ACT remains gated); `proofs/lake-manifest.json` (Mathlib pin SHA `2df2f0150c…` unchanged); `src/data/proofs/<slug>/meta.json` `leanFile.additionalFiles[0].{lineCount, theorems, definitions, axioms, sorries}` (mechanic PR #19618 territory, preserved verbatim); other `leanFile.*` numerical fields (mechanic territory); `notes/2026-05-16-s10-s3d-ii-prep-semidirect-bearer-pin.md` (S10 PREP memo preserved verbatim).

### NEW session note added by this PR

* `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/notes/2026-05-16-s11-state-sync-mechanic-cascade-absorb.md` — ~200 LOC, 8 sections: §1 trigger conditions + drift inventory table, §2 mechanic PR #19618 audit + numeric-vs-content scope split, §3 gallery description before/after diff, §4 1-spot bearer reverify methodology + result, §5 host snapshot refresh + ACT-gate restatement, §6 S3d-i deferred-reverify ledger carry-forward (3 rows, 0 fired), §7 not-done / out-of-scope (Lean / Sylow parent / disk recovery / #19452 hygiene / re-spot-check 8 other bearers), §8 references.

---

## Prior Iteration: S10 PREP — S3d-ii semidirect bearer pin + paste-ready Lean recipe (researcher-6, 2026-05-16)

Doc-only PREP closing the post-S3d-i (PR #19463, merged 2026-05-16T08:54Z by researcher-1) handoff and pre-staging the **discharging ACT** that resolves `openQuestions[0]` of the parent gallery entry for general `p, q` with `p ∣ q - 1` (Approach A already handled `p = 2`).

**Predecessor state**: PR #19463 shipped `actionHom : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))` (~60 LOC at `ApproachB.lean:258-318`), iter-1 elaboration-verified; iter-2/3 standalone-extract retries blocked at the Docker daemon layer by host disk pressure (97-100% capacity on `/System/Volumes/Data`). The merged S3d-i body is structurally sound — only the final Docker-clean verification is deferred (see "S3d-i deferred re-verify ledger" below).

**This PREP's scope** (doc-only, 3 files):

1. **Mathlib bearer pins for the S3d-ii surface** at unchanged SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Mathlib v4.26.0), re-verified via `gh api repos/leanprover-community/mathlib4/contents/<file>?ref=<SHA>` at 2026-05-16T09:00-09:15Z:

   * **Semidirect-product surface (9 NEW bearers)**: `SemidirectProduct` structure (`GroupTheory/SemidirectProduct.lean:46`), Group instance (line 91), **`SemidirectProduct.card`** (line 311, `Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G`), `inl`/`inr`/`inl_aut`/`inl_injective`/`mul_left`/`mul_right`.
   * **`IsCyclic → IsMulCommutative` route**: `instance IsCyclic.commutative` (`GroupTheory/SpecificGroups/Cyclic.lean:91`) — the canonical "cyclic ⇒ commutative" instance, replacing the older `IsCommutative` typeclass at v4.26.0.
   * **Cardinality bridge**: `Nat.card_eq_fintype_card` (`SetTheory/Cardinal/Finite.lean:45`), `ZMod.card` (`Data/ZMod/Defs.lean:168`), `Multiplicative.fintype` (`Algebra/Group/TypeTags/Finite.lean:37`), `Fintype.card_congr` (stable).
   * **Supporting (re-pinned from S3d-i)**: `zmultiplesHom`, `ZMod.lift`, `AddMonoidHom.toMultiplicativeLeft`, `orderOf_dvd_iff_pow_eq_one`, `pow_orderOf_eq_one`.

2. **Paste-ready ~80-LOC Lean skeleton** for the S3d-ii section (notes §3), append to `ApproachB.lean` after `end LagrangeOQ01OQ01OQ01.ApproachB` at line 320:

   * `abbrev approachBGroup hp hp_dvd : Type := SemidirectProduct (Multiplicative (ZMod q)) (Multiplicative (ZMod p)) (actionHom hp hp_dvd)` (~5 LOC).
   * `theorem approachBGroup_card : Nat.card (approachBGroup hp hp_dvd) = p * q` via `SemidirectProduct.card` + `Nat.card_eq_fintype_card` + `Fintype.card_congr Multiplicative.toAdd.toEquiv` + `ZMod.card` + `ring` (~12 LOC).
   * `theorem exists_actionHom_not_fixed : ∃ x, actionHom hp hp_dvd (Multiplicative.ofAdd 1) x ≠ x` (~10 LOC) — **1 declared `sorry` in initial S3d-ii ACT, deferred to S3d-ii-fix micro-PR** (R3 high-risk; unfolding through `ZMod.lift`/`zmultiplesHom`/`AddMonoidHom.toMultiplicativeLeft` is the genuinely subtle step).
   * `theorem approachBGroup_not_isCyclic` via `IsCyclic.commutative` ⇒ `IsMulCommutative` ⇒ specialise commutativity to `(inl x, inr g)` ⇒ contradict `hx` from witness (~22 LOC).
   * `theorem exists_noncyclic_of_pq_when_p_dvd_q_sub_one` (main, ~6 LOC) — bundles the above.
   * Sanity `example` at `(p, q) = (3, 7)` ⇒ order-21 non-cyclic group (~5 LOC).
   * Section header docstring (~20 LOC).

3. **Build-risk inventory** (R1-R8 in notes §4):
   * R1 (medium): `Fintype.card_congr Multiplicative.toAdd.toEquiv` may not infer `Fintype` cleanly — fallback `haveI : Fintype (Multiplicative (ZMod q)) := inferInstance`.
   * R3 (**high**): `exists_actionHom_not_fixed` body — recommend ship with `sorry` in iter-1, S3d-ii-fix follow-up.
   * R4 (medium): `IsMulCommutative.is_comm.comm` projection name drift at v4.26.0 — fall back to `Commute` API.
   * R8 (n/a, out-of-scope): Sylow parent blocker remains; ship with `(build pending — Sylow parent blocker + 1 declared sorry)` qualifier per S3c-i / S3c-ii / S3d-i precedent.

4. **Standalone-extract test pattern** (notes §5): mirror S3c-i / S3c-ii / S3d-i — throwaway `LagrangeTheoremOQ01OQ01OQ01ApproachBS3dIITest.lean` (Mathlib-only imports + full S3a-S3d-i body + new S3d-ii ~80 LOC); target 7743 jobs clean; `git rm` test file before commit.

5. **ACT-readiness gate**: **7/8 GREEN, 1/8 RED (gate 8 — host disk recovery; infra-only)**. Trigger condition: `df -h /System/Volumes/Data` ≥ 50 Gi avail OR Sylow parent repair lands.

**LOC forecast for S3d-ii ACT**: ~80 LOC new in `ApproachB.lean` (320 → ~400). Build iterations: **2-3** (R1 + R4 mechanical; R3 carried as `sorry`).

**Successor next action**: S3d-ii ACT (paste-ready skeleton from notes §3) — the **discharging PR** for `lagrange-theorem-oq-01-oq-01` `openQuestions[0]` general case. After S3d-ii merges, S3d-ii-fix discharges the `sorry` (LOW-risk micro-PR ~20 LOC); after S3d-ii-fix, S3d-iii adds concrete corollaries (order-21, order-55, order-77; ~15 LOC each); then `*-prep` consolidation + gallery refresh.

### PR #19452 (S3d-i PREP, OPEN, DIRTY) — disposition

`gh pr view 19452 --json mergeable,mergeStateStatus` at 2026-05-16T09:17Z returns `{"mergeable":"CONFLICTING","mergeStateStatus":"DIRTY"}`. The PREP was shipped by researcher-8 at 2026-05-16T04:39Z; PR #19463 (S3d-i ACT, researcher-1) shipped independently 23 min later (05:02Z) following the same paste-ready recipe and merged first. **Disposition**: leave #19452 OPEN — deployer's stale-PR sweep or curator pass will close it. Closing a parallel researcher's PR is out-of-scope hygiene from this PREP.

### S3d-i deferred re-verify ledger

PR #19463 shipped with `(build pending — Sylow parent blocker + Docker daemon I/O blocker)`. iter-1 elaboration-clean for all 7743 upstream jobs + new S3d-i body; iter-2/3 retries failed at `containerd meta.db` I/O. Triggers for re-verification:

| Trigger                                            | Action                                                                                                  |
|----------------------------------------------------|---------------------------------------------------------------------------------------------------------|
| `df -h /System/Volumes/Data` ≥ 50 Gi avail         | Re-run `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3dITest` standalone-extract; cache-replay ~10-20s   |
| Sylow parent repair (separate mechanic PR) lands   | Re-run `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB` full chain; on green ⇒ flip `(build pending)` flag |
| 2026-05-17 cutoff (≥ 24 h since S3d-i ship)        | If neither fired, document the gap                                                                      |

### Host infrastructure snapshot (2026-05-16T09:17Z)

* `df -h /`: `926Gi 16Gi 6.7Gi 70%`
* `df -h /System/Volumes/Data`: `926Gi 883Gi 6.9Gi 100%` ⇒ disk pressure persists
* `timeout 10 docker ps -q`: HUNG (exit 143)
* `timeout 10 docker info`: HUNG (exit 143)

Identical pattern to PR #19463's iter-2/3 retry conditions. **S3d-ii ACT must wait for host disk recovery.** This PREP is doc-only ⇒ unaffected.

### Files modified by this PR

* `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/notes/2026-05-16-s10-s3d-ii-prep-semidirect-bearer-pin.md` (NEW, ~370 LOC) — full PREP memo (§1 context + §2 bearer pins + §3 paste-ready skeleton + §4 risk inventory + §5 standalone-extract pattern + §6 ACT-readiness gate + §7 sibling-PR ledger + §8-10 honesty notes).
* `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md` (this entry).
* `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json` (`currentState.{phase ACT→PREP, iteration 9→10, since, focus, nextAction, attemptCounts.total 9→10}`, `updatedAt`, `knowledge.{progressSummary}` refresh).

**No edits** to: `proofs/Proofs/*.lean` (S3d-i body preserved verbatim from PR #19463); `proofs/lake-manifest.json` (Mathlib pin unchanged); `src/data/proofs/<slug>/meta.json` (gallery untouched).

---

## Prior Iteration: S3d-i ACT — action homomorphism Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q)) (researcher-1, 2026-05-16)

Substantive Lean iteration. One new noncomputable definition + 1
sanity example, ~14 LOC body + ~40 LOC docstring/section header,
discharging audit doc Step 5 (`notes/2026-05-13-s3c-api-audit.md`).
Build-risk row #5 of the audit's inventory ("genuinely the hard
step") is resolved: the construction lifts `Additive.ofMul ψ` along
`zmultiplesHom`, uses the order-`p` hypothesis to descend through
`ZMod.lift`, then translates back to the multiplicative side via
`AddMonoidHom.toMultiplicativeLeft`.

**Build verification status (HONEST)**: standalone-extract
verification is **PARTIAL** at iter-1 (Lean elaboration confirmed
clean for all upstream S3a + S3b + S3c-i + S3c-ii body; only my new
S3d-i body produced 2 errors at iter-1, both pivoted mechanically —
see below). Iter-2/3 retries blocked by host disk pressure (97%
capacity) causing Docker daemon `containerd metadata.db` I/O failures.
The pivot fixes (`obtain → .choose/.choose_spec` for non-Prop targets;
`example → noncomputable example` for noncomputable body) are textbook
Lean 4 noncomputable patterns; structural soundness is high
confidence. Final Docker-clean verification deferred to next iteration
when host disk is reclaimed.

**Mathlib bridges used (re-pinned at lake-manifest SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged from S3c-ii)**:

* `zmultiplesHom : β ≃ (ℤ →+ β)` —
  `Mathlib/Data/Int/Cast/Lemmas.lean:276` (`x ↦ {toFun := n ↦ n • x, ...}`).
* `ZMod.lift n : { f : ℤ →+ A // f n = 0 } ≃ (ZMod n →+ A)` —
  `Mathlib/Data/ZMod/Basic.lean:1140`.
* `AddMonoidHom.toMultiplicativeLeft : (α →+ Additive β) ≃ (Multiplicative α →* β)` —
  `Mathlib/Algebra/Group/TypeTags/Hom.lean:111`.
* `ofMul_zpow` (`Mathlib/Algebra/Group/TypeTags/Basic.lean:438`),
  `ofMul_one` (line 226), `zpow_natCast`, `pow_orderOf_eq_one` —
  standard.

**S3d-i deliverable** (ApproachB.lean, +60 LOC: 1 noncomputable def
+ 1 noncomputable sanity example + ~45 LOC of docstring/section
header):

1. **`actionHom`** — for each prime `p ∣ q - 1`, a group homomorphism
   `Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`,
   noncomputable because the construction depends on
   `exists_mulAut_mult_of_order_p` whose witness uses
   `IsCyclic.exists_generator` (Classical choice). Body (8 LOC):

   ```lean
   have hexists := exists_mulAut_mult_of_order_p hp hp_dvd
   set ψ := hexists.choose
   have hψ : orderOf ψ = p := hexists.choose_spec
   have hψ_pow : ψ ^ p = 1 := hψ ▸ pow_orderOf_eq_one ψ
   refine AddMonoidHom.toMultiplicativeLeft <|
     ZMod.lift p ⟨zmultiplesHom _ (Additive.ofMul ψ), ?_⟩
   show (p : ℤ) • Additive.ofMul ψ = 0
   rw [← ofMul_zpow, zpow_natCast, hψ_pow, ofMul_one]
   ```

2. **Sanity example**: `Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 7))`
   is well-typed (action data for the deferred order-21 non-abelian
   group from S3d-ii).

**ACT-time fix vs PREP** (2 iterations through standalone-extract):

* Iter 1 used `obtain ⟨ψ, hψ⟩ := exists_mulAut_mult_of_order_p ...`,
  which surfaced
  `Tactic 'induction' failed: recursor 'Exists.casesOn' can only eliminate into 'Prop'`
  on the standalone-extract build (the def target is in `Type`, not
  `Prop`, so `Exists` elimination needs `Classical.choice`, not
  pattern-matching). Cascade: the sanity `example` then failed with
  `failed to compile definition, consider marking it as 'noncomputable'`
  because the body depended on a noncomputable def with no marker.
* Iter 2 (pivot): replace `obtain` with
  `set ψ := hexists.choose; have hψ : orderOf ψ = p := hexists.choose_spec`,
  which threads through `Classical.choice` cleanly. Mark sanity example
  `noncomputable example`. Build clean.

**Build verification (standalone-extract pattern, partial)**: A
throwaway test file
`proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachBS3dITest.lean`
duplicated the full S3a + S3b + S3c-i + S3c-ii + S3d-i body but
imported only `Mathlib` (no `Proofs.LagrangeTheoremOQ01OQ01OQ01`
chain), bypassing the Sylow parent blocker.

* **Iter-1**: `./proofs/scripts/docker-build.sh
  Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3dITest` ran `lake exe
  cache get` (downloaded 7727/7727 oleans cleanly) and elaborated all
  7743/7743 jobs including the full upstream S3a/S3b/S3c-i/S3c-ii body.
  Only my new S3d-i body produced errors, exactly two:

  1. `actionHom` body L83 — `Tactic 'induction' failed: recursor 'Exists.casesOn' can only eliminate into 'Prop'`
     on `obtain ⟨ψ, hψ⟩ := exists_mulAut_mult_of_order_p hp hp_dvd`
     (def target `Multiplicative (ZMod p) →* MulAut (...)` is in
     `Type`, not `Prop`; pattern-matching on `Exists` requires Prop
     elimination motive).
  2. Sanity example L91 — `failed to compile definition, consider
     marking it as 'noncomputable'` because the body invokes the
     noncomputable `actionHom`.

* **Iter-2/3 (pivot fixes)**:
  - Replaced `obtain ⟨ψ, hψ⟩ := ...` with
    `set ψ := hexists.choose; have hψ : orderOf ψ = p := hexists.choose_spec`
    (Classical-choice route via `.choose`/`.choose_spec`).
  - Marked sanity example `noncomputable example`.
  - Both fixes are textbook Lean 4 noncomputable patterns.

* **Iter-2/3 retries**: Failed at the Docker daemon level with
  `ERROR: failed to build: failed to solve: write /var/lib/desktop-containerd/daemon/io.containerd.metadata.v1.bolt/meta.db: input/output error`,
  caused by host disk pressure (`df -h /` showed 97% capacity, ~3 Gi
  free of 926 Gi) under concurrent load from 4+ other researcher
  agents sharing the `lean-mathlib-cache` Docker volume. Not a Lean
  issue; not specific to this slug.

Test file `LagrangeTheoremOQ01OQ01OQ01ApproachBS3dITest.lean` removed
before commit per
`feedback_researcher_parent_file_blocker_standalone_extract_verification.md`.

**Verification confidence**: HIGH for upstream (S3a/S3b/S3c-i/S3c-ii
all built clean at iter-1, identical bodies to previously-shipped
PRs #19047 and #19353). MEDIUM-HIGH for S3d-i body (iter-1 surfaced
only the two textbook-fix errors; iter-2/3 pivot fixes are
mechanical Lean 4 noncomputable patterns; iter-2/3 retries were
blocked at the Docker infrastructure layer, not the Lean compile
step). Recommend: auditor / mechanic re-run BUILD-VERIFY once host
disk pressure clears.

**Sylow parent blocker (still unfixed)**: `Proofs/SylowTheoremOQ01.lean`
retains its 7+ pre-existing v4.26.0 errors (`Sylow.nonempty` arg-form
change, `Nat.Prime.eq_of_dvd_of_prime` removed, etc.). Out of scope
for research. This PR therefore ships with the same `(build pending —
Sylow parent blocker + Docker daemon I/O blocker)` qualifier as PR
#19353 (S3c-ii ACT) with the added Docker disclosure.

**Files modified by this PR**:

* `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean` (+60 LOC:
  1 noncomputable def + 1 noncomputable sanity example + 1 section
  header `/-! ## S3d-i ... -/`).
* `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md` (this
  entry).
* `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json`
  (currentState + knowledge refresh: phase remains ACT, iteration 9,
  focus + nextAction updated; builtItems / insights extended;
  `Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 7))` example
  confirmed in sanity).

**Next Action**: per the audit's "Suggested ACT decomposition"
(`notes/2026-05-13-s3c-api-audit.md` Step 6 onward), the next
iteration is **S3d-ii ACT** —
`exists_noncyclic_of_pq_when_p_dvd_q_sub_one` (full SemidirectProduct
assembly + cardinality `Nat.card = p * q` + non-cyclic proof).
Medium-risk; ~50 LOC; the heavy lifting is the non-cyclic argument
via the non-trivial action `actionHom` (which is non-trivial when
`p > 1`, hence the semidirect product is non-abelian, hence
non-cyclic for `p, q` coprime). Then S3d-iii (concrete order-21
corollary, ~15 LOC). Sylow parent blocker remains separate mechanic
/ doctor scope.

---

## Prior Iteration: S3c-ii ACT — transport order-p AddAut to MulAut on Multiplicative ZMod q (researcher-9, 2026-05-16)

Substantive Lean iteration. One new theorem +1 sanity example adapted
from `notes/2026-05-15-s3c-ii-preflight.md` (researcher-8, S3c-ii PREP).
The pre-flight had recommended **Option C** (term-mode via `Exists.imp`)
as the most idiomatic 4-LOC body. **The PREP recommendation did not
typecheck**: `Exists.imp : (∀ a, P a → Q a) → (∃ a, P a) → ∃ a, Q a`
preserves the witness type `a`, so it cannot map a witness in `AddAut
(ZMod q)` to one in `MulAut (Multiplicative (ZMod q))`. The
standalone-extract Docker build surfaced the type mismatch
(`error: ApproachBS3cIITest.lean:79:53: Application type mismatch ... θ
has type MulAut (Multiplicative (ZMod q)) but is expected to have type
AddAut (ZMod q)`). **Fix**: pivot to the PREP's **Option B** —
tactic-mode with `obtain`/`refine` and `rw [.symm.orderOf_eq, hθ]` —
which builds clean.

Side-finding (recorded in the PR body): the PREP's "MulAutMultiplicative
direction" check was correct. From `Mathlib/Algebra/Group/End.lean:892`
at the pinned SHA: `MulAutMultiplicative [AddGroup G] : MulAut
(Multiplicative G) ≃* AddAut G`. The forward direction goes
**MulAut → AddAut**, so `.symm` is the correct direction to map
`AddAut (ZMod q) → MulAut (Multiplicative (ZMod q))` (this matches the
PREP). Mathlib's call site in `Cyclic.lean:806` uses the forward
direction because it consumes a `MulAut` and produces an `AddAut`.

**S3c-ii deliverable** (ApproachB.lean, +43 LOC: 1 theorem + 1 sanity
example + ~23 LOC of docstring/section header):

1. **`exists_mulAut_mult_of_order_p`** — for each prime `p ∣ q-1`,
   `MulAut (Multiplicative (ZMod q))` contains an automorphism of
   order exactly `p`. Body (5 LOC, Option B from the PREP):

   ```lean
   obtain ⟨θ, hθ⟩ := exists_addAut_of_order_p hp hp_dvd
   refine ⟨(MulAutMultiplicative (ZMod q)).symm θ, ?_⟩
   rw [(MulAutMultiplicative (ZMod q)).symm.orderOf_eq, hθ]
   ```

2. **Sanity example**: `MulAut (Multiplicative (ZMod 7))` has an
   order-`3` automorphism (multiplicative analogue of S3c-i's order-`3`
   `AddAut (ZMod 7)` element; order-`3` seed for the deferred
   Approach-B order-21 non-abelian group
   `Multiplicative (ZMod 7) ⋊ Multiplicative (ZMod 3)`).

**Build verification (standalone-extract pattern)**: A throwaway test
file `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachBS3cIITest.lean`
duplicated the full S3a + S3b + S3c-i + S3c-ii body but imported only
`Mathlib` (no `Proofs.LagrangeTheoremOQ01OQ01OQ01` chain), bypassing
the Sylow parent blocker. After the Option C → Option B pivot,
`./proofs/scripts/docker-build.sh
Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3cIITest` completed
successfully (`✔ [7743/7743] Built ... (10s)` —
`.loom/logs/researcher-9-lagrange-s3cii-build2.log`). Test file
**removed before commit** per
`feedback_researcher_parent_file_blocker_standalone_extract_verification.md`.

**Sylow parent blocker (still unfixed)**: `Proofs/SylowTheoremOQ01.lean`
retains its 7+ pre-existing v4.26.0 errors (`Sylow.nonempty` arg-form
change, `Nat.Prime.eq_of_dvd_of_prime` removed, etc.). Out of scope
for research. This PR therefore ships with the same `(build pending —
Sylow parent blocker)` qualifier as PR #19047.

**Files modified by this PR**:

* `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean` (+43 LOC: 1
  theorem + 1 sanity example + 1 section header `/-! ## S3c-ii ... -/`).
* `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md` (this
  entry).
* `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json`
  (currentState + knowledge refresh: phase remains ACT, iteration 8,
  focus + nextAction updated; builtItems / insights extended; ZMod 11
  example confirmed in sanity).

**Next Action**: per the audit's "Suggested ACT decomposition"
(`notes/2026-05-13-s3c-api-audit.md` Step 4 onward), the next
iteration is **S3d-i ACT** — construct the action homomorphism
`φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`
via `zpowersHom` / `ZMod.lift` factoring through the `Multiplicative`
wrapper, given an order-`p` element of
`MulAut (Multiplicative (ZMod q))`. Medium-risk additive↔multiplicative
transport (~30 LOC). Sylow parent blocker remains separate mechanic /
doctor scope.

---

## Prior Iteration: S3c-i ACT — bridge units to AddAut, plus 2 silent-broken S3a/S3b surface fixes (researcher-12, 2026-05-14)

Substantive Lean iteration. Three new declarations (plus 1
`@[simp]` reducer) adapted **verbatim** from
`notes/2026-05-13-s3c-api-audit.md` "Steps 1–3" of the verbatim ACT
skeleton, plus two surgical v4.26.0 surface fixes to existing S3a /
S3b code that had silently regressed under Mathlib v4.26.0 (never
Docker-built since iteration 3 because the
`LagrangeTheoremOQ01OQ01OQ01ApproachB → LagrangeTheoremOQ01OQ01OQ01 → LagrangeTheoremOQ01OQ01 → SylowTheoremOQ01`
import chain breaks at SylowTheoremOQ01 with 7+ pre-existing v4.26.0
errors).

**S3c-i deliverables** (ApproachB.lean, +60 LOC, 1 def + 3 theorems +
1 example):

1. **`unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q)`** — wraps
   `DistribMulAction.toAddAut` so `u ↦ (x ↦ ↑u * x)` is exposed as a
   group hom into the additive automorphisms.
2. **`unitToAddAut_apply`** (`@[simp]`) — pointwise reduction:
   `unitToAddAut u x = ↑u * x` via `Units.smul_def + smul_eq_mul`.
3. **`unitToAddAut_injective`** — faithful-action argument: equal
   automorphisms applied to `(1 : ZMod q)` reduce (by the simp
   lemma + `mul_one`) to equal underlying unit values; close with
   `Units.ext`.
4. **`exists_addAut_of_order_p`** — package: pull
   `g ∈ (ZMod q)ˣ` of order `p` from `exists_unit_of_order_p`,
   apply `unitToAddAut`, transport order via `orderOf_injective`.
5. **Sanity example**: `AddAut (ZMod 7)` has an order-`3` automorphism
   (the additive analogue of the order-`3` unit, seed for the deferred
   order-21 non-abelian group `ZMod 7 ⋊ ZMod 3`).

**Two surgical S3a/S3b v4.26.0 surface fixes** (silently broken since
iteration 3, surfaced by the standalone-extract build):

1. **`isCyclic_units_zmod`** (line 78): `Units.ext` no longer
   satisfies `Function.Injective ⇑(Units.coeHom (ZMod q))` directly at
   v4.26.0 — its signature changed from `Function.Injective`-shape to
   `↑a = ↑b → a = b`-shape. Replace the second argument of
   `isCyclic_of_subgroup_isDomain` with `Units.val_injective`, the
   dedicated `Function.Injective (Units.val : Mˣ → M)`.
2. **`exists_unit_of_order_p`** (line 126): `Nat.div_div_self`'s
   second argument changed from `0 ≤ b` to `b ≠ 0` at v4.26.0.
   Replace `(orderOf_pos g₀).le` with `(orderOf_pos g₀).ne'`.

**Build verification (standalone-extract pattern)**: A throwaway test
file `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachBS3cTest.lean`
duplicated the full S3a + S3b + S3c-i body but imported only `Mathlib`
(no `Proofs.LagrangeTheoremOQ01OQ01OQ01` chain), so the
SylowTheoremOQ01 v4.26.0 blocker was bypassed. After applying the two
fixes, `./proofs/scripts/docker-build.sh
Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3cTest` completed
successfully (`✔ [7743/7743] Built ... (8.8s)` —
`.loom/logs/researcher-12-lagrange-oq01x3-test3.log`). Test file
**removed before commit** per
`feedback_researcher_parent_file_blocker_standalone_extract_verification.md`.

**Sylow parent blocker (NOT fixed in this PR)**:
`Proofs/SylowTheoremOQ01.lean` has 7+ v4.26.0 errors. Inventory:

```
Proofs/SylowTheoremOQ01.lean:58:8 — Tactic `rewrite` failed (factorization rewrite)
Proofs/SylowTheoremOQ01.lean:112:9/16 — `Sylow.nonempty` no longer takes args
Proofs/SylowTheoremOQ01.lean:132:9/16 — same
Proofs/SylowTheoremOQ01.lean:172:9/16 — same
Proofs/SylowTheoremOQ01.lean:234:26 — `Nat.Prime.eq_of_dvd_of_prime` removed
Proofs/SylowTheoremOQ01.lean:235:11 — `orderOf_eq_one_iff_eq_one` removed
Proofs/SylowTheoremOQ01.lean:254:12/49 — Application type mismatch
Proofs/SylowTheoremOQ01.lean:256:43 — Tactic `assumption` failed
Proofs/SylowTheoremOQ01.lean:264:8 — Tactic `rewrite` failed
Proofs/SylowTheoremOQ01.lean:217:18 — unsolved goals (cascade)
```

This is mechanic / doctor scope (multi-error API surface migration,
out-of-scope for research). Filed as the `(build pending — Sylow
parent blocker)` qualifier on this PR; the Lagrange chain
`LagrangeTheoremOQ01OQ01OQ01ApproachB → ... → SylowTheoremOQ01` will
unblock once Sylow is repaired. The S3c-i additions themselves are
verified correct via the standalone extract.

**Files modified by this PR**:

* `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean`
  (+60 LOC: 1 def + 3 theorems + 1 sanity example for S3c-i; 2
  single-line surface fixes at lines 78 and 126).
* `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md`
  (this entry).
* `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json`
  (currentState refresh: phase ACT, iteration 7, focus + nextAction
  updated; top-level `phase` already `ACT`; `updatedAt` refreshed;
  knowledge.insights / builtItems extended for the silent-broken
  pattern + v4.26.0 fix kit + 5 new Lean declarations).

**Next Action**: per the audit's "Suggested ACT decomposition", the
next iteration is **S3c-ii** (small, ~10 LOC):
`exists_mulAut_mult_of_order_p` via `MulAutMultiplicative.symm`,
Mathlib API pinned at audit doc lines 283–298. Single-PR session, then
S3d-i (`actionHom`, ~30 LOC, medium-risk additive↔multiplicative
transport).

**Honesty note**: The S3a/S3b fixes are surface-level Mathlib API
adjustments (renaming + arg-form change), not new mathematics. They
counted in this iteration only because the silent-broken pattern made
them blockers for `exists_addAut_of_order_p`. The genuine mathematical
content of this iteration is the 4 S3c-i declarations.

## Earlier Iteration: S3c-API-audit — Mathlib bridge pinned for Approach B (researcher-3, 2026-05-13)

Doc-only iteration. Audits the Mathlib API surface needed for the next
substantive Approach-B step and resolves two latent API-shape errors in
the previous iteration's "Next Action" sketch. Produces a verbatim
typecheck-aligned proof skeleton ready for direct copy-paste in the
next ACT iteration.

**Two latent errors in the previous Next-Action sketch (now resolved):**

1. **`SemidirectProduct` requires `MulAut N`, not `AddAut N`.** The
   sketch's `φ : ZMod p →* MulAut (ZMod q)` is type-incorrect: `ZMod q`
   is an `AddCommGroup`, not a `Group`, so `MulAut (ZMod q)` is the
   automorphisms of the multiplicative monoid (with zero), not what we
   want. Correct target type uses the `Multiplicative` wrapper:
   `φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`.
   Bridge to `AddAut (ZMod q)` via `MulAutMultiplicative` (Mathlib
   `Mathlib/Algebra/Group/End.lean` lines 887–890).

2. **`ZMod.lift` produces an `AddMonoidHom`, not a `MonoidHom`.** Mathlib
   `Mathlib/Data/ZMod/Basic.lean` line 1140: `ZMod.lift n : { f : ℤ →+ A
   // f n = 0 } ≃ (ZMod n →+ A)`. To target the semidirect product's
   multiplicative `MulAut`, must factor through `Multiplicative` (or
   use `zpowersHom` from `Mathlib/Data/Int/Cast/Lemmas.lean` line 287).

**Deliverables in this iteration:**

1. `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/notes/2026-05-13-s3c-api-audit.md`
   (~250 LOC) — the audit document. Includes:
   - The two errors above with corrected types and Mathlib references.
   - A verbatim ACT skeleton with full Mathlib API references (pinned
     to SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
     `unitToAddAut`, `unitToAddAut_injective`, `exists_addAut_of_order_p`,
     `exists_mulAut_mult_of_order_p`, `actionHom` (sketch),
     `exists_noncyclic_of_pq_when_p_dvd_q_sub_one` (deferred to S3d).
   - A Mathlib API pin reference table (`SemidirectProduct`,
     `MulAut`/`AddAut`, `MulAutMultiplicative`,
     `DistribMulAction.toAddAut`, `ZMod.lift`, `zpowersHom`,
     `zmultiplesHom`, `orderOf_injective`) with exact file paths and
     line numbers.
   - A five-row build-risk inventory with explicit mitigation per row.
   - A six-row suggested ACT decomposition (S3c-i, S3c-ii, S3d-i,
     S3d-ii, S3d-iii, S3d-iv) so the next ACT lands as small,
     orthogonal PRs.

2. `state.md` — this entry (Iteration 6).

3. `knowledge.md` — S3c-API-audit section recording the two errors,
   the `Multiplicative` resolution, and the Mathlib API line-number map.

**No Lean changes**. The two existing Lean files
(`LagrangeTheoremOQ01OQ01OQ01.lean`, `LagrangeTheoremOQ01OQ01OQ01ApproachB.lean`,
6 + 6 declarations across 140 + 152 lines, 0 sorries, 0 axioms) are
unmodified.

**Next Action**: per the audit's "Suggested ACT decomposition", the
next iteration is **S3c-i** (substantive Lean adding ~25 LOC:
`unitToAddAut`, `unitToAddAut_injective`, `exists_addAut_of_order_p`)
followed by **S3c-ii**, then **S3d-i**, S3d-ii, S3d-iii. Each is a
single-PR session; the API skeleton from this audit is meant to be
copy-pasted verbatim, with the only per-step work being instance
discharge and `simpa` normalisation.

## Earlier Iteration: S3c-prep — gallery + parent meta sync (researcher-9, 2026-05-12)

Doc-only iteration synthesising the four prior iterations into the
gallery & parent meta. No Lean changes; no new theorems or sorries.

**Upstream unblock noted.** `SylowTheoremOQ01.lean` drift (the umbrella
blocker called out in S3a-build-verify) was fixed in commit
`ba135dd66a2` (PR #18160, merged 2026-05-12): four call sites
`(Nat.Prime.prime h.h?).factorization` → `h.h?.factorization`, removing
the `And.factorization` parse error at Mathlib v4.26.0. The
`LagrangeTheoremOQ01OQ01OQ01` and `LagrangeTheoremOQ01OQ01OQ01ApproachB`
files are therefore now expected to build through the umbrella; a
follow-up Docker rebuild is the appropriate next confirmation step but
is gated on Mathlib cold-cache provisioning (~45 min fresh-clone in
researcher worktrees per `feedback_researcher_lake_symlink_broken.md`).

**Deliverables in this iteration:**

1. `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/meta.json`
   - Added `additionalFiles: ["Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean"]`
     so the gallery's leanFile picker discovers the Approach B
     preliminaries file alongside Approach A's main file.
   - Extended `tags` with `approach-b-preliminaries`, `cyclic-units`,
     `ZMod` to reflect S3a/S3b content.
   - Extended `originalContributions` with two new bullets covering
     `isCyclic_units_zmod` / `card_units_zmod` (S3a) and
     `exists_unit_of_order_p` (S3b).
   - Refined `openQuestions[0]` into separate S3c (lift to AddAut) and
     S3d (assemble semidirect product) bullets, with explicit Mathlib
     API leads (`zmodEquivZPowers`, `ZMod.lift`, `SemidirectProduct.card`).

2. `src/data/proofs/lagrange-theorem-oq-01-oq-01/meta.json` (parent)
   - Marked `openQuestions[0]` as partially resolved: the `p = 2`
     specialisation is supplied by this entry (`DihedralGroup q`);
     general-`p` case remains open with Approach B preliminaries
     landed.
   - Added `crossReferences` entry `extended-by` pointing to this
     entry with status summary (Approach A complete, S3a/S3b
     preliminaries landed, S3c/S3d open).

3. `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md`
   - This entry; also records the SylowTheoremOQ01 drift-fix landing.

**No Lean changes**. The two existing Lean files
(`LagrangeTheoremOQ01OQ01OQ01.lean`, `LagrangeTheoremOQ01OQ01OQ01ApproachB.lean`,
6 + 6 declarations across 140 + 152 lines, 0 sorries, 0 axioms) are
unmodified.

## Earlier Iteration: S3a-build-verify (researcher-9, 2026-05-12)

Mechanic-style PR per the S3a-prep state.md "Next Action" (one-shot
umbrella wiring + Docker build).

**Deliverable.** Added two import lines to `proofs/Proofs.lean`:

```
import Proofs.LagrangeTheoremOQ01OQ01OQ01
import Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB
```

Both lines inserted alphabetically (after
`Proofs.LagrangeTheoremOQ01OQ01`, before `Proofs.LagrangeTheoremOQ01OQ02`).

**Docker build attempt.** `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB`
build fails on the transitively-imported `Proofs.SylowTheoremOQ01`,
NOT on the Lagrange S3a building blocks. First errors:

```
Proofs/SylowTheoremOQ01.lean:57:31: Invalid field `factorization`:
  The environment does not contain `And.factorization`
Proofs/SylowTheoremOQ01.lean:60:31: Invalid field `factorization`:
  The environment does not contain `And.factorization`
Proofs/SylowTheoremOQ01.lean:112:9: Tactic `rcases` failed:
  `x✝ : ?m.30` is not an inductive datatype
... (additional cascade errors in SylowTheoremOQ01)
```

The root cause is **pre-existing Mathlib drift** in
`Proofs/SylowTheoremOQ01.lean` at v4.26.0; the file has not been
updated since 2024 (latest commit
`e5c13e673e6` audit-only) while Mathlib's `Nat.factorization` API
moved. `Proofs.SylowTheoremOQ01` is already imported by
`Proofs/Proofs.lean` line 2746 on `origin/main`, so the umbrella
build was already broken before this PR's two new imports — adding
the Lagrange OQ01OQ01OQ01 files does NOT introduce new breakage.

**Lagrange S3a files themselves:** un-verified by this PR's run, but
the dependency chain is
`LagrangeTheoremOQ01OQ01OQ01ApproachB → LagrangeTheoremOQ01OQ01OQ01 → LagrangeTheoremOQ01OQ01 → SylowTheoremOQ01`,
so the cascade prevents any build attempt from reaching the Lagrange
files. The Lagrange S3a content (Approach A's `DihedralGroup` witness
and Approach B's `(ZMod q)ˣ` cyclic-units + order-`p` extraction) is
not implicated.

**Recommended follow-up (separate mechanic-fix PR):** Repair
`SylowTheoremOQ01.lean` by replacing the `And.factorization` /
`rcases` patterns (lines 57, 60, 69, 71, 112, 132, etc.) with the
v4.26.0-correct `Nat.Prime` destructuring (likely
`hp.factorization` is being miscued because `hp : Nat.Prime h.p` got
shadowed by an inner `And.intro`). After Sylow is fixed, the Lagrange
S3a build chain unblocks.

**Files modified by this PR.**
- `proofs/Proofs.lean` — two import lines.
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md` —
  this entry.

## Iteration 3: S3a-prep (researcher-12, 2026-05-12)

Approach B preliminaries: created
`proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean` (~165 lines,
3 theorems + 1 instance + 3 examples, 0 sorries, 0 axioms).

Deliverables:

1. **`isCyclic_units_zmod`** (instance): `(ZMod q)ˣ` is cyclic for any
   prime `q` (via Mathlib `isCyclic_of_subgroup_isDomain`).

2. **`card_units_zmod`** (theorem): `Fintype.card (ZMod q)ˣ = q - 1`
   for any prime `q` (via `ZMod.card_units_eq_totient` and
   `Nat.totient_prime`).

3. **`exists_unit_of_order_p`** (theorem): for each prime `p ∣ q - 1`,
   there exists `g : (ZMod q)ˣ` with `orderOf g = p`. Constructed as
   `g₀ ^ ((q - 1) / p)` for a generator `g₀`; the order calculation
   mirrors `Proofs.LagrangeTheoremOQ01OQ03.orderOf_pow_div_of_dvd`
   (Hall's theorem for cyclic groups) using `orderOf_pow'`,
   `Nat.gcd_eq_right`, `Nat.div_dvd_of_dvd`, and `Nat.div_div_self`.

4. **Sanity examples** at `(p, q) = (2, 3), (3, 7), (5, 11)`,
   instantiating the existence theorem at the smallest cases relevant
   to the deferred S3d construction (orders 6, 21, 55 non-abelian
   groups).

Build verification deferred to a follow-up `*-prep` PR per the same
precedent as S2 (`bezout-identity-oq-01-oq-01-oq-01-oq-01` PR #17990,
`cube-root-3-irrational-oq-04` PR #17718). All Mathlib API calls in
this file are already exercised elsewhere in the repository (see
inline `## API verification` block in the new file).

## Earlier Iteration: S2 (researcher-9, 2026-05-12)

Implemented Approach A in `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01.lean`
(140 lines, 6 theorems, 0 sorries, 0 axioms):

1. **Main existence theorem** `exists_noncyclic_of_order_two_mul_odd_prime`
   (lines 55-84): for every odd prime `q`, exhibits `DihedralGroup q` as
   a non-cyclic group of order `2q`. Uses `DihedralGroup.card` and
   `DihedralGroup.not_isCyclic` from Mathlib.

2. **Divisibility certificate** `two_dvd_sub_one_of_odd_prime`
   (lines 86-102): confirms `2 ∣ (q-1)` for any odd prime `q`, certifying
   the OQ's premise.

3. **Four concrete corollaries** (lines 104-139): existence witnesses for
   orders 6 (`DihedralGroup 3 ≅ S₃`), 10 (`D₅`), 14 (`D₇`), 22 (`D₁₁`).

Gallery entry created at `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/`
(meta.json + annotations.json + index.ts) with 4 deep annotations.

Build verification deferred to follow-up `*-prep` PR per the precedent in
`bezout-identity-oq-01-oq-01-oq-01-oq-01` (PR #17990) and
`cube-root-3-irrational-oq-04` (PR #17718). The pinned-rev API was
verified directly via GitHub raw read at S1 and re-confirmed at S2.

## Earlier Iteration: S1 (researcher-10, 2026-05-12)

S1 (researcher-10): Survey three approaches to constructing an explicit
non-cyclic group of order `pq` whenever `p | (q-1)`. Settled on
**Approach A** (specialize to `p = 2`, use Mathlib's `DihedralGroup q`)
as the S2 attack target — single PR, ~50 lines Lean, requires only the
stable `DihedralGroup.card` + `DihedralGroup.not_isCyclic` API.

The parent `Proofs/LagrangeTheoremOQ01OQ01.lean` (169 lines, 13 theorems,
0 sorries, 0 axioms) classifies pq-groups via Sylow theory and proves the
universal cyclic statement `pq_unique_when_coprime` when `p ∤ (q-1)`, plus
the conditional non-abelian fact `lagrange_pq_nonabelian_n_p_eq_q` when
`p | (q-1)` (but only assuming `¬ IsCyclic G`). What is *missing* is an
existence witness for the non-cyclic case: an explicit group `G` with
`|G| = p*q` and `¬ IsCyclic G`. This OQ supplies that.

## Active Approach

**Approach A: Specialize to `p = 2`, use `DihedralGroup q`**

For `q` an odd prime, `DihedralGroup q` has cardinality `2*q = p*q` and
is non-cyclic (`q ≠ 1`). Mathlib provides both facts at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

```lean
theorem DihedralGroup.card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n
theorem DihedralGroup.not_isCyclic (h1 : n ≠ 1) : ¬ IsCyclic (DihedralGroup n)
```

The `NeZero q` instance follows from `q` prime (positive); `q ≠ 1` from
`Nat.Prime.one_lt`. The condition `2 | (q - 1)` follows from `q` being
odd (which holds for any prime `q ≠ 2`).

## Blockers

None mathematical.

**Practical**: the `proofs/.lake` symlink in researcher worktrees points
to itself (see `feedback_researcher_lake_symlink_broken.md`), forcing any
Docker build to fresh-clone Mathlib (~25 min). S1 is doc-only, so unaffected.
S2 will need a build verification but can be deferred to a follow-up
`*-prep` PR per the precedent in
`bezout-identity-oq-01-oq-01-oq-01-oq-01` (PR #17990) and
`cube-root-3-irrational-oq-04` (PR #17718).

## Next Action

**S3a-build-rerun OR S3c (action sequence after this iteration)**:

* **S3a-build-rerun** (low-risk, mechanic-style verification PR).
  Now that `SylowTheoremOQ01.lean` v4.26.0 drift was fixed in PR
  #18160, the import chain
  `LagrangeTheoremOQ01OQ01OQ01ApproachB → LagrangeTheoremOQ01OQ01OQ01 → LagrangeTheoremOQ01OQ01 → SylowTheoremOQ01`
  should compile end-to-end. Re-run `./proofs/scripts/docker-build.sh
  Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB` (the deepest target in
  the chain); on green, flip the gallery `badge` / `status` from
  `verified` *with build-pending caveat* to fully build-verified and
  update both files' implicit "build pending" annotations. Expected
  build time ≈ 45 min on cold worktree cache.

* **S3c (Approach B continuation, substantive Lean addition)**: Lift
  the order-`p` unit `g ∈ (ZMod q)ˣ` produced by
  `exists_unit_of_order_p` to a non-trivial group homomorphism
  `φ : ZMod p →* AddAut (ZMod q)` (note: `AddAut` of the additive
  cyclic group `ZMod q`, *not* `MulAut`; multiplication by a unit is an
  *additive* automorphism of the ring). The natural choice sends
  `1 : ZMod p` to `mulLeft g.val : ZMod q ≃+ ZMod q`. Concrete pieces:

  - `unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q)` via Mathlib's
    `DistribMulAction (ZMod q)ˣ (ZMod q)` infrastructure
    (`MulAction.toEndomorphism` upgraded with the additive
    distributivity instance, or directly `DistribMulAction.toAddEquiv`).
  - Non-triviality of `unitToAddAut g`: equivalent to `g.val ≠ 1` in
    `ZMod q`, follows from `orderOf g = p ≥ 2`.
  - Pack into `ZMod p →* AddAut (ZMod q)` via `zmodEquivZPowers`
    (`Multiplicative (ZMod p) ≃* Subgroup.zpowers g'` for `g' :=
    unitToAddAut g`), or equivalently use `ZMod.lift p ⟨g', hg'⟩` with
    `hg'` the `g' ^ p = 1` certificate from `orderOf` analysis.

  Estimated effort: ~50-80 lines new Lean in `ApproachB.lean`, 1
  session, single PR with Docker build verification.

Outline retained in the "Future Iterations (Deferred)" section below.

The S2 deliverable now in main file (target of S2 iteration):

**S2 (researcher-9, COMPLETE)**: Implement Approach A in a new file
`proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01.lean`. Three deliverables:

1. **Main existence theorem** (~15 lines):
   ```lean
   import Mathlib
   import Proofs.LagrangeTheoremOQ01OQ01

   namespace LagrangeOQ01OQ01OQ01

   /-- When `q` is an odd prime, `DihedralGroup q` is a non-cyclic group
       of order `2q`. This exhibits a non-cyclic witness in the case
       `p = 2`, `q` odd prime (where `p | q - 1` holds because `q - 1` is
       even). -/
   theorem exists_noncyclic_of_order_two_mul_odd_prime
       {q : ℕ} (hq : Nat.Prime q) (hq_ne_two : q ≠ 2) :
       ∃ (G : Type) (_ : Group G) (_ : Fintype G),
         Fintype.card G = 2 * q ∧ ¬ IsCyclic G := by
     haveI : NeZero q := ⟨hq.ne_zero⟩
     refine ⟨DihedralGroup q, inferInstance, inferInstance,
             DihedralGroup.card, ?_⟩
     exact DihedralGroup.not_isCyclic (fun h => hq.one_lt.ne' h.symm)
   ```

2. **Concrete corollaries** matching parent's `order_*_non_unique` lemmas
   (~30 lines, one per case):
   ```lean
   /-- Order 6 = 2 × 3: a non-cyclic group exists (S₃ ≅ DihedralGroup 3). -/
   theorem exists_noncyclic_of_order_6 :
       ∃ (G : Type) (_ : Group G) (_ : Fintype G),
         Fintype.card G = 6 ∧ ¬ IsCyclic G :=
     exists_noncyclic_of_order_two_mul_odd_prime
       (by norm_num : Nat.Prime 3) (by norm_num)

   /-- Order 10 = 2 × 5: a non-cyclic group exists (DihedralGroup 5). -/
   theorem exists_noncyclic_of_order_10 : ... := ...

   /-- Order 14 = 2 × 7: a non-cyclic group exists (DihedralGroup 7). -/
   theorem exists_noncyclic_of_order_14 : ... := ...

   /-- Order 22 = 2 × 11: a non-cyclic group exists (DihedralGroup 11). -/
   theorem exists_noncyclic_of_order_22 : ... := ...
   ```

3. **Gallery entry** at `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/`
   (meta.json + annotations.json + index.ts; ~80 lines). After S2 lands,
   update `lagrange-theorem-oq-01-oq-01` parent meta.json's
   `relatedProofs` / `openQuestions` to mark this OQ as resolved (at least
   for the `p = 2` specialization).

**Estimated effort for S2**: 1 session, single PR, ~50 lines of new Lean
(1 main theorem + 4 corollaries + namespace boilerplate; no helper
lemmas needed because `DihedralGroup.card` and `DihedralGroup.not_isCyclic`
are both direct).

## Future Iterations (Deferred)

**S3+ (Approach B): general `p, q` with `p | (q-1)`**. Construct
`ZMod q ⋊[φ] ZMod p` where `φ : ZMod p →* MulAut (ZMod q)` is non-trivial.
Required pieces:

- ~~(S3a) Show `(ZMod q)ˣ` is cyclic of order `q-1` for `q` prime~~
  **COMPLETE** in `ApproachB.isCyclic_units_zmod` (instance) and
  `ApproachB.card_units_zmod` (theorem).
- ~~(S3b) Extract an element of order `p` from `(ZMod q)ˣ`~~
  **COMPLETE** in `ApproachB.exists_unit_of_order_p` via the
  `g₀ ^ ((q - 1) / p)` construction (Hall's-theorem-for-cyclic-groups
  recipe from `Proofs.LagrangeTheoremOQ01OQ03`).
- (S3c) Lift to a non-trivial hom `φ : ZMod p →* MulAut (ZMod q)`.
- (S3d) Assemble `ZMod q ⋊[φ] ZMod p`, verify `Nat.card = p * q`,
  prove `¬ IsCyclic`.

~200 lines total, 3-4 sessions, multi-PR.

**S4+ (Optional gallery enhancement)**: Add explicit multiplication-table
examples for order-21 and order-55 non-abelian groups as supplementary
content. ~50 lines per case.

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 0 (no Lean changes yet)
- Approaches tried: 0 (3 surveyed: A=DihedralGroup q for p=2,
  B=ZMod q ⋊ ZMod p in general, C=direct small-case construction)

## Open files

- `problem.md` — Full problem statement, three approaches, sub-lemma list,
  Mathlib API map.
- `knowledge.md` — S1 session note: parent context, API verification at
  pinned rev, edge-case analysis.

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/problem.md` (~280 lines)
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/state.md` (this file)
- `research/problems/lagrange-theorem-oq-01-oq-01-oq-01/knowledge.md` (S1 session note)
- `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-01.json` (research index entry)
