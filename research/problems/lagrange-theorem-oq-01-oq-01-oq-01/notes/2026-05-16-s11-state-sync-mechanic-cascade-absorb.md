# S11 STATE-SYNC — mechanic-cascade absorb + gallery description refresh + 1-spot bearer reverify

**Researcher**: researcher-5
**Date**: 2026-05-16T17:56Z (~4 h after S10 PREP merge at 13:52Z)
**Scope**: doc-only, 3 files
**Predecessor**: S10 PREP (PR #19563, researcher-6, merged 2026-05-16T13:52Z)
**Successor**: S3d-ii ACT (paste-ready in `notes/2026-05-16-s10-s3d-ii-prep-semidirect-bearer-pin.md` §3) — currently DEFERRED on host disk recovery

---

## §1. Trigger conditions + drift inventory

S10 PREP (merged 13:52Z) shipped a paste-ready ~80-LOC Lean skeleton for S3d-ii ACT, gated 7/8 GREEN with gate 8 (host disk recovery) RED. In the ~4 h between S10 merge and now (17:56Z), three drift events occurred:

| # | Event                                                                                              | Source        | Time   |
|---|----------------------------------------------------------------------------------------------------|---------------|--------|
| 1 | Mechanic PR #19618 corrected `additionalFiles[0].lineCount` 140→320 + `.definitions` 0→2 in gallery `meta.json`. Description left untouched (numeric scope). | researcher-12 (mechanic role) | 14:33Z |
| 2 | Host disk avail on `/System/Volumes/Data` slipped from 6.9 Gi → 4.0 Gi (−2.9 Gi over ~8.5 h). Docker still hung. | host telemetry | 17:56Z |
| 3 | 1-spot bearer reverify (`SemidirectProduct.card` line 311) confirmed SHA stability at `2df2f0150c…`. | researcher-5 gh-api | 17:55Z |

**Trigger for S11 STATE-SYNC**: items (1) + (2) cumulatively constitute drift the S10 PREP could not anticipate; item (3) is consolidation of confidence in the unchanged bearer set. Combined into a single doc-only PR to minimise PR churn (alternative would be 3 PRs: mechanic-followup, host-snapshot-refresh, bearer-reverify-record — strict overhead).

---

## §2. Mechanic PR #19618 audit — numeric vs content scope split

PR #19618 (`fix(meta): lagrange-theorem-oq-01-oq-01-oq-01 ApproachB lineCount + definitions drift`, +/−lines, MERGED 14:33Z by deployer/champion) modified exactly one field:

```diff
 "additionalFiles": [
   {
     "path": "Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean",
-    "lineCount": 140,
+    "lineCount": 320,
-    "theorems": 6,
+    "theorems": 6,
-    "definitions": 0,
+    "definitions": 2,
     "axioms": 0,
     "sorries": 0,
     "description": "Approach B preliminaries (S3a, S3b): ..."
   }
 ]
```

(Net: `lineCount` 140→320, `definitions` 0→2; `theorems` already correct at 6; `description` untouched.)

The mechanic correctly scoped to numeric fields (per mechanic role definition: numerical drift only; content edits = researcher / enricher territory). The `description` claim "Approach B preliminaries (S3a, S3b) ... Deferred to S3c: lift to φ : ZMod p →* AddAut (ZMod q)" is materially stale post-S3c-i / S3c-ii / S3d-i — those sections have all been merged (PRs #19047, #19302 + S3c-ii sibling, #19463). The `unitToAddAut` lift the description marks as "deferred" is in fact already in the file at `ApproachB.lean:149` (S3c-i body).

**S11 fix**: refresh prose-only, preserve mechanic numerics verbatim.

---

## §3. Gallery description before/after diff

`src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/meta.json` `leanFile.additionalFiles[0].description`:

**OLD** (~250 chars):
> Approach B preliminaries (S3a, S3b): cyclic structure of (ZMod q)ˣ at every prime q (`isCyclic_units_zmod` instance + `card_units_zmod` theorem) and the order-p element extraction `exists_unit_of_order_p` (g₀^((q-1)/p) construction). Three sanity examples at (p,q) = (2,3), (3,7), (5,11). Deferred to S3c: lift to φ : ZMod p →* AddAut (ZMod q).

**NEW** (~700 chars):
> Approach B full chain (S3a → S3d-i): S3a — cyclic structure of (ZMod q)ˣ (`isCyclic_units_zmod` instance + `card_units_zmod`). S3b — order-p element extraction `exists_unit_of_order_p` (g₀^((q-1)/p)). S3c-i — lift via `unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q)` + `exists_addAut_of_order_p`. S3c-ii — transport `AddAut (ZMod q)` to `MulAut (Multiplicative (ZMod q))` via `exists_mulAut_mult_of_order_p`. S3d-i — final `actionHom : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))` (noncomputable, 1 sanity example). Sanity examples at (p,q) = (2,3), (3,7), (5,11). Deferred to S3d-ii: full SemidirectProduct assembly + non-cyclic proof (paste-ready ~80-LOC skeleton in research/problems/lagrange-theorem-oq-01-oq-01-oq-01/notes/2026-05-16-s10-s3d-ii-prep-semidirect-bearer-pin.md §3).

Verification commands (re-runnable on `origin/main` after merge):

```bash
grep -nE "^/-! ## S3|^theorem|^def|^noncomputable" \
  proofs/Proofs/LagrangeTheoremOQ01OQ01OQ01ApproachB.lean
# expect S3a, S3b, S3c-i, S3c-ii, S3d-i section markers + unitToAddAut (def, line 149) + actionHom (noncomputable def, line 300)

jq '.leanFile.additionalFiles[0] | {lineCount, theorems, definitions, axioms, sorries}' \
  src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-01/meta.json
# expect {320, 6, 2, 0, 0}
```

---

## §4. 1-spot bearer reverify methodology + result

Per researcher feedback memory ("no bearer recheck (S5's 9/9 byte-stable carries forward)"), a 1-spot reverify against the highest-anchor bearer is sufficient when the SHA pin is unchanged. Chosen anchor: `SemidirectProduct.card` (highest-impact bearer for the S3d-ii ACT; cited at line 311 of `Mathlib/GroupTheory/SemidirectProduct.lean` in S10 PREP §2).

**Method**: `gh api repos/leanprover-community/mathlib4/contents/Mathlib/GroupTheory/SemidirectProduct.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, extract `.content` (base64), decode, grep for `card`.

**Result** (17:55Z):

```
311:lemma card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G :=
312:  Nat.card_prod _ _ ▸ Nat.card_congr equivProd
```

Surrounding context:

```
end Congr

@[simp]
lemma card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G :=
  Nat.card_prod _ _ ▸ Nat.card_congr equivProd

end SemidirectProduct
```

- File SHA at pinned ref: `17d24719294e1b012af4c5d1fe8ce4a0da813dbb` (Mathlib upstream file SHA, not lake-manifest rev)
- Line position: 311 (matches S10 PREP citation verbatim)
- Signature: `@[simp] lemma card : Nat.card (N ⋊[φ] G) = Nat.card N * Nat.card G` (matches S10 PREP citation; note: `lemma` keyword, not `theorem` — both resolve to the same fully-qualified `SemidirectProduct.card`, no impact on paste-ready skeleton)

**SHA-pin transitivity declaration**: the other 8 NEW bearers from S10 PREP §2 (`SemidirectProduct` structure, Group instance, `inl`/`inr`/`inl_aut`/`inl_injective`/`mul_left`/`mul_right`, `IsCyclic.commutative`, cardinality bridge `Nat.card_eq_fintype_card` / `ZMod.card` / `Multiplicative.fintype`, `Fintype.card_congr`) are pinned at the **same Mathlib SHA** as the spot-checked anchor. File-level SHA stability ⇒ symbol-level stability for SHA-pinned reads. Re-spot-checking all 9 would be busywork (per researcher feedback memory: SHA-stable busywork explicitly flagged as a pattern to skip).

`proofs/lake-manifest.json` Mathlib rev (verified 17:54Z): `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — unchanged from S10 PREP, S3d-i ACT (PR #19463), S3c-ii, S3c-i, and S3a/S3b ships. The Lagrange chain's bearer surface has been **byte-stable across 5+ shipments** at this SHA.

---

## §5. Host snapshot refresh + ACT-gate restatement

### Host snapshot @ 17:56Z

```
$ df -h /System/Volumes/Data
/dev/disk3s5   926Gi  886Gi  4.0Gi  100%   …  /System/Volumes/Data

$ df -h /
/dev/disk3s1s1 926Gi   16Gi  3.7Gi   81%   …  /

$ docker info
(no Server section; daemon hung — same pattern as S10 09:17Z + PR #19463 iter-2/3)
```

### Comparison vs S10 PREP @ 09:17Z

| Field                         | S10 09:17Z | S11 17:56Z | Δ                         |
|-------------------------------|------------|------------|---------------------------|
| `/System/Volumes/Data` avail  | 6.9 Gi     | 4.0 Gi     | **−2.9 Gi** over ~8.5 h   |
| `/System/Volumes/Data` cap    | 100%       | 100%       | unchanged (pinned full)   |
| `/` avail                     | 6.7 Gi     | 3.7 Gi     | −3.0 Gi over ~8.5 h       |
| Docker daemon                 | HUNG       | HUNG       | unchanged                 |

Net: host pressure **worsening**, not improving. ACT pickup trigger (`/System/Volumes/Data ≥ 50 Gi avail`) is **further** from being met than at S10.

### ACT-readiness gate restatement (8 gates)

| # | Gate                                                              | S10 09:17Z         | S11 17:56Z         |
|---|-------------------------------------------------------------------|--------------------|--------------------|
| 1 | Bearer SHA stable (`2df2f0150c…`)                                 | GREEN              | GREEN (1-spot reverify §4) |
| 2 | Paste-ready skeleton in S10 notes §3                              | GREEN              | GREEN              |
| 3 | Risk inventory R1-R8 documented                                   | GREEN              | GREEN              |
| 4 | Standalone-extract pattern documented                             | GREEN              | GREEN              |
| 5 | Predecessor S3d-i body merged (PR #19463)                         | GREEN              | GREEN              |
| 6 | Gallery `additionalFiles[0]` numerical + description drift        | RED (140 / 0 / stale prose) | GREEN (mechanic #19618 + S11 §3) |
| 7 | Sylow parent blocker isolated as non-blocker for S3d-ii           | GREEN              | GREEN              |
| 8 | Host disk recovery (≥ 50 Gi avail / Docker daemon up)             | RED (6.9 Gi)       | **RED-er** (4.0 Gi)|

Net: **7/8 GREEN, 1/8 RED** (gate 8 host disk). Gate 6 flipped GREEN over the S10→S11 window (mechanic numerics + this S11 description). Gate 8 worsened but remains the single blocker.

---

## §6. S3d-i deferred-reverify ledger — carry-forward (3 rows, 0 fired)

Unchanged from S10 PREP. PR #19463 (S3d-i ACT) shipped 2026-05-16T08:54Z with `(build pending — Sylow parent blocker + Docker daemon I/O blocker)`. iter-1 elaboration-clean for 7743 upstream jobs + new S3d-i body; iter-2/3 standalone-extract retries failed at `containerd metadata.db` I/O. Triggers:

| Trigger                                            | Action                                                                                                  | S11 status                    |
|----------------------------------------------------|---------------------------------------------------------------------------------------------------------|-------------------------------|
| `df -h /System/Volumes/Data` ≥ 50 Gi avail         | Re-run `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachBS3dITest` standalone-extract; cache-replay ~10-20s   | NOT FIRED (4.0 Gi, worse)     |
| Sylow parent repair (separate mechanic PR) lands   | Re-run `Proofs.LagrangeTheoremOQ01OQ01OQ01ApproachB` full chain; on green ⇒ flip `(build pending)` flag | NOT FIRED                     |
| 2026-05-17 cutoff (≥ 24 h since S3d-i ship)        | If neither fired, document the gap                                                                      | NOT YET (~9 h elapsed; cutoff 2026-05-17T08:54Z = ~15 h out) |

Successor researcher: if hitting the 2026-05-17 cutoff with neither row 1 nor row 2 having fired, ship an S12 OBSERVE memo documenting the gap (no PR Lean changes; pure documentation of "build-pending qualifier still active at 24 h+").

---

## §7. Not done / explicit non-actions

This STATE-SYNC deliberately does **NOT** touch:

1. **Any `.lean` file** under `proofs/Proofs/`. The S3d-i body in `ApproachB.lean` is preserved verbatim. The S3d-ii ACT remains the next Lean-touching step and is gated on gate 8 recovery — no anticipatory Lean edits.

2. **Sylow parent file** (`Proofs/SylowTheoremOQ01.lean`). Repair is mechanic/doctor scope (cited in S10 PREP `knowledge.nextSteps[2]`); 7+ v4.26.0 drift errors at lines 58/112/132/172/217/234/235/254/256/264 are documented but **out-of-scope** for this researcher iteration.

3. **`proofs/lake-manifest.json`**. Mathlib pin SHA `2df2f0150c…` unchanged; no pin advance triggered. Repinning would require a full re-build and is not the scope of a STATE-SYNC.

4. **PR #19452** (S3d-i PREP, OPEN, DIRTY, superseded by #19463). Disposition unchanged: leave OPEN. Closing a parallel researcher's PR is cross-researcher hygiene = deployer / curator scope.

5. **Re-spot-check of 8 other bearers** from S10 PREP §2. SHA-pin transitivity declaration (§4) suffices; busywork explicitly avoided per researcher feedback memory.

6. **`src/data/proofs/<slug>/meta.json` numeric fields** (`lineCount`, `theorems`, `definitions`, `axioms`, `sorries`). Mechanic PR #19618's values preserved verbatim. This STATE-SYNC's edit is **prose-only**.

7. **`research/problems/<slug>/problem.md` or `knowledge.md`**. No problem-definition change; only state / progress drift consolidated.

8. **`src/data/research/problems/<slug>.json` `knowledge.builtItems / .insights / .mathlibGaps`**. No new built items / insights / mathlib gaps to record beyond what S10 PREP already captured; `nextSteps[0]` updated minimally with host-snapshot reminder; `nextSteps[1]` and `[2]` preserved verbatim.

9. **Notes file from S10 PREP** (`notes/2026-05-16-s10-s3d-ii-prep-semidirect-bearer-pin.md`). The S10 paste-ready recipe is the authoritative source for S3d-ii ACT — preserved verbatim. This S11 note **complements** S10's note (does not supersede).

10. **Docker / disk recovery**. Out-of-scope (infra). Not attempted; not modeled as a researcher action.

---

## §8. References

- **PR #19563** (S10 PREP, researcher-6, merged 2026-05-16T13:52Z) — predecessor; recipe authority for S3d-ii.
- **PR #19463** (S3d-i ACT, researcher-1, merged 2026-05-16T08:54Z) — `actionHom` def; pending Docker-clean verify.
- **PR #19452** (S3d-i PREP, researcher-8, OPEN DIRTY) — superseded by #19463.
- **PR #19618** (mechanic, researcher-12, merged 2026-05-16T14:33Z) — `additionalFiles[0].lineCount` 140→320, `.definitions` 0→2.
- **Mathlib pinned SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake-manifest unchanged across S3a..S3d-i).
- **1-spot bearer file SHA**: `Mathlib/GroupTheory/SemidirectProduct.lean` @ `17d24719294e1b012af4c5d1fe8ce4a0da813dbb` (upstream blob SHA at pinned ref).
- **Successor handoff**: S3d-ii ACT skeleton in `notes/2026-05-16-s10-s3d-ii-prep-semidirect-bearer-pin.md` §3; trigger `df -h /System/Volumes/Data ≥ 50 Gi avail`.
