## S4d PREP — Strategy B split-point forward-reference audit + pin-verification of S4c workaround bearers (doc-only)

**Date**: 2026-05-15 (~06:42 UTC)
**Researcher**: researcher-3
**Mode**: PREP (doc-only; sibling-audit targeting two load-bearing-but-unverified claims
in the merged S4 PREP-chain — (a) the **split-point** chosen by S4 PREP Strategy B,
(b) the **bearer existence** of every Mathlib name used inside the S4c §3 and §4
workarounds)
**Phase target**: S4 ACT (the Lean discharge) + S5 (the parent split-and-replace)
**Status**: pristine orthogonal to the open STATE-SYNC PR #19081. 0 Lean changes,
0 builds, 0 axiom / sorry / theorem deltas, 0 gallery-data edits.

## 0. Why this PREP

Three merged doc-only PREPs design the S4 ACT → S5 transition:

| PR | Session note | Load-bearing claim |
|---|---|---|
| #18482 | `2026-05-13-s4-prep-parent-axiom-replacement-choreography.md` | Strategy B is **the only clean path**; the split-point is **"immediately after `gal_card_dvd_60_proved`"** (around line 1900 of the current 2067-line parent). |
| #18633 | `2026-05-13-s4b-prep-annotations-migration-audit-strategy-b.md` | 6 annotations: 3 move, 2 shift, 1 retitle. (Not audited here.) |
| #18731 | `2026-05-13-s4c-prep-mathlib-bearer-audit-pinned-sha.md` | Two phantom Mathlib lemmas (`arithFrobAt_mem_stabilizer`, `card_stabilizer_eq_card_inertia_mul_finrank`) blocked at pin `2df2f01...`; workarounds proposed in §3 (smul_eq_self) and §4 (Option B local extraction). |

The S4 PREP **does not explicitly perform** the forward-reference audit (does any theorem
in lines 329..1896 of the parent actually use a theorem below the split-point?), nor does
the S4c PREP **pin-verify the bearer Mathlib lemmas the workarounds rely on** (it pins
the *phantoms*; it does not pin the *replacements*). Both gaps are load-bearing for S4
ACT compilation and for S5 succeeding without a cascading refactor.

This PREP fills both gaps. It also re-verifies the S4c phantom flags against the
current pinned SHA (no Mathlib bump has occurred since S4c was written) and confirms
both lemmas remain absent.

## 1. Pinned SHA verification

```bash
$ jq -r '.packages[] | select(.name=="mathlib") | "\(.inputRev) \(.rev)"' proofs/lake-manifest.json
v4.26.0 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

All bearer audits in §3 and §4 below are checked against this exact SHA.

## 2. Strategy B split-point forward-reference audit

### 2.1 The proposed split

S4 PREP §"Step 1" instructs:

> Then **remove** from `Base.lean`:
> - Line 309: `axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal`
> - All lines from `q_gal_card` (around 1907) to end of `Part XVII` (lines ~1907–2060, approximately 150 LOC).

Resolving against the current parent (`proofs/Proofs/InverseGaloisA5.lean`, 2067 LOC):

| Boundary | Actual line | Note |
|---|---:|---|
| Last theorem to stay in **Base** | 1896 | `theorem gal_card_dvd_60_proved` |
| Section separator (comment block "Part XV: Galois Group Cardinality...") | 1899–1902 | included in Base or shifted to main? S4 PREP is silent — **§2.3 below recommends Base**. |
| First theorem to move to **main** | 1912 | `theorem q_gal_card` |
| Last theorem to move to main | 2035–2046 | `theorem gal_not_solvable` and the closing docstring/`end` |

**Concretely**: Base = lines 1..1898 (or 1..1902 with the section comment block) + the trailing
`end InverseGaloisA5` line (currently at 2067). Main = lines 1899(or 1903)..2066 with
a new `import Proofs.InverseGaloisA5Base` and a new `theorem three_dvd_gal_card := ...`
at the head.

### 2.2 Forward-reference audit (the load-bearing claim Strategy B never checks)

**Question**: does any theorem in lines 329..1896 of the parent reference, in its statement
or proof, any theorem at line ≥1912? If so, Strategy B's split point is **wrong** and would
produce a compile error in Base.

**Method**: grep for the six below-split-point named theorems across the in-Base region
(1..1896).

```bash
grep -n -E "q_gal_card|q_gal_iso_a5|a5_realizable|splitting_field_q_finrank|gal_has_index_two|gal_not_solvable" \
  proofs/Proofs/InverseGaloisA5.lean
```

Audit (current parent, all 14 hits classified):

| Line | Match | Classification |
|--:|---|---|
| 262 | `## Axiom Decomposition for q_gal_card` | docstring header |
| 670 | `4. gal_not_solvable: ...` | docstring (numbered list) |
| 671 | `5. a5_realizable: ...` | docstring |
| 672 | `6. a5_realizable_iso: ...` | docstring |
| 673 | `7. splitting_field_q_finrank: ...` | docstring |
| 678 | `12. gal_has_index_two_in_s5: ...` | docstring |
| 698 | `19. q_gal_card: ...` | docstring |
| 699 | `20. q_gal_iso_a5: ...` | docstring |
| 705 | `... ─→ q_gal_card` | docstring (ASCII graph) |
| 709 | `q_gal_card ──→ a5_realizable, ...` | docstring |
| 710 | `q_gal_card ──→ q_gal_iso_a5 ──→ ...` | docstring |
| 715 | `-- Part XII: Supporting Infrastructure for q_gal_card` | section comment |
| 719 | `## Roadmap to Eliminating the q_gal_card Axiom` | docstring |
| 875 | `The axiom three_dvd_gal_card is therefore supported ...` | docstring |

**Conclusion**: every hit at line < 1896 is either inside a `/-` … `-/` docstring or a `--`
comment. **Zero genuine forward-references**. Strategy B's split point is mechanically safe.

### 2.3 Stale-docstring cleanup load (deferred)

The 14 docstring hits above will become **partially stale** after Strategy B ships (S5):

- Hits 262, 670–719, 875: still accurate ("explains the role of the [now-proved] theorem
  `q_gal_card`"). Stays in Base.
- Hit 1907: docstring on `q_gal_card` itself says **"Uses only 2 axioms: vandermondeProduct_sq_eq
  and three_dvd_gal_card"** — **becomes false** after Strategy B (the parent will then have 0 axioms).
- Hits 2052, 2057, 2059–2063: the trailing `Axiom elimination history` docstring (lines 2040–2065).
  Says **"Current: 1 axiom (three_dvd_gal_card)"** + lists the axiom as still standing — entirely
  stale after S5.

**Recommendation**: defer these to S5 (the Strategy B ACT) as a final 8-line docstring edit at the
*main* file head (lines 1907, 2052, 2057, 2059–2063). Do **not** include them in S4 ACT — keep S4
ACT scoped to discharging `exists_gal_order_three`.

The S4b PREP's annotations.json migration (PR #18633) does **not** cover prose docstring updates;
those are S5 scope. (S4b's "1 retitle" is the gallery-card title, not in-file docstrings.)

### 2.4 `set_option` + `open` + `namespace` carry-over

The parent uses these top-of-file declarations:

```lean
set_option linter.unusedVariables false           -- line 45
set_option linter.unusedSimpArgs false            -- line 46
open scoped Classical                             -- line 67
namespace InverseGaloisA5                         -- line 69
open Polynomial                                   -- line 71
```

**For Strategy B**, both **Base** AND **main** files need these. The main file currently
does not have its own copies (it would inherit them from `Proofs.InverseGaloisA5` in the
current single-file world; after the split, main is a fresh file and must re-declare).

**Recommendation for S5 implementer**: literally copy lines 45–71 of the parent verbatim
into both `InverseGaloisA5Base.lean` (replacing line 1's `import Mathlib` block) and into
the new `InverseGaloisA5.lean` (after the new `import Proofs.InverseGaloisA5Base` /
`import Proofs.InverseGaloisA5Dedekind` lines).

Failure to do so will cause:
- Without `linter.unusedVariables false`: ~30 lint warnings in main on the unchanged
  `q_gal_iso_a5`, `gal_not_solvable` etc. (existing proofs use unused variables that
  the parent silences via the linter option).
- Without `open scoped Classical`: `decide`/`native_decide` on `Equiv.Perm (Fin 5)` may
  fail to compile (Fintype-instance synthesis).
- Without `open Polynomial`: `q.Gal`, `q.SplittingField`, `Polynomial.discr` references fail.
- Without `namespace InverseGaloisA5`: theorems would land in `_root_`, breaking every
  callsite of `InverseGaloisA5.q_gal_card` etc.

The two `native_decide` theorems at lines 53–65 (`perm_fin5_order5_order3_not_commute` and
`perm_fin5_no_order_15`) live **outside** the namespace (above line 69). They must stay in
Base (lines 1..1896 include them).

### 2.5 Umbrella `proofs/Proofs.lean` placement

Imports in `Proofs.lean` are alphabetical (verified lines 2410–2424). The new line
`import Proofs.InverseGaloisA5Base` must be inserted **between** the existing
`import Proofs.InverseGaloisA5` (line 2415) and `import Proofs.InverseGaloisA5Dedekind`
(line 2416):

```diff
 import Proofs.InverseGalois
 import Proofs.InverseGaloisA5
+import Proofs.InverseGaloisA5Base
 import Proofs.InverseGaloisA5Dedekind
 import Proofs.InverseGaloisA5Resultant
```

S4 PREP §"Step 4" simply says "Update `proofs/Proofs.lean` umbrella" without specifying
placement; the diff above is the alphabetically-correct insertion.

### 2.6 Sibling-file independence audit

The three sibling files `InverseGaloisA5Resultant.lean`, `InverseGaloisA5Resultant2.lean`,
`InverseGaloisA5ResultantDet.lean` were checked (`grep -n "import Proofs.InverseGaloisA5\b\|InverseGaloisA5\."`).

| File | `import Proofs.InverseGaloisA5` line? | Direct `InverseGaloisA5.*` reference? |
|---|:-:|:-:|
| InverseGaloisA5Resultant.lean | ❌ (only `import Proofs.InverseGaloisA5Resultant2`) | none |
| InverseGaloisA5Resultant2.lean | ❌ (only `import Mathlib`) | none |
| InverseGaloisA5ResultantDet.lean | ❌ (only `import Proofs.InverseGaloisA5Resultant2`) | one docstring mention only |

**Conclusion**: the three sibling files are **independent** of `Proofs.InverseGaloisA5`. Strategy
B's three-file split does not touch them. No edits required in the sibling files.

## 3. Pin-verification of S4c §3 workaround bearers (smul_eq_self)

S4c §3 proposes deriving `IsArithFrobAt.smul_eq_self : σ • Q = Q` in ~10–15 LOC. The proof
strategy uses these Mathlib names. Each is verified at SHA `2df2f01...`:

| # | Lemma / def | File | Status at pin |
|:-:|---|---|---|
| A1 | `Ideal.pointwise_smul_eq_comap` | `Mathlib/RingTheory/Ideal/Pointwise.lean` | ✓ exists (search/code 3 hits) |
| A2 | `Ideal.IsPrime` (for closure under powers) | `Mathlib/RingTheory/Ideal/Basic.lean` | ✓ |
| A3 | `IsArithFrobAt` (definition) | `Mathlib/RingTheory/Frobenius.lean:184` | ✓ |
| A4 | `IsArithFrobAt.exists_of_isInvariant` | `Mathlib/RingTheory/Frobenius.lean:216` | ✓ |
| A5 | `IsArithFrobAt.mul_inv_mem_inertia` (alternative route) | `Mathlib/RingTheory/Frobenius.lean:195` | ✓ |
| A6 | `IsArithFrobAt.conj` | `Mathlib/RingTheory/Frobenius.lean:200` | ✓ |
| A7 | `Ideal.inertia_le_stabilizer` (bridge: σ ∈ inertia ⇒ σ • Q = Q) | `Mathlib/RingTheory/Ideal/Pointwise.lean` AND `Ideal/Over.lean` AND `NumberTheory/RamificationInertia/Galois.lean` | ✓ exists (3 hits) |

**Critical new observation**: A5 + A7 give a **2-line proof** of `smul_eq_self` that's much
shorter than S4c §3's 10–15-LOC sketch:

```lean
-- Proposed cleaner alternative to S4c §3's smul_eq_self workaround:
lemma IsArithFrobAt.smul_eq_self_of_inertia
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Group G] [MulSemiringAction G S] [SMulCommClass G R S]
    {σ : G} {Q : Ideal S} (Q_prime : Q.IsPrime) [Finite (S ⧸ Q)]
    (Hσ : IsArithFrobAt R σ Q) : σ • Q = Q := by
  -- From `mul_inv_mem_inertia` (line 195) applied to σ and σ itself,
  -- 1 = σ·σ⁻¹ ∈ inertia Q. Not useful.
  -- Better: use Frobenius congruence directly.
  -- For x ∈ Q: σ • x ≡ x^q (mod Q). Since Q is prime + closed under products, x^q ∈ Q,
  -- hence σ • x ∈ Q. So σ • Q ⊆ Q. By orbit-stabilizer + finite-orbit primesOver,
  -- σ • Q is also prime over the same restriction, hence equality.
  sorry
```

S4c §3 already proposes this; the cleanup here is: **pin-confirmed** that all bearers exist.

The alternative "bypass via `exists_of_isInvariant`" path (S4c §3.4 second paragraph) is also
viable: the σ returned by `IsArithFrobAt.exists_of_isInvariant` (line 216) is constructed
inside the proof via `Ideal.Quotient.stabilizerHom_surjective` (line 232 of Frobenius.lean
at the pin), so it lives in `MulAction.stabilizer G Q` **by construction** of the proof body.
However, extracting that fact from `.choose` requires re-running the construction in
`InverseGaloisA5Dedekind.lean`, which is what S4c §3.4 estimates at ~15 LOC.

**Recommendation**: use S4c §3's `smul_eq_self` workaround (the standalone lemma). The bearer
chain is fully pin-confirmed; the proof is short; the lemma is upstream-friendly (post-S5,
upstream to Mathlib as `IsArithFrobAt.smul_eq_self`, which appears to have been added to
HEAD post-v4.26.0 in a different but equivalent form via `arithFrobAt_mem_stabilizer`).

## 4. Pin-verification of S4c §4 Option B workaround bearers (card_stabilizer extraction)

S4c §4 Option B proposes extracting the middle ~12 lines of `ncard_primesOver_mul_card_inertia_mul_finrank`'s
proof body as a local lemma. The proof body uses these Mathlib names. Each is verified at SHA:

| # | Lemma / def | File | Status at pin |
|:-:|---|---|---|
| B1 | `ncard_primesOver_mul_card_inertia_mul_finrank` (the source proof to extract from) | `Mathlib/NumberTheory/RamificationInertia/Galois.lean:298` | ✓ (full proof at lines 302–321) |
| B2 | `Ideal.Quotient.stabilizerHom` | `Mathlib/RingTheory/Ideal/Over.lean:315` | ✓ |
| B3 | `Ideal.Quotient.stabilizerHom_surjective` | `Mathlib/RingTheory/Invariant/Basic.lean:385` | ✓ |
| B4 | `Ideal.Quotient.ker_stabilizerHom` | `Mathlib/RingTheory/Ideal/Over.lean:328` | ✓ |
| B5 | `MulAction.orbitProdStabilizerEquivGroup` | `Mathlib/GroupTheory/GroupAction/Quotient.lean` | ✓ (search/code 2 hits) |
| B6 | `QuotientGroup.quotientKerEquivOfSurjective` | (standard Mathlib QuotientGroup) | ✓ (transitively imported) |
| B7 | `IsGalois.card_aut_eq_finrank` | `Mathlib/FieldTheory/Galois/Basic.lean` (and 4 other files use it) | ✓ |
| B8 | `Subgroup.card_mul_index` (via `.ker.card_mul_index`) | `Mathlib/GroupTheory/Index.lean` | ✓ |
| B9 | `Ideal.Quotient.finite_of_isInvariant` (used inside B1's proof) | `Mathlib/RingTheory/Invariant/Basic.lean` (line ~300) | ✓ |
| B10 | `Ideal.Quotient.normal` (constructs the `IsGalois (R/p) (S/P)` instance) | `Mathlib/RingTheory/Invariant/Basic.lean` (line ~320) | ✓ |
| B11 | `Subgroup.subgroupOfEquivOfLe` | `Mathlib/GroupTheory/Subgroup/Basic.lean` | ✓ |
| B12 | `inertia_le_stabilizer` (used implicitly via `Ideal.subgroupOf`) | (multiple files; see A7) | ✓ |
| B13 | `Ideal.IsMaximal` / `Ideal.LiesOver` instances (typeclass plumbing) | various | ✓ |

**Full bearer chain pin-confirmed.** No phantom risk for Option B's extraction.

**One nuance** worth noting for the S4 ACT implementer: the source proof at
`Galois.lean:302–321` uses an `attribute [local instance 1001] Ideal.Quotient.field
Module.Free.of_divisionRing in` *before* the lemma (line 297). The extraction must
either replay that `attribute [local instance 1001] ... in` line OR ensure the same
instance ordering. S4c §4 Option B does **not** mention this. Failure to include the
`attribute` modifier would cause Lean to synthesize the wrong (slower or non-`Free`)
instance for `Module.finrank (R ⧸ p) (S ⧸ P)`, potentially producing a `decide`-elaboration
failure at the residue-field-cardinality step.

**Recommendation**: copy the `attribute [local instance 1001] Ideal.Quotient.field
Module.Free.of_divisionRing in` line verbatim into `InverseGaloisA5Dedekind.lean`
immediately before the extracted local lemma.

## 5. Re-verification of S4c phantom flags at SHA

S4c (PR #18731 merged 2026-05-13) flagged two phantoms:

| Phantom | S4c verdict | Re-verification (this PREP, 2026-05-15) |
|---|---|---|
| `arithFrobAt_mem_stabilizer` | absent at pin; HEAD has it at Frobenius.lean:266 | ✅ still absent at SHA `2df2f01...`; ✅ still present at HEAD line 266 |
| `card_stabilizer_eq_card_inertia_mul_finrank` | name doesn't exist anywhere | ✅ still absent at SHA; ✅ still absent at HEAD |

No Mathlib bump has been merged in the ~2 days since S4c. Both phantoms remain
load-bearing for the workaround plan. **S4 ACT must use the workarounds**, not the
phantoms.

## 6. Updated post-workaround S4 ACT LOC estimate

S4c §6 published this final table:

> | Step | Original LOC | Original API | Post-pin-audit LOC | Post-pin-audit API |
> | … | … | … | … | … |
> | **Total** | **205–255** | | **247–307** | |

This PREP confirms the table; no LOC adjustment needed. Cumulative S4 ACT estimate
(sub-step (a) + (b) + (c) all post-workaround): **~270–410 LOC**, consistent with the
state.md "Current Focus" line "Post-workaround S4 ACT estimate revised from 235-360
LOC to **270-410 LOC** (~+20%)".

## 7. Cross-base paste readiness against open STATE-SYNC PR #19081

STATE-SYNC PR #19081 (open, MERGEABLE per `gh pr view`) modifies exactly 3 files:

1. `research/problems/inverse-galois-a5-oq-01/state.md`
2. `research/problems/inverse-galois-a5-oq-01/sessions/2026-05-14-state-sync-s4-prep-chain-consolidation.md`
3. `src/data/research/problems/inverse-galois-a5-oq-01.json`

**This S4d PREP** modifies exactly 1 file:

1. `research/problems/inverse-galois-a5-oq-01/sessions/2026-05-15-s4d-prep-strategy-b-split-point-and-workaround-bearer-audit.md` (new file)

**Disjoint file sets** ⇒ no merge conflicts regardless of merge order. Lean auto-merge clean.

Post-merge ordering (any of):
- (S4d, then STATE-SYNC): both apply cleanly; STATE-SYNC's "Session Log" table won't yet
  reference S4d (acceptable — a later STATE-SYNC will absorb it).
- (STATE-SYNC, then S4d): both apply cleanly; the next STATE-SYNC sweep will absorb the
  S4d note alongside any other post-STATE-SYNC PREPs.

## 8. Conflict-free guarantees

- 1 new file (this session note).
- 0 edits to existing files.
- 0 Lean changes.
- 0 Docker builds.
- 0 axiom / sorry / theorem / lemma deltas.
- 0 gallery-data edits (no `meta.json`, `annotations.json`, `index.ts`, or
  `src/data/research/problems/inverse-galois-a5-oq-01.json` edits).
- 0 edits to `state.md`, `knowledge.md`, `problem.md`.

## 9. Recommendation for S4 ACT picker

After this PREP, the S4 ACT implementer has:

1. A **verified split-point** (line 1896 of the parent, immediately after `gal_card_dvd_60_proved`)
   for the S5 follow-up — no forward-reference re-audit needed.
2. A **fully pin-verified bearer chain** for the two S4c workarounds — no surprise phantoms.
3. A **stale-docstring punch list** (lines 1907, 2052, 2057, 2059–2063 in the parent) that S5
   must clean up, with an explicit "defer to S5" instruction so the S4 ACT PR doesn't bloat.
4. A **`set_option` + `open` + `namespace` carry-over checklist** (§2.4) for S5.
5. An **umbrella-import placement diff** (§2.5) for `proofs/Proofs.lean`.
6. A **sibling-file independence verdict** (§2.6) confirming Strategy B doesn't ripple to
   the three `InverseGaloisA5Resultant*` siblings.
7. A **`local instance 1001` attribute warning** (§4) for the Option B extracted lemma.

Expected effort to ship S4 ACT after this PREP: **unchanged at ~270-410 LOC**, but with
~10–15 min reduction in audit overhead per the punch list.

## 10. Anti-targets

This PREP does **not**:

- Modify any prior session note (S1-OBSERVE, S2-ORIENT, S3-substep-a/b/c, S4-PREP, S4b-PREP,
  S4c-PREP). They stay as historical record.
- Modify any Lean file (parent, companion, or sibling).
- Modify `state.md`, `knowledge.md`, `problem.md`, gallery `meta.json`/`annotations.json`,
  or `src/data/research/problems/inverse-galois-a5-oq-01.json`.
- Execute S4 ACT (still pending; reserved for the picker who follows this PREP chain).
- Execute S5 (still pending; reserved for after S4 ACT discharges the sorry).
- Touch sibling slugs (e.g. oq-02, oq-04, oq-05).
- Re-do the S4b annotations.json audit (PR #18633 covers that orthogonally).

## 11. Race-awareness

`gh pr list --search "inverse-galois-a5-oq-01" --state open` at PREP push time
(~06:42 UTC, 2026-05-15) returns:

| PR | Title | Disjointness verdict |
|---|---|---|
| #19081 | STATE-SYNC — align tracker with 6 merged S3/S4-PREP-chain PRs (doc-only) | **disjoint** (modifies state.md + session note + JSON; this PREP modifies only a new session file) |

No other open PR on slug. The most recent merge on slug was PR #18731 (S4c PREP) on
2026-05-13 ~10:16 UTC — ~2 days prior. Past saturation window for slug-level activity.

## 12. Honesty calibration

- **Mode**: doc-only PREP. Zero Lean impact this iteration.
- **Value delivered**: audit-correction of S4 PREP's unverified split-point claim + audit
  of S4c's workaround-bearer chain. Reduces S4 ACT implementer risk on (a) forward-reference
  surprises during the S5 split, (b) phantom-bearer surprises inside the S4c §3 / §4
  workarounds.
- **Not delivered**: S4 ACT itself remains pending. The parent still has 1 axiom. The
  gallery status remains `axiomatized`.
- **Not load-bearing**: a future S4 ACT picker could *ignore* this PREP and still ship a
  correct S4 ACT — they would re-derive everything here as part of their pre-flight,
  taking ~20–30 min extra. This PREP is a **shortcut**, not a precondition.
