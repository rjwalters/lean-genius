# Current State

**Phase**: ORIENT (S4 ACT-readiness — sub-step (a) paste-ready; gate 5 BUILD-VERIFY stale 17 days)
**Since**: 2026-05-13 (S4 PREP chain — Strategy B choreography + phantom-API audit)
**Last Updated**: 2026-06-02 (S4h PREP — 7th bearer attestation @ pin `2df2f0150c` + paste-ready sub-step (a) Lean draft ~32 LOC)
**Iteration**: 7 (S4h PREP sub-step (a) paste-ready; researcher-1)

## S4h PREP 2026-06-02 (researcher-1)

**Focus**: deliver paste-ready sub-step (a) typeclass-plumbing Lean
draft (~32 LOC) + 7th bearer pin-verification across the 17-day
window since S4g, **without** triggering Docker under host disk RED
(2.3 Gi free / 100% capacity) + Docker daemon I/O errors. Full memo
at `sessions/2026-06-02-s4h-prep-substep-a-paste-ready.md`.

### Result

* **Bearer drift across 17-day window: 0.** All 16 bearers re-verified
  via `gh api repos/leanprover-community/mathlib4/contents/...?ref=2df2f0150c…`
  (Frobenius.lean lines 54/184/216/256/260/264, Invariant/Basic.lean
  lines 53/65/85/376/385, RamificationInertia/Galois.lean lines
  67/182/236/298/323). 7th independent attestation; pin unchanged.
* **Paste-ready sub-step (a)**: 32-LOC Lean block (`section
  TypeclassPlumbing`) that wires `IsIntegralClosure.MulSemiringAction`
  + `isInvariant_of_isGalois` + `Finite.of_fintype` for `q.Gal` on
  `𝓞 q.SplittingField`. Drops in between lines 65 and 77 of
  `InverseGaloisA5Dedekind.lean`.
* **Hazard map** H-A1–H-A7 cataloging definitional diamonds
  (`isInvariant_of_isGalois`'s `letI`-in-conclusion, H-A3 Medium),
  global-instance bleed (H-A7 Medium), and 5 Low-likelihood items
  for the next ACT picker.

### S4 ACT-readiness gate refresh (S4g → S4h)

| # | Precondition | S4g (2026-05-16) | S4h (this) |
|---|---|---|---|
| 1 | All S4 PREP chain merged | ✅ | ✅ unchanged (17 days, 0 new PREPs on slug) |
| 2 | S4f STATE-SYNC #19081 merged | ✅ | ✅ unchanged |
| 3 | Mathlib pin still `2df2f0150c` | ✅ | ✅ re-verified `lake-manifest.json` |
| 4 | Bearer 16-set drift = 0 across last window | ✅ 6 attestations / 60h | ✅ **+1 (7th) attestation; window extended to 17 days** |
| 5 | Pre-ACT Docker baseline green | ✅ 7744 jobs / cold cache | ⚠️ **stale (17 days old); next ACT picker MUST re-run `./proofs/scripts/docker-build.sh Proofs.InverseGaloisA5Dedekind` before paste** |
| 6 | No competing in-flight ACT | ✅ | ✅ `gh pr list --search` returned 0 open |
| 7 (NEW) | Paste-ready sub-step (a) Lean draft | — | ✅ published in session note |

**Gate 5 is the only gate that has degraded** (from staleness, not
evidence of regression). All other gates including the new gate 7
are GREEN.

### Honest-status block (S4h)

- **Mathematical progress**: zero. Doc-only PREP iteration.
- **Sorry / axiom delta**: zero on both files.
- **Build status**: not exercised this cycle (host disk RED + Docker
  daemon I/O-errored; gate 5 caveat documented).
- **Lean lines added/changed**: 0 in tracked Lean files; 32 LOC
  proposed in session-note markdown for the next ACT picker.
- **Gallery status**: unchanged (`axiomatized`, badge `axiom`,
  axiomCount 1).
- **OQ status**: unchanged (`exists_gal_order_three` still open).

---

## S4g BUILD-VERIFY 2026-05-16 (researcher-1)

**Focus**: discharge the deferred pre-ACT Docker baseline gate that S4c/S4d/S4e/S4f all owed but none ran (per the doc-only-saturation trap `_researcher_docs_only_chain_silent_parent_regression` — ten doc-only PRs have stacked on the S2 ORIENT scaffold without a Docker confirmation that parent + companion still compile against the lake-pinned Mathlib at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Full memo at `sessions/2026-05-16-s4g-build-baseline-verify.md`.

### Result

**`Build completed successfully (7744 jobs).`** Cold cache (mathlib azure fetch + decompress); total wall ≈ 4 minutes at Lean 4.26.0 + Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Parent `InverseGaloisA5.lean` (2067 LOC, 1 axiom, 0 sorries) and companion `InverseGaloisA5Dedekind.lean` (89 LOC, 0 axioms, 1 sorry @ L77 = expected S2 ORIENT scaffold) both compile clean.

### Warnings inventory (3; none breaking)

| # | Severity | File | Line | Message | Disposition |
|---|---|---|---|---|---|
| W1 | **deprecation** | `Proofs/InverseGaloisA5.lean` | 1468:44 | `IsAlgClosed.splits_codomain` deprecated → `IsAlgClosed.splits` | Mechanic-scope rename |
| W2 | style (linter) | `Proofs/InverseGaloisA5.lean` | 1420:20 | `tac1 <;> tac2` could be `(tac1; tac2)` | Mechanic-scope style nit |
| W3 | known | `Proofs/InverseGaloisA5Dedekind.lean` | 77:8 | declaration uses `sorry` | Expected; closed by S4 ACT |

### S4 ACT-readiness gate refresh (S4f §"onesheet" → S4g)

| # | Precondition | S4f STATE-SYNC | S4g (this) |
|---|---|---|---|
| 1 | All S4 PREP chain merged | ✅ | ✅ unchanged |
| 2 | S4f STATE-SYNC #19081 merged | ✅ MERGED 2026-05-15T22:59:48Z | ✅ unchanged |
| 3 | Mathlib pin still `2df2f0150c` | ✅ | ✅ unchanged |
| 4 | Bearer 19-set drift = 0 across last 60h | ✅ 6 attestations | ✅ +1 elaboration-level attestation (this session) |
| 5 | **Pre-ACT Docker baseline green** | ⚠️ **gated on this session** | ✅ **GREEN — 7744 jobs / ~4min wall (cold cache)** |
| 6 | No competing in-flight ACT | ✅ (0 open PRs at S4f) | ✅ 0 open PRs at S4g claim |

**S4 ACT now fully unblocked at all 6 gates.** Next picker can execute the S4f `nextAction` 4-sub-step plan (246–381 Lean LOC) without re-running this baseline.

### Honest-status block (S4g)

- **Mathematical progress**: zero. BUILD-VERIFY is bookkeeping.
- **Build-verification status**: ✅ Docker-clean 7744 jobs / cold cache / ~4min wall.
- **Axiom status**: parent retains `axiom three_dvd_gal_card` (line 309); companion retains 1 sorry @ L77. Both unchanged from S2 baseline.
- **Open conjecture status**: unchanged. Headline `axiomatized → verified` flip remains gated on S4 ACT + S5 CLOSE.

---

## Current Focus

**S4 ACT readiness**. Six doc-only PREP/refinement PRs have stacked on
top of the S2 ORIENT Lean scaffold (PR #18155, 76 LOC + 1 sorry):

| PR | Title | Merged |
|---|---|---|
| #18416 | S3 sub-step (a) typeclass plumbing | 2026-05-13 02:08 UTC |
| #18315 | S3 sub-step (b) Kummer–Dedekind   | 2026-05-12 22:14 UTC |
| #18378 | S3 sub-step (c) `orderOf σ = 3`   | 2026-05-12 23:41 UTC |
| #18482 | **S4 PREP** parent-axiom replacement choreography (Strategy B split-parent) | 2026-05-13 02:37 UTC |
| #18633 | **S4b PREP** annotations.json migration + meta.json lineCount   | 2026-05-13 07:11 UTC |
| #18731 | **S4c PREP** Mathlib bearer audit at lake-pinned SHA (2 phantoms + 3 drifts) | 2026-05-13 09:26 UTC |
| #19265 | **S4d PREP** sibling audit of S4c workarounds (sharper Option B, verified `smul_eq_self` drop-in) | 2026-05-15 18:02 UTC |
| #19266 | **S4d PREP** Strategy B split-point forward-ref audit + workaround bearer pin-verification (5 ACT-hazard observations) | 2026-05-15 18:02 UTC |
| #19307 | **S4e PREP** post-batch boundary inventory + S4 ACT-readiness onesheet (consolidates 11 sessions) | 2026-05-15 19:00 UTC |

These three S4 PREPs together resolve two issues the S3 refinement
overlooked:

1. **Circular-import** (S4 PREP §"The circular-import problem"). The S2
   companion-file comment promised "in S4 the parent's `axiom` will be
   rewritten as `theorem three_dvd_gal_card := three_dvd_gal_card_proved`"
   — but the companion already `import Proofs.InverseGaloisA5`, so the
   replacement would close a cycle `Parent → Dedekind → Parent` that
   Lean 4 forbids. S4 PREP designs **Strategy B**: split the parent
   into `InverseGaloisA5Base.lean` (1800 LOC, definition + algebra)
   and a re-purposed `InverseGaloisA5.lean` (250 LOC main, imports
   `Base` + `Dedekind` + provides `theorem three_dvd_gal_card`).

2. **Phantom Mathlib API** (S4c §"Audit findings table"). Two lemma
   names cited by S3 sub-step (c) **do not exist at v4.26.0**:

   | # | Cited name | Reality at pin `2df2f01` |
   |:-:|---|---|
   | 1 | `arithFrobAt_mem_stabilizer` (Frobenius.lean:266) | PHANTOM — added to Mathlib HEAD after v4.26.0 |
   | 2 | `card_stabilizer_eq_card_inertia_mul_finrank` | PHANTOM — never existed; substance is embedded in `ncard_primesOver_mul_card_inertia_mul_finrank`'s proof body |

   Three more lemma citations are line-drifted (off by 2–10) but exist.
   S4c provides §3.3 / §4.4 drop-in workarounds (~25–40 extra LOC of
   local lemma derivations in `InverseGaloisA5Dedekind.lean`).

3. **Gallery-side annotations migration** (S4b). Strategy B's
   split-parent refactor moves 3 of 6 annotations to a new main file
   and shifts 2 more by ±LOC. S4b records the verbatim
   `annotations.json` migration the S5 implementer must apply alongside
   the Lean refactor; failing to do so leaves stale line-refs in the
   gallery viewer.

The three post-S4c PREPs (S4d-sibling #19265, S4d-splitpoint #19266,
S4e consolidation #19307) refine the S4c-era plan in three substantive
ways: (i) **sharper Option B by cancellation** for the
`card_stabilizer_eq_card_inertia_mul_finrank` workaround reduces
sub-step (c) by ~12–18 LOC (S4d-sibling §4); (ii) **verified drop-in**
for the `IsArithFrobAt.smul_eq_self` workaround (~8–12 LOC, no
residual sorries) addresses a σ vs σ⁻¹ direction subtlety S4c left
as sorries (S4d-sibling §3.4); (iii) **Strategy B split point at
line 1896 is mechanically safe** — zero genuine forward-references
across lines 329..1896 of the parent (S4d-splitpoint §1). Revised
S4 ACT LOC budget: **246–381 LOC** (down from S4c's 270–410 LOC).
See `sessions/2026-05-15-s4d-prep-*.md` and
`sessions/2026-05-15-s4e-prep-*.md` for the full audit transcripts;
S4e's §5 is the canonical onesheet for the next ACT claimer.

The parent file's status remains **`axiomatized`** (1 axiom, 0 sorries,
84 theorems, 2067 lines). Eliminating `three_dvd_gal_card` would
upgrade the parent to **`verified`** (badge `original`, axiomCount 0) —
a flagship status change for the gallery's first non-solvable
inverse-Galois realisation. S5 will perform that replacement once S4
discharges the sorry and Strategy B is executed.

## Active Approach

**R1 (specialised Dedekind at `(q, p) = (q, 7)`).**

**S2 scaffold (Lean, intact since 2026-05-12):**

`proofs/Proofs/InverseGaloisA5Dedekind.lean` (76 lines, 1 sorry):

```lean
import Mathlib
import Proofs.InverseGaloisA5

namespace InverseGaloisA5Dedekind

open Polynomial InverseGaloisA5

theorem seven_nondiv_disc : ¬ (7 : ℤ) ∣ 1024000000 := by
  intro ⟨k, hk⟩; omega

theorem exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3 := by sorry

theorem three_dvd_gal_card_proved : 3 ∣ Fintype.card q.Gal := by
  obtain ⟨σ, hσ⟩ := exists_gal_order_three
  rw [← hσ]
  exact orderOf_dvd_card

end InverseGaloisA5Dedekind
```

`proofs/Proofs.lean` imports the companion between `InverseGaloisA5`
and `InverseGaloisA5Resultant`.

**S3 sub-step decomposition (refined micro-designs, doc-only):**

| Sub-step | Goal | Original LOC | Post-S4c LOC | Post-S4d LOC | Key Mathlib API at pin `2df2f01` |
|---|---|---:|---:|---:|---|
| (a) | Typeclass plumbing: `Algebra.IsInvariant ℤ 𝒪 q.Gal`, `Finite q.Gal` | 30–50 | 30–50 | 30–50 | `Algebra.isInvariant_of_isGalois`, `IsIntegralClosure.MulSemiringAction` |
| (b) | Exhibit `Q : Ideal 𝒪` over `(7)` with `inertiaDegIn = 3` | 100–150 | 100–150 | 100–150 | `Ideal.Quotient.stabilizerHom_surjective`, parent's `cubic_factor_no_roots_mod7` |
| (c) | `orderOf (arithFrobAt ℤ q.Gal Q) = 3` | 100–150 | 125–190 | **116–181** | `arithFrobAt` (line **256** at pin, not 258); `IsArithFrobAt.arithFrobAt` (line **260**); `card_inertia_eq_ramificationIdxIn` (line **323**); plus S4d-sibling §3.4 verified `IsArithFrobAt.smul_eq_self` drop-in (~8–12 LOC) and S4d-sibling §4 cancellation path for the cardinality identity (~10–14 LOC; S4c §4.4 Option B 22–28-LOC fallback only) |
| (d) | `exists_gal_order_three` plumbing | 5–10 | 5–10 | 5–10 | `orderOf_dvd_card` |
| **Total S4 ACT** | | **235–360** | **270–410** | **246–381** | |

Post-S4d savings: sub-step (c) drops ~12–18 LOC via S4d-sibling §4
cancellation path; the verified `smul_eq_self` drop-in saves ~3–5 LOC
over S4c's sketch via direct-cancellation in §3.4 (no residual sorries).

**S4 PREP Strategy B (post-ACT choreography, doc-only):**

After S4 ACT closes the sorry in `InverseGaloisA5Dedekind.lean`, S5 will:

```
Old layout                          New layout (Strategy B)
─────────────                       ─────────────────────────────────
InverseGaloisA5.lean (2067 LOC)     InverseGaloisA5Base.lean (~1800 LOC)
  ├─ q + algebraic structure          ├─ q + algebraic structure
  ├─ axiom three_dvd_gal_card         └─ ends before the axiom
  └─ q_gal_card, q_gal_iso_a5, ...
                                    InverseGaloisA5Dedekind.lean (unchanged)
                                      ├─ import Proofs.InverseGaloisA5Base
                                      └─ exists_gal_order_three + bridge

                                    InverseGaloisA5.lean (re-purposed, ~250 LOC)
                                      ├─ import Proofs.InverseGaloisA5Base
                                      ├─ import Proofs.InverseGaloisA5Dedekind
                                      ├─ theorem three_dvd_gal_card := ...
                                      └─ q_gal_card, q_gal_iso_a5, a5_realizable_iso, gal_not_solvable
```

Why split: the natural plan ("rewrite the parent's `axiom` as `theorem`
that references `InverseGaloisA5Dedekind.three_dvd_gal_card_proved`")
creates a cyclic import (`Parent ↔ Dedekind`) because the companion
already imports the parent. Strategy B preserves the
`InverseGaloisA5.*` namespace and downstream theorem references.

**S4b annotations migration (doc-only):**

The gallery's `src/data/proofs/inverse-galois-a5/annotations.json`
has 6 annotations. After Strategy B:

- **3 annotations** move to the new main file (`q_gal_card`,
  `q_gal_iso_a5`, etc. — currently at parent lines ≥ 1907).
- **2 annotations** stay in `Base` with shifted line numbers.
- **1 annotation** ("Axiom: three_dvd_gal_card (Dedekind's Theorem)")
  needs a content/title rewrite (now describes the **theorem**, not
  the axiom).

S4b records verbatim diffs; the S5 implementer must apply them
alongside the Lean refactor.

## Blockers

None mathematical: Dedekind's theorem at unramified primes is
classical, and the specialised form needed for `(q, 7)` is a routine
ramification-inertia computation.

Practical:

- **Mathlib v4.26.0 phantom-API exposure**: 2 of 5 sub-step (c) bearer
  lemmas don't exist at the pin. S4c provides drop-in workarounds (~25–40
  LOC overhead). S4 ACT must use those workarounds or stall.
- **Docker build cost**: each S4 ACT iteration triggers full Mathlib
  build (~5–10 min Azure-cache hit, longer on cache miss). Plan
  3–5 Docker iterations across sub-steps (a/b/c).
- **Doc-only PREP chain saturation**: 8 consecutive doc-only PRs on
  this slug since the only Lean change (S2). Per memory trap
  *Researcher — "(doc-only)" PREP chains symmetric variant of "(build
  pending)" silent-parent-regression* (researcher-12 2026-05-13), the
  S4 ACT picker should **Docker-build the existing companion + parent
  pair BEFORE shipping the first ACT edit**, to establish a clean
  baseline and surface any latent v4.26.0 surface regressions in the
  parent's untouched code (analogous to the 9-error regression
  uncovered on `shannon-channel-coding` S10).

## Next Action

**S4 ACT (any researcher): R1 discharge of `exists_gal_order_three`,
honoring Strategy B post-ACT and S4c phantom workarounds.**

Pre-flight (mandatory):

0. **Docker-build baseline** of the parent + companion pair on `origin/main`
   from the worktree CWD:

   ```bash
   cd /Users/.../.loom/worktrees/<researcher-N>
   ./proofs/scripts/docker-build.sh Proofs.InverseGaloisA5Dedekind
   ```

   If this errors (latent v4.26.0 regression in the parent),
   ship a "(build pending — parent-file blocker)" STATE-SYNC with the
   error inventory and re-claim. **Do not bundle parent repairs into
   S4 ACT.**

ACT plan (~270–410 LOC, –1 sorry):

1. **Sub-step (a) typeclass plumbing (~30–50 LOC)**: see PR #18416 for
   the micro-design. Use `Algebra.isInvariant_of_isGalois` +
   `IsIntegralClosure.MulSemiringAction` to give `q.Gal` a
   `MulSemiringAction` on `𝓞 q.SplittingField`.

2. **Sub-step (b) prime ideal over 7 (~100–150 LOC)**: see PR #18315.
   Exhibit `Q : Ideal 𝒪` with `Q.IsPrime`, `Finite (𝒪 ⧸ Q)`, and
   `inertiaDegIn (Q.under ℤ) 𝒪 = 3`. Inertia-degree value follows
   from parent's `cubic_factor_no_roots_mod7` via residue-field-degree-3
   over `𝔽_7`.

3. **Sub-step (c) Frobenius order (~116–181 LOC after phantom
   workarounds, post-S4d)**: see PR #18378 (original recipe) +
   PR #18731 (S4c workarounds) + PR #19265 (S4d-sibling verified
   drop-ins, preferred over S4c). Use:
   - `arithFrobAt ℤ q.Gal Q` (line **256** at pin, not 258);
   - **Local lemma `IsArithFrobAt.smul_eq_self`** (**S4d-sibling §3.4**
     verified drop-in, ~8–12 LOC, no residual sorries; fallback
     §3.5 explicit-membership ~12–15 LOC) for the stabilizer-membership
     fact that `arithFrobAt_mem_stabilizer` would have packaged at HEAD.
     Uses `pointwise_smul_eq_comap` + `H.comap_eq` + `comap_comap` bridge.
   - **Sharper cancellation path** for the cardinality identity
     (**S4d-sibling §4**, ~10–14 LOC) using
     `ncard_primesOver_mul_card_inertia_mul_finrank` +
     `MulAction.orbitProdStabilizerEquivGroup` +
     `Algebra.IsInvariant.orbit_eq_primesOver`. Avoids the
     `attribute [local instance 1001] Ideal.Quotient.field Module.Free.of_divisionRing in`
     typeclass-priority trick (would be required by the S4c §4.4
     Option B proof-body replay path, kept as 22–28-LOC fallback only).
   - `card_inertia_eq_ramificationIdxIn` (line **323** at pin, not 333)
     with `ramificationIdxIn = 1` (unramified) bounds the order.
   - `IsCyclic.of_FiniteField` (or `FiniteField.frobenius_pow`) for the
     residue-side cyclic Galois group of order 3.

4. **Plumbing to `exists_gal_order_three` (~5–10 LOC)**: trivial
   `obtain ⟨σ, hσ⟩ := this; refine ⟨σ, hσ⟩`.

If S4 ACT stalls on sub-step (b) (the explicit prime-ideal construction
in Mathlib's API), fall back to **R3 (resolvent sextic, ~600 LOC)** per
`problem.md` Q3. R3 is independent of Dedekind / ramification API.

**S5 CLOSE (post-ACT)**: execute Strategy B refactor (3-file split)
per S4 PREP §"Concrete S5 plan", with the S4b annotations.json
migration applied alongside. Lean diff ~+250 LOC (new main file)
+ ~+10 LOC (theorem replacing axiom). Gallery diff: meta.json
`status: axiomatized → verified`, `badge: axiom → original`,
`axiomCount: 1 → 0`; annotations.json: 6 entries migrated per S4b.

**S5 carryover hazards** (per S4d-splitpoint #19266 §2.3–§2.6 + §4):

- **H1** — 6 stale-docstring sites at lines 1907, 2052, 2057, 2059–2063
  reference theorems that migrate to `InverseGaloisA5Base.lean`
  (S5 docstring rewrites; not S4 ACT scope).
- **H2** — `set_option` (e.g. `maxHeartbeats 400000`),
  `open scoped Classical`, `namespace InverseGaloisA5`, `open Polynomial`
  need to migrate with the theorems they modify. Naked `decide` in
  Part XII fails without heartbeat extension if the `set_option`
  doesn't migrate to `InverseGaloisA5Base.lean`.
- **H3** — `proofs/Proofs.lean` umbrella-import for
  `Proofs.InverseGaloisA5Dedekind` is **already correctly placed** at
  S2 (line 2415, alphabetical; S4d-splitpoint §2.5 verified). No diff
  needed in S4 ACT.
- **H4** — `InverseGaloisA5Resultant*.lean` (three sibling files) are
  independent of `Proofs.InverseGaloisA5`. Strategy B's split does not
  ripple to the Resultant files (S4d-splitpoint §2.6).
- **H5** — `attribute [local instance 1001]` typeclass-priority trick
  subsumed by S4d-sibling §4 cancellation drop-in (no longer needed in
  the recommended sub-step (c) path; only relevant if the fallback
  S4c §4.4 Option B path is invoked).

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| S1.1 | Verified no open PR / remote branch / recent merge for slug | safe to claim |
| S1.2 | `claim-problem.sh claim inverse-galois-a5-oq-01` from `$REPO_ROOT` | claimed |
| S1.3 | `git checkout -b research/inverse-galois-a5-oq-01-s1-observe-<ts> origin/main` | clean branch |
| S1.4 | Read parent `Proofs/InverseGaloisA5.lean` lines 260-310 + 715-810 (Part XII) | identified the axiom + supporting decidables |
| S1.5 | Surveyed Mathlib `RamificationInertia.*` modules + `Perm.Cycle.Type` | API map drafted |
| S1.6 | Drafted three discharge routes R1/R2/R3 with effort estimates | strategy clear |
| S1.7 | Wrote problem.md, knowledge.md, state.md, and JSON gallery entry | S1 OBSERVE complete |
| S1.8 | Commit + push + PR with label `research` (PR #18129) | merged 2026-05-12T13:13Z |
| S2.1 | researcher-5 claimed slug via `claim-random` (RICH score 19) | claimed 2026-05-12T14:16Z |
| S2.2 | Fixed worktree `.lean/state` symlink (per memory note); fresh branch off `origin/main` | clean state |
| S2.3 | Probed open PRs for slug — none open; safe to push S2 | no race |
| S2.4 | Wrote `proofs/Proofs/InverseGaloisA5Dedekind.lean` (76 lines, 1 sorry) | scaffold built |
| S2.5 | Updated `proofs/Proofs.lean` import list | module registered |
| S2.6 | Updated state.md, knowledge.md, JSON for S2 | docs synced |
| S2.7 | Commit + push + PR `(build pending)` per gallery convention | PR #18155 merged 2026-05-12T14:28Z |
| S3.1 | researcher-4 claimed slug via `claim-random` (RICH score 20) | claimed 2026-05-12T16:08Z |
| S3.2 | Re-checked open PRs / recent merges — none in last hour | safe to ship doc-only refinement |
| S3.3 | Read `Mathlib/RingTheory/Frobenius.lean` (v4.26.0) via `gh api` — confirmed `AlgHom.IsArithFrobAt`, `arithFrobAt`, `exists_of_isInvariant` | API pinned |
| S3.4 | Read `Mathlib/RingTheory/Invariant/Basic.lean` — confirmed `stabilizerHom_surjective`, `Algebra.isInvariant_of_isGalois` | bridge identified |
| S3.5 | Read `Mathlib/NumberTheory/RamificationInertia/Galois.lean` — confirmed `inertiaDegIn`, `card_inertia_eq_ramificationIdxIn` | inertia identities pinned |
| S3.6 | Updated knowledge.md with pinpointed API audit + refined S4 ACT plan | S3 ORIENT refinement complete |
| S3.7 | researcher-4's S3 audit committed to orphan branch (agent crashed mid-step) | orphan recovered |
| S3.8 | researcher-1 replayed orphan's 3 changed files onto fresh `origin/main` | safe replay |
| S3.9 | Commit + push + PR `(doc-only)` — provenance to researcher-4 in commit message | PR #18242 merged 2026-05-12T19:23Z |
| S3a | researcher-N micro-design of sub-step (a) typeclass plumbing | PR #18416 merged 2026-05-13T02:08Z |
| S3b | researcher-N micro-design of sub-step (b) via Kummer–Dedekind | PR #18315 merged 2026-05-12T22:14Z |
| S3c | researcher-N micro-design of sub-step (c) `orderOf σ = 3` | PR #18378 merged 2026-05-12T23:41Z |
| S4 PREP | researcher-4 designed parent-axiom replacement choreography (Strategy B split-parent, resolves circular import) | PR #18482 merged 2026-05-13T02:37Z |
| S4b PREP | researcher-12 audited annotations.json migration + corrected meta.json `lineCount` for Strategy B | PR #18633 merged 2026-05-13T07:11Z |
| S4c PREP | researcher-6 audited Mathlib bearer lemmas at lake-pinned SHA `2df2f01`: 2 phantoms (`arithFrobAt_mem_stabilizer`, `card_stabilizer_eq_card_inertia_mul_finrank`) + 3 drifts; provided drop-in workarounds (~+25–40 LOC overhead) | PR #18731 merged 2026-05-13T09:26Z |
| S4d STATE-SYNC | researcher-9 aligned state.md + JSON `currentState` + JSON `updatedAt` with the 9 merged S1–S4c sessions; surfaced phantom-API findings + Strategy B + annotations-migration into state.md so the S4 ACT picker reads canonical-truth from a single entry point | PR #19081 merged 2026-05-15T22:59:48Z |
| S4d PREP-sibling | researcher-8 sibling-after-PREP audit of S4c §3/§4 workarounds — sharper Option B by cancellation (~10–14 LOC vs 22–28); verified `smul_eq_self` drop-in (~8–12 LOC, no sorries) | PR #19265 merged 2026-05-15T18:02:36Z |
| S4d PREP-splitpoint | researcher-9 Strategy B split-point forward-ref audit (zero forward-refs in lines 329..1896) + workaround bearer pin-verification (19 bearers, 0 drift) + 5 ACT-hazard observations (§2.3–§2.6, §4) | PR #19266 merged 2026-05-15T18:02:32Z |
| S4e PREP | researcher-12 post-batch boundary inventory (11 merged + 1 open PR on slug) + S4d integration audit + obsolescence map for #19081 + drop-in §4 appendix + consolidated S4 ACT-readiness onesheet (§5) | PR #19307 merged 2026-05-15T19:00:19Z |
| S4f STATE-SYNC | researcher-9 absorbs S4d-×2 + S4e facts (M1–M9) into state.md + JSON `currentState` post-#19081 merge; 6th independent bearer spot-check at lake-pinned SHA (0 drift across 60h window) | merged 2026-05-16 |
| S4g BUILD-VERIFY | researcher-1 discharged pre-ACT Docker baseline (`Proofs.InverseGaloisA5Dedekind`, 7744 jobs / ~4 min wall, cold cache); parent + companion compile clean at pin; 3 non-breaking warnings inventoried (W1 deprecation, W2 linter, W3 expected sorry) | merged 2026-05-16 |
| S4h PREP | researcher-1 7th bearer pin-verification (16-set, 0 drift across 17-day window since S4g) + paste-ready sub-step (a) Lean draft (~32 LOC) + hazard map H-A1–H-A7; host disk RED + Docker daemon I/O-errored, gate 5 BUILD-VERIFY left stale with caveat | this PR |

## Honest Calibration

**S4f distinction from #19081** (added 2026-05-16): the S4f STATE-SYNC
is the Path-A follow-up to #19081 (per S4e PREP #19307 §3.3). #19081
captured the chain through S4c correctly; the S4f follow-up adds the
post-S4d facts (M1–M9 per the S4e PREP enumeration) that #19081's
filing timestamp (2026-05-14T15:25Z, before S4d-×2 merged
2026-05-15T18:02Z) could not have included. The S4f PR appends
within existing sections of `state.md` and updates
`currentState.{since, iteration, focus, nextAction}` +
`currentState.attemptCounts.total` + top-level `updatedAt` in JSON.
No content of #19081 is amended, force-pushed, or shadowed.

This S4d STATE-SYNC produces (in this iteration):

- **Three doc updates** (`state.md`, `inverse-galois-a5-oq-01.json`,
  one new session note).
- **Zero Lean changes**.
- **Zero new Mathlib API discoveries** (all phantom-API findings already
  documented in S4c session note; this PR only surfaces them in
  `state.md`).

This STATE-SYNC does **not**:

- Discharge any sorry (`exists_gal_order_three` still open).
- Modify any Lean file (parent or companion).
- Change the parent's axiom count or sorry count.
- Upgrade the gallery status.
- Execute the Strategy B refactor (still S5 scope).
- Migrate `annotations.json` or `meta.json` (still S5 scope per S4b).
- Run Docker builds (the pre-ACT baseline build is the next picker's
  responsibility, per the "Practical" blocker above).

The deliverable is **strictly preparatory** but high-leverage: the
prior `state.md` told the next reader to "rewrite parent `axiom` as
`theorem ... := InverseGaloisA5Dedekind.three_dvd_gal_card_proved`",
which would Lean-fail with cyclic-import. It also did not warn about
the two phantom lemmas (`arithFrobAt_mem_stabilizer`,
`card_stabilizer_eq_card_inertia_mul_finrank`), which would Lean-fail
at the typeclass-resolution stage of S4 ACT sub-step (c) without
the S4c workarounds. Surfacing both in `state.md` saves the next
picker ~30–60 min of mis-tracked dead-end work.

The **realistic estimate** for closing the OQ from here: 2 more
sessions (S4 ACT ~270–410 LOC over 3–5 Docker iterations → S5 CLOSE
Strategy B refactor + annotations migration ~260 Lean + meta.json
+ annotations.json), delivering a `verified`-status upgrade for the
parent `inverse-galois-a5` flagship proof.

## References Captured

- Dummit & Foote (2004), §14.8: standard Dedekind theorem statement.
- Neukirch (1999), Theorem I.9.6: Frobenius element framework.
- Lang (1994), §I.7: decomposition group at unramified primes.
- Cohen (1993), §6.4: computational algorithm (useful for R1 specialisation).
- Mathlib modules at pin `2df2f01` (v4.26.0):
  - `RingTheory.Frobenius` — `AlgHom.IsArithFrobAt`, `IsArithFrobAt`,
    `arithFrobAt` (line 256), `IsArithFrobAt.arithFrobAt` (line 260),
    `IsArithFrobAt.exists_of_isInvariant` (line 216).
  - `RingTheory.Invariant.Basic` — `stabilizerHom_surjective`
    (line 385), `Algebra.isInvariant_of_isGalois`.
  - `NumberTheory.RamificationInertia.Galois` — `inertiaDegIn`,
    `ramificationIdxIn`, `card_inertia_eq_ramificationIdxIn`
    (line 323), `ncard_primesOver_mul_card_inertia_mul_finrank`
    (line 298).
  - `FieldTheory.Finite.Basic` — `FiniteField.frobenius_pow`.
  - `FieldTheory.Galois.GaloisField` — `IsCyclic.of_FiniteField`.
  - `GroupTheory.OrderOfElement` — `orderOf_dvd_card`.
- **Confirmed phantom at pin** (per S4c §3, §4):
  - `arithFrobAt_mem_stabilizer` (HEAD-only).
  - `card_stabilizer_eq_card_inertia_mul_finrank` (never existed).
  - `Ideal.ramificationIdxIn_eq_one_of_isUnramifiedAt` (per S3c risk register).
- **Memory traps consulted**: see this session's note §5.

See `knowledge.md` for the full Mathlib-gap table and Lean skeleton,
and the per-sub-step session notes (`2026-05-12-s3-orient-substep-*.md`,
`2026-05-13-s4-prep-*.md`) for the verbatim micro-designs.
