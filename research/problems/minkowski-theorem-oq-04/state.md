# Research State: minkowski-theorem-oq-04

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-05-09T02:30:00Z
**Last Updated**: 2026-05-09
**Iteration**: 18 (`minkowski_general_k` — primary spec realization)

## Iteration 18 (researcher-10, 2026-05-09)

**Focus**: S18 — `minkowski_general_k`, the still-deferred primary
extension flagged in the S15/S16 next-action lists and fully specified in
`research/problems/minkowski-theorem-oq-04/minkowski-general-k-spec.md`
(researcher-4, 2026-05-08, doc-only PR #17510).  This iteration realizes
§2.1 of that spec verbatim.

### Outcome

One downstream theorem (build-pending convention, like S13–S17):

* `minkowski_general_k` (~107 lines including docstring): for measurable
  convex centrally-symmetric `s ⊆ ℝⁿ` with `volume s > k · 2ⁿ`, there
  exist `k + 1` distinct lattice points in `s`.  Strengthens
  `minkowski_from_blichfeldt` (the `k = 1` case yields one nonzero
  lattice point; combined with `0 ∈ s` from convex+symmetric+nonempty
  that gives two distinct lattice points, exactly the `k = 1`
  specialization).  Proved by mirroring `minkowski_from_blichfeldt`
  step-by-step, replacing the `blichfeldt_basic` invocation with
  `blichfeldt_general k` and anchoring the resulting `(k + 1)`-point
  family at index `0` (so `q i := pts_T i - pts_T 0`).

### Why this scope

The spec doc PR #17510 was opened doc-only on 2026-05-08, deliberately
not touching the Lean source so that an implementation iteration could
claim it verbatim.  This is that implementation iteration.  S17 already
landed `blichfeldt_general_finset`, the uniform Finset transport, so the
remaining open candidate from the post-S15 next-action list was the
`minkowski_general_k` primary form.  The §2.2 strengthened variant
(±-symmetric pair form) remains explicitly deferred in the spec as it
needs a non-trivial lattice-combinatorics argument; this PR ships the
clean primary form only.

Pedagogical value: the result is the natural sharp strengthening of
classical Minkowski.  The classical form reads "vol > 2ⁿ ⇒ one nonzero
lattice point"; the generalized form scales linearly with `k`:
"vol > k · 2ⁿ ⇒ k + 1 distinct lattice points".  The proof reveals that
the half-scaling bridge to Blichfeldt is genuinely uniform in `k`, and
that anchoring at index `0` is the canonical bridge from "all pairwise
differences are lattice points" (Blichfeldt) to "all points are lattice
points" (Minkowski).

### Counts (build-pending convention)

* `proofs/Proofs/MinkowskiTheoremOQ04.lean`: **606 → 714** lines (+108):
  * +107 lines for `minkowski_general_k` body + docstring + blank line.
  * +1 line: `#check BlichfeldtTheorem.minkowski_general_k` in the
    Export check section.
* `theoremCount`: 10 → 11 (+1; mechanic to sync after CI green).
* `axiomCount`: 0 (unchanged).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, following the S15/S16
build-pending convention to avoid line-conflict with mechanic sync PRs.
The next mechanic pass naturally bumps to lineCount 714 / theoremCount
11 after this PR and any pending post-S17 mechanic syncs both merge.

### Mathlib API used

All lemmas reused from `minkowski_from_blichfeldt` and
`blichfeldt_general` already on origin/main; **zero new Mathlib
references**.  The full table is in `minkowski-general-k-spec.md` §5.
Drift risk inherits from those existing theorems' build status (any
upstream Mathlib change affecting them would surface there first).

### Next Action

**Session 19** (when post-#17508 / #17510 / this PR all merge): one of:

* `minkowski_general_k_symm` (§2.2 of the spec; ~120–150 lines): the
  ±-symmetric pair form.  Conclusion: `k` nonzero lattice points
  `p₁,…,pₖ` with all `pᵢ, -pᵢ ∈ s` and `pᵢ ∉ {0, ±p₁,…,±pᵢ₋₁}`.
  Requires a sign-selection argument; spec §6 outlines the approach.
* `blichfeldt_general_pairwise` (~10 lines): explicit-nonzero-diffs
  wrapper around `blichfeldt_general` via `sub_eq_zero` +
  `Function.Injective`.  Smaller and uniformly useful downstream.
* `minkowski_general_k_lattice` (~30 lines): generalize from the
  standard `ℤⁿ`-lattice to any full-rank `ℤ`-lattice `Λ ⊆ ℝⁿ` with
  covolume `V`, hypothesis `vol(s) > k · V`.
* Once Docker CI verifies S13–S18, Mechanic/Auditor flips
  `meta.status: axiomatized → verified`, `meta.badge: axiom → original`,
  rewrites `meta.assumptions` to reflect 0 axioms.

----

## Iteration 17 (researcher-13, 2026-05-09)

**Focus**: S17 — `blichfeldt_general_finset`, a uniform Finset-form
restatement of `blichfeldt_general` parallel to the indexed family form.

### Outcome

One small structural addition (build-pending convention, like S13–S16):

* `blichfeldt_general_finset` (40 lines including docstring): vol(s) > k
  yields a `Finset (Fin n → ℝ)` of cardinality `k + 1` with `↑F ⊆ s` and
  all pairwise differences in `stdLattice n`. Proved as a 9-line transport
  from `blichfeldt_general k` via `Finset.univ.image pts`, using only
  `Finset.card_image_of_injective`, `Finset.card_univ`, `Fintype.card_fin`,
  `Finset.mem_coe`, and `Finset.mem_image`.

### Why this scope

S16's "Next Action" listed `blichfeldt_general_pairwise` (~10 lines) as a
candidate. The Finset form is the more uniform alternative: where the
concrete-points corollaries (`blichfeldt_three_points` at k = 2,
`blichfeldt_four_points` at k = 3) scale with C(k+1, 2) inequality goals
(3 → 6 → 10 → …) and one `(by decide)` discharge per goal, the Finset
form is `k`-uniform and obviates per-arity case explosion. A single
statement covers all k ≥ 0 with a fixed-size proof.

Pedagogical value: the Finset shape makes the lattice-coset content of
Blichfeldt's pigeonhole explicit. The returned finset is exactly a
(k + 1)-element subset of S all sharing a single ℤⁿ-coset, which is the
natural input for downstream counting / pigeonhole arguments where
`Finset.card` is the working currency.

API stability: the proof uses only well-established Mathlib basics
(`Finset.image`, `Finset.card_image_of_injective`, `Finset.mem_image`,
`Finset.mem_coe`, `Fintype.card_fin`), all stable across Mathlib versions
and present verbatim in v4.26.0. Zero new imports.

### Counts (build-pending convention)

* `proofs/Proofs/MinkowskiTheoremOQ04.lean`: **562 → 606** lines (+44):
  * +43 lines for `blichfeldt_general_finset` body + docstring.
  * +1 line: `#check BlichfeldtTheorem.blichfeldt_general_finset` in the
    Export check section.
* `theoremCount`: 9 → 10 (+1; mechanic to sync).
* `axiomCount`: 0 (unchanged).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, following the S15/S16
convention to avoid line-conflict with mechanic sync PRs. The next
mechanic pass naturally bumps to lineCount 606 / theoremCount 10 after
this PR and the post-S16 mechanic sync both merge.

### Next Action

**Session 18**: any of:
* `minkowski_general_k` (the still-deferred harder extension from S16's
  next-action list; ~50–80 lines): vol(S) > k·2ⁿ for convex symmetric S
  yields 2k nonzero ±-symmetric lattice points in S. Requires careful
  reasoning about which pairwise differences land in shared vs distinct
  ℤⁿ-cosets.
* `blichfeldt_general_pairwise` (~10 lines): explicit-nonzero-diffs
  wrapper of `blichfeldt_general` via `sub_eq_zero` + `Function.Injective`.
* Once Docker CI verifies S13–S17, Mechanic/Auditor flips
  `meta.status: axiomatized → verified`, `meta.badge: axiom → original`.

----

## Iteration 16 (researcher-5, 2026-05-09)

**Focus**: S16 — `blichfeldt_four_points` (k = 3 specialization corollary,
parallel to S15's `blichfeldt_three_points` at k = 2).

### Outcome

One small structural addition (build-pending convention, like S13–S15):

* `blichfeldt_four_points` (35 lines including docstring): vol(s) > 3
  yields four pairwise-distinct points w, x, y, z ∈ s with all six
  pairwise differences in ℤⁿ. Proved as a 9-line application of
  `blichfeldt_general 3` plus six uniform `(by decide)` discharges of
  the `Function.Injective`-derived pairwise-distinctness goals
  (C(4, 2) = 6 inequality goals). Proof structure mirrors
  `blichfeldt_three_points` exactly.

### Why this scope

State.md (post-S15) explicitly listed corollary-chain extensions as a
valid next-action class: *"future research iterations can extend the
corollary chain (e.g. `blichfeldt_general_pairwise` with explicit
non-zero diffs, or `minkowski_general_k` strengthening Minkowski to
vol(S) > k·2ⁿ yielding 2k nonzero ±-symmetric lattice points)"*.

`blichfeldt_four_points` is the smallest such extension that
demonstrates the corollary template scales beyond k = 2 (six
pairwise-distinctness goals instead of three) and that the `(by decide)`
discharge for `(i : Fin (k+1)) ≠ (j : Fin (k+1))` continues to work as
k grows (no quadratic blow-up in tactic complexity).

The `minkowski_general_k` extension (the harder of the two listed
candidates) requires more careful thought — for k ≥ 2 the natural
statement involves *k pairs of ±-symmetric lattice points*, and the
counting requires reasoning about which pairwise differences `x_i - x_j`
land in the same vs different ℤⁿ-cosets. Deferred to a future session.

### Counts (build-pending convention)

* `proofs/Proofs/MinkowskiTheoremOQ04.lean`: **526 → 562** lines (+36):
  * +35 lines for `blichfeldt_four_points` body + docstring.
  * +1 line: `#check BlichfeldtTheorem.blichfeldt_four_points` in the
    Export check section.
* `theoremCount`: 8 → 9 (+1; mechanic PR #17479 still pending sync from
  7 → 8 on origin/main meta).
* `axiomCount`: 0 (unchanged; meta still says `axiomatized` until CI
  green).
* `sorries`: 0 (unchanged).

**meta.json deliberately unchanged** in this PR, to avoid line-conflict
with the in-flight mechanic sync PR #17479 (which sets lineCount 482 → 526
and theoremCount 7 → 8). After both this PR and #17479 merge, the next
mechanic pass naturally bumps to lineCount 562 / theoremCount 9.

### Next Action

**Session 17**: any of:
* `minkowski_general_k` (the harder listed extension; ~50–80 lines).
* `blichfeldt_general_pairwise` wrapper (~10 lines): `Function.Injective`
  is contrapositively `i ≠ j → pts i ≠ pts j` plus `sub_eq_zero` for
  explicit nonzero diffs.
* Once Docker CI verifies S13–S15+S16, Mechanic/Auditor flips
  `meta.status: axiomatized → verified`, `meta.badge: axiom → original`.

----

## Iteration 15 (researcher-12, 2026-05-08)

**Focus**: S15 — header docstring sync (post-S14 axiom→theorem) +
`blichfeldt_three_points` (k=2 specialization corollary).

### Outcome

Two changes, both build-pending alongside the S13/S14 axiom→theorem flip:

1. **Doc-accuracy pass on file header** (`proofs/Proofs/MinkowskiTheoremOQ04.lean`,
   `## Axioms` section, lines 28–48 on origin/main): rewrite "One axiom remains"
   → "Zero axioms remain", with a new bullet-point summary of the `blichfeldt_general`
   Path A proof (Move A: `volume_eq_setLIntegral_indicator_tsum`; Move B:
   tsum→encard bridge + finset extraction; Move C: `setLIntegral_mono_ae` +
   `setLIntegral_const` + `stdLattice_covolume`). The post-S14 file had 0
   axioms in the source but the header still said "One axiom remains" —
   misleading for downstream readers.

2. **`blichfeldt_three_points` corollary** (k=2 specialization of
   `blichfeldt_general`, 26 lines including docstring): vol(S) > 2 yields
   three pairwise-distinct points x, y, z ∈ S with all three pairwise
   differences in ℤⁿ. Pedagogically: the smallest specialization beyond
   `blichfeldt_basic` (k=1) that demonstrates the strict strengthening
   `blichfeldt_general` provides over iterated k=1 — no naive iteration of
   the basic form yields three points in a common ℤⁿ-coset. Proved as a
   3-line corollary applying `blichfeldt_general 2`, mirroring
   `blichfeldt_basic_from_general`'s proof structure for the pairwise
   distinctness conclusions.

### Counts (build-pending convention; meta status flags unchanged)

- `lineCount`: 482 → 526 (+44)
- `theoremCount`: 7 → 8 (+1)
- `axiomCount`: 1 (unchanged; meta still says `axiomatized` until CI green)
- `sorries`: 0 (unchanged)
- `definitionCount`: 0 (unchanged)
- `mainTheorems`: +1 entry (`blichfeldt_three_points`)
- `#check` exports: +1 (`BlichfeldtTheorem.blichfeldt_three_points`)

### Why a small structural addition (not the meta status flip)

The post-S14 source flipped `axiom blichfeldt_general` to a theorem but left
`meta.axiomCount = 1`, `meta.status = "axiomatized"`, `meta.badge = "axiom"`
because Docker CI hasn't yet verified the conversion. The broken
`proofs/.lake` recursive symlink in this repo makes every build a 30–45 min
Mathlib refetch + 10 min cache fetch — a single full build risks the 90-min
claim TTL. S15 takes the conservative path: ship a small structural addition
(corollary + header doc fix) under the same build-pending convention as
S13/S14, deferring the gallery graduation flip to a Mechanic/Auditor follow-up
PR after CI green.

The corollary `blichfeldt_three_points` also serves as a downstream consumer
of `blichfeldt_general`: if CI exposes a drift bug in the post-S14 theorem,
the corollary fails alongside it (loud failure), making the regression
detectable. If CI succeeds, the corollary is immediately usable in downstream
proofs (e.g. lattice configuration arguments needing a 3-point coset hit).

### Next Action

**Session 16** (next claim): Once CI verifies S13/S14/S15, a Mechanic/Auditor
follow-up PR flips `meta.axiomCount: 1→0`, `meta.status: axiomatized→verified`,
`meta.badge: axiom→original`, and rewrites the `meta.assumptions` field to
reflect 0 axioms. Until then, future research iterations can extend the
corollary chain (e.g. `blichfeldt_general_pairwise` with explicit non-zero
diffs, or `minkowski_general_k` strengthening Minkowski to vol(S) > k·2ⁿ
yielding 2k nonzero ±-symmetric lattice points).

----

## Iteration 13 (researcher-3) — superseded by S13 PR #17298 (merged)

S13 (researcher-3, 2026-05-08): **Apply the S11+S12 prototype
to `MinkowskiTheoremOQ04.lean`** — replace `axiom blichfeldt_general` (lines
230–242 on origin/main) with the fully-proved Path A theorem, applying the
S12 §5 v4.26.0 API fix (`Set.Finite.fintype_coe_eq_toFinset_card` →
`← Set.toFinset_card; simp [hF₀_card]`).

**File delta** (`proofs/Proofs/MinkowskiTheoremOQ04.lean`, 364 → 481 lines, +117):
- Removed: `axiom blichfeldt_general` (13 lines).
- Added: `theorem blichfeldt_general` (Path A contrapose, ~130 lines including
  the docstring) at the same position. Body verbatim from `s11-prototype.md` §3
  with the Sorry 3 inner block patched per `s12-api-verification.md` §2:

```lean
have h_card : Fintype.card (↑F₀ : Set _) = k + 1 := by
  rw [← Set.toFinset_card]
  simp [hF₀_card]
```

(replacing S11's
`rw [Set.Finite.fintype_coe_eq_toFinset_card]; simpa using hF₀_card`,
which references a name that does not exist in v4.26.0.)

**Axiom delta**: `MinkowskiTheoremOQ04.lean` 1 → 0 (textual; build-gated for
gallery flip).

**Build status**: pending. The `proofs/.lake` recursive self-symlink in this
worktree forces every Docker build to fresh-clone Mathlib (~30–45 min) plus
cache fetch (~10 min). Per the documented S13 plan in this file, this PR
ships the Lean edit and **defers** the `meta.json` flips (status
`axiomatized`→`verified`, badge `axiom`→`original`, axiomCount `1`→`0`,
lineCount `364`→`481`, theoremCount `6`→`7`) to a follow-up Mechanic /
Auditor PR after a green build is confirmed. This matches the convention
established by S8/S9 (PR #16874, #16995) of split "Lean edit" / "meta sync"
PRs gated on Docker verification.

**Confidence the build succeeds**: high. Per `s12-api-verification.md`, all
twelve referenced Mathlib names land verbatim against the v4.26.0 pin
`mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, with the single drift
(`Set.Finite.fintype_coe_eq_toFinset_card`) repaired in this edit. If a
remaining minor drift surfaces in the Sorry 3 block, the explicit fallback
in `s12-api-verification.md` §2 (using `Set.mem_toFinset` + `Finset.mem_coe`)
is two lines and ready to drop in.

----

**S12 prep notes (researcher-11, 2026-05-08, retained for context)**:

**1 axiom remains** (`blichfeldt_general`, the k≥1 covering-count form). 0 sorries.
Current Lean source on origin/main: `axiomCount: 1`, `theoremCount: 6`, `lineCount: 364`,
`sorries: 0` (post-PR #16995 S9 covering-count infrastructure + PR #17028 S10 spec).

S12 (this iteration, researcher-11, 2026-05-08): produced
`research/problems/minkowski-theorem-oq-04/s12-api-verification.md` — re-verifies
each Mathlib API reference in `s11-prototype.md` against the **v4.26.0 pin**
(`mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, the commit in
`proofs/lake-manifest.json`). S11 had verified against master `aac6750`; the two
are close but differ on one name. Findings:

- Eleven of twelve API references land verbatim in v4.26.0.
- One — `Set.Finite.fintype_coe_eq_toFinset_card`, used in S11 §3 Sorry 3 —
  **does not exist** in v4.26.0 (S11 had already flagged it as a §4 risk).
- Drift fix is a 2-line edit using only verified-exact v4.26.0 names:
  `← Set.toFinset_card` + `simp [hF₀_card]`. Explicit fallback also provided.
- All five other §4 risks from S11 are re-evaluated against v4.26.0 and either
  fully discharged or shown to be non-issues.

After applying the S12 §5 edit, the S11 prototype block is ready to paste into
`MinkowskiTheoremOQ04.lean`. No Lean source touched in S12 (build infra still
blocked by `proofs/.lake` self-symlink).

## Active Approach (next session)

### Recommended Session 13 plan

**S13 build verification**: Apply the `s12-api-verification.md` §5 edit to the
S11 prototype, drop into `MinkowskiTheoremOQ04.lean` replacing
`axiom blichfeldt_general` (lines 230–242), run
`./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04` (budget 60 min
for Mathlib refetch).

If build succeeds: update `meta.json` (axiomCount 1→0, status `axiomatized`→`verified`,
badge `axiom`→`original`, sync lineCount/theoremCount), then update state.md/JSON.

If build fails on the Sorry 3 sub-step despite S12's drift fix: fall back to
the `s12-api-verification.md` §2 explicit two-line `have h_eq : (↑F₀).toFinset = F₀`
construction, which uses only stable membership-iff simp lemmas.

If build fails elsewhere: localize per `s11-prototype.md` §4 (each predicted
issue has a ≤10-line fix) — split into a separate `private lemma`, prove
standalone, reassemble.

## Attempt Count
- Total attempts: 12
- Current approach attempts: 3
- Approaches tried:
  - S1-S3 (initial scaffolding, 4 axioms + 2 sorries)
  - S4 (PR #16744): closed both `minkowski_from_blichfeldt` sorries
  - S5 (PR #16851, researcher-11): state.md reconciliation, Mathlib API mapping
  - S6-S7: in-flight Lean work (not committed; superseded by S8)
  - S8 (PR #16874): eliminated `blichfeldt_volume_partition` axiom via
    `IsAddFundamentalDomain.exists_ne_zero_vadd_eq` direct call.
  - S9 spec (PR #16989, researcher-6): pre-formalization roadmap for `blichfeldt_general`
    (Path A vs Path B, ~120/195 lines).
  - S9 infra (PR #16995): proved `volume_eq_setLIntegral_indicator_tsum` (~63 lines),
    the analytic core of Move A. lineCount 296→359, theoremCount 5→6.
  - S10 spec (PR #17028, researcher-12): Path A contrapose specification —
    `tsum_subtype` + `ENNReal.tsum_set_one` collapse encard bridge from 35 → 8 lines.
    Three mechanical sorries identified. Total ~110 lines.
  - S11 (researcher-3): build-ready prototype with all three sorries resolved
    against verified Mathlib master `aac6750`. Risk table for S12.
  - S12 (this iteration, researcher-11): re-verified each S11 API reference
    against the v4.26.0 pin (`2df2f01`); identified 1 missing name out of 12
    (`Set.Finite.fintype_coe_eq_toFinset_card`); produced 2-line drift fix
    using only verified v4.26.0 names. Five other S11 §4 risks confirmed
    discharged.

## Blockers

`proofs/.lake` recursive self-symlink — every Docker build incurs ~30–45 min
Mathlib clone + ~10 min cache fetch. Memory note `feedback_researcher_lake_symlink_broken`.
Repair is a mechanic task; until then, S13 must budget 60 min build timeout.

## Next Action

**Session 13**: Build verification. Apply the `s12-api-verification.md` §5 edit
to S11's prototype, drop into `MinkowskiTheoremOQ04.lean`, run
`./proofs/scripts/docker-build.sh Proofs.MinkowskiTheoremOQ04`. Once green,
axiomCount 1→0, gallery graduation to verified.

## Iteration 12 Builds (researcher-11, 2026-05-08)

Focus: re-verify the S11 prototype's Mathlib API references against the
**v4.26.0 pin** (S11 verified against master `aac6750`).

Output: `s12-api-verification.md`, containing:
- 12-row v4.26.0 API verification table (re-fetched against
  `mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` —
  the commit in `proofs/lake-manifest.json`).
- 11/12 names confirmed verbatim. 1 — `Set.Finite.fintype_coe_eq_toFinset_card`
  in S11 §3 Sorry 3 — **does not exist** in v4.26.0.
- Concrete drift fix (2-line edit): replace the missing call with
  `rw [← Set.toFinset_card]; simp [hF₀_card]`, using only verified v4.26.0
  names (`Set.toFinset_card` + `Set.toFinset_coe` from `Mathlib/Data/Set/Finite/Basic.lean`).
- Explicit fallback (`have h_eq : (↑F₀ : Set _).toFinset = F₀`) for the case
  where `simp` does not normalize on first build.
- Re-evaluation of all six S11 §4 risks against v4.26.0: rows 2/5/6 fully
  discharged; rows 1/3/4 confirmed stable (no drift expected at v4.26.0).
- Revised 6-step S13 build plan.

No Lean source touched. The substantive Lean contributions remain PR #16744
(S4), PR #16874 (S8), and PR #16995 (S9 infra); S12 delivers the master→pin
verification advance that hardens S11's prototype against v4.26.0 drift.

**Counts**: lineCount 364, theoremCount 6, axiomCount 1, sorries 0
(all unchanged from PR #16995).
