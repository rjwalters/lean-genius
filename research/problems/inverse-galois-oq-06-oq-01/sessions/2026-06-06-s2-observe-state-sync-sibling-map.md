# S2 OBSERVE — state.md sync + sibling-slug overlap map

**Date**: 2026-06-06T08:10:00Z
**Researcher**: researcher-1 (claim id researcher-61425)
**Mode**: OBSERVE (doc-only state.md ↔ JSON reconciliation + sibling overlap audit)
**Outcome**: progress — state.md synced with substantive JSON progress; sibling slug `inverse-galois-a5-oq-01` identified as duplicative; retarget recommendation.

## Why this iteration

Claim selected `inverse-galois-oq-06-oq-01`. On read:

* `state.md` is the **template-stub from creation** (2026-04-04, Iteration 1, OBSERVE,
  no attempts).
* `src/data/research/problems/inverse-galois-oq-06-oq-01.json` already carries a
  substantive feasibility survey (`currentState.focus` = "Feasibility survey complete.
  |Gal| ∈ {5,10,60}. Eliminate 5 and 20. Hard case D₅ requires Dedekind. Not in
  Mathlib 4.26.") with 7 detailed `knowledge.insights` entries and 4 listed
  `mathlibGaps`.
* A **local Lean file** `proofs/Proofs/InverseGaloisOQ06OQ01.lean` (255 LOC,
  13 theorems, 0 sorries, 0 axioms) already exists and is tracked in JSON
  `leanFiles[]`.

The state divergence is real: substantive prior work happened, but only landed in
JSON and the Lean file — never in `state.md`. This iteration reconciles.

## Pin re-confirmation

Mathlib pin SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since the
sibling slug's S4h, 2026-06-02). No bearer re-spot-check at this OBSERVE iteration.

## Local Lean file audit: `Proofs/InverseGaloisOQ06OQ01.lean`

**Inspected at git HEAD**. 255 LOC, 13 theorems, 0 sorries, 0 axioms. Structure:

| Section | Theorems | Role |
|---|---|---|
| §1 Root count in ℂ | `q_rootSet_ℂ_card` | `|rootSet q ℂ| = 5` |
| §2 Monotonicity / real roots | `q_deriv_pos`, `q_strictMono`, `q_has_real_root`, `q_rootSet_ℝ_card` | 1 real root (rules out `|Gal|=5`) |
| §3 Complex conjugation | `galConj_sq_eq_one`, `galConj_support_card`, `galConj_nontrivial`, `two_dvd_gal_card` | 2 ∣ \|Gal\| |
| §4 Case elimination | `gal_card_ne_5` | \|Gal\| ≠ 5 (the cleanest case) |
| §5 Mod-7 factorization | `q_ℤ_mod7_factorization`, `cubicMod7_no_roots` | mod-7 has irreducible cubic factor |
| §6 Summary | `three_dvd_gal_card_proved` | **NOT new**: re-uses `InverseGaloisA5.three_dvd_gal_card` axiom verbatim |

**Honesty caveat**: the §6 "summary" theorem is *not* an elimination of the parent
axiom — it just exports the same axiom under a different namespace. The supporting
infrastructure (§1–§5) is genuine, but the *bridge* from "mod-7 has irreducible
cubic factor" to "3 ∣ \|Gal\|" via the Frobenius construction is **not present in
this file**; it is delegated to the (axiomatized) parent.

## Sibling slug overlap: `inverse-galois-a5-oq-01`

`research/problems/inverse-galois-a5-oq-01/` is the sibling slug working on the
**same axiom-elimination target** (`three_dvd_gal_card` in `InverseGaloisA5.lean`).
Status (per `state.md` head, 2026-06-02):

* **Phase**: ORIENT (S4 ACT-readiness — sub-step (a) paste-ready)
* **Iteration**: 7 (S4h PREP)
* **Lean file**: `Proofs/InverseGaloisA5Dedekind.lean` (89 LOC, 1 substantive sorry
  `exists_gal_order_three`, the Frobenius-at-p=7 construction)
* **Mathlib bearer set**: 16 bearers across `RingTheory/Frobenius.lean`,
  `RingTheory/Invariant/Basic.lean`, `NumberTheory/RamificationInertia/Galois.lean`,
  pin-attested 7× over a 17-day window with zero drift.
* **Paste-ready sub-step (a)**: 32-LOC Lean block (typeclass plumbing) sitting
  in the S4h memo, awaiting Docker BUILD-VERIFY before insertion.

**Overlap**: the two slugs share the **same target axiom**. The sibling is the
**genuine A5-specific Frobenius construction track**; this slug's title and
problem.md frame the **general Dedekind theorem** (a Mathlib-upstream-prep
scope), but the local Lean file (`InverseGaloisOQ06OQ01.lean`) works on the
*A5-specific* mod-7 factorization and conjugation, i.e. the **same scope as
the sibling** but at a lower level of completion (no Frobenius construction).

## Three options for this slug going forward

### Option A: Subsume into sibling

Mark this slug `subsumed` and redirect future Dedekind/Frobenius work to
`inverse-galois-a5-oq-01`. The local Lean file remains useful supporting
infrastructure (root counts + mod-7 factorization) — it can stay in the repo
as part of the A5 axiom-elimination story, but this slug's research lifecycle
closes.

**Pro**: avoids two researchers racing on the same target. The sibling is
much closer to ACT.

**Con**: the local Lean file (255 LOC, §1–§5) does carry real Frobenius
infrastructure that the sibling's `InverseGaloisA5Dedekind.lean` does NOT
duplicate — closing this slug strands that infrastructure outside any active
research narrative.

### Option B: Retarget this slug to general Dedekind theorem upstream

Take the problem.md's stated target literally: formalize Dedekind's theorem
**in full generality** as a Mathlib upstream contribution, not the A5
specialization. This is the **300-500 LOC Mathlib gap** identified in JSON
`knowledge.mathlibGaps`:

* Frobenius element order = inertia degree (general number-field setting)
* `InertiaGroup` and `DecompositionGroup` API extension
* Dedekind theorem statement at the polynomial level

**Pro**: this is the genuine open research question. Mathlib gap is real;
upstream value is high.

**Con**: 300-500 LOC, multi-month, very high risk. Coordination with
Mathlib reviewers required ([[mathlib-contribution]] skill). Sibling slug
provides the A5-specific path while this slug stays general.

### Option C: Maintain status quo as a complementary track

Keep this slug active as the **A5-specific mod-7 / cubic infrastructure
slug**, with the sibling owning the Frobenius construction. Both slugs
land their respective work; deployer merges in order.

**Pro**: no closure churn; both researchers have a clear lane.

**Con**: the slug's stated mission (general Dedekind) does not match its
local Lean file's scope (A5-specific mod-7). Cross-slug semantics drift.

## Recommendation: Option B with explicit retarget

The slug's name (`inverse-galois-oq-06-oq-01`) and problem.md frame it as
the general Dedekind theorem, which is the genuinely open Mathlib gap. The
local Lean file's §1–§5 (root counts, conjugation, mod-7 factorization) is
A5-specific *evidence* that motivates the general theorem; it can stay as a
supporting case study while this slug's main research target shifts to:

> **Retargeted goal**: formalize Dedekind's theorem at the polynomial level
> (statement: `∀ f : ℤ[X] irreducible, p prime, factorization mod p ⇒ Gal(f)
> contains permutation with the corresponding cycle type`) as a candidate
> Mathlib upstream contribution. The A5-specific evidence (`q ≡
> (X-5)(X-6)(cubic) mod 7`) becomes a unit test for the general theorem.

S3 ORIENT would then:
1. Survey Mathlib's `NumberField.RamificationIdx`, `Ideal.inertiaDeg`,
   `arithFrobAt R G Q` API and identify the precise statement that's
   missing.
2. Map the bearer chain to the sibling's S4h 16-bearer set (large overlap).
3. Estimate scope: ~300-500 LOC upstream split-PR, comparable to
   `mathlib4#7967` (Sperner upstream).

Anti-recommendation: do NOT spawn a separate parallel Frobenius-construction
track on this slug — the sibling already owns that with 7 iterations of
PREP. Race conditions waste Docker cycles.

## Next Action (S3 ORIENT or S2-bis)

**Preferred** (S2-bis, doc-only): write a problem.md/JSON retargeting
amendment explicitly framing the slug as the general Dedekind theorem
upstream track, with a `subsumes` / `subsumedBy` link to the sibling
slug for the A5-specific track. Defer to the deployer / champion for
authoritative pool-status reconciliation.

**Alternative** (S3 ORIENT): pivot to Option C (maintain status quo);
extend the local Lean file to cover `gal_card_ne_20` (the trivial
elimination per JSON insights — "~40 lines, A₅ simple → no order-20
subgroup"). Bounded scope, immediate ACT-shippable.

**Conservative**: pause this slug at S2 OBSERVE-substantive (this
memo) until a human / deployer / champion picks Option A/B/C. State.md
sync is the value delivered this iteration.

## Files modified by this iteration

* `research/problems/inverse-galois-oq-06-oq-01/sessions/2026-06-06-s2-observe-state-sync-sibling-map.md` — NEW (this memo, ~140 LOC, 9 sections).
* `research/problems/inverse-galois-oq-06-oq-01/state.md` — replace template stub with substantive S2 OBSERVE head + iter-2 entry.
* `src/data/research/problems/inverse-galois-oq-06-oq-01.json` — `currentState.{phase OBSERVE→OBSERVE-substantive (kept as ORIENT for JSON consistency with existing focus), iteration 1→2, focus, nextAction}` + `lastUpdate`.

## Anti-scope (S2 OBSERVE)

* No Lean diff. The local `InverseGaloisOQ06OQ01.lean` is untouched.
* No `meta.json` edit on the parent `inverse-galois-oq-06` gallery entry.
* No bearer audit (sibling has 7× attestations at the same Mathlib pin).
* No retargeting commitment — Options A/B/C are presented; pick deferred.
* No coordination edit on sibling slug `inverse-galois-a5-oq-01`.

## Build risk

Zero (doc-only).

## Memory pattern

S2 OBSERVE for a slug with **state.md ↔ JSON drift**: reconcile the
two before doing new research. The JSON had substantive prior work
(feasibility survey, insights, mathlibGaps) that never made it to
state.md. Future researchers claiming this slug should always read
*both* the state.md and the JSON `knowledge.*` block. When they
diverge, the JSON is usually more recent (it's auto-touched by
gallery sync; state.md is human-curated).

Cross-slug overlap audit at S2 OBSERVE: when a slug's title overlaps
with a sibling, *check the sibling's state before committing scope*.
The sibling `inverse-galois-a5-oq-01` has 7 PREP iterations on the
same target axiom — researching this slug without that knowledge
would have raced the sibling's S4 ACT.
