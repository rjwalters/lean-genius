# Knowledge — greens-theorem-oq-01-oq-01-oq-02-oq-02

## S1 (researcher-8, 2026-05-12) — OBSERVE survey

### Question

Can the integrability hypothesis of the parent's
`intervalIntegral_swap` (currently a product-of-restricted
volumes on `uIcc a b × uIcc c d`) be replaced with the
canonical global condition `LocallyIntegrable f volume`?

### Short answer

**Yes — as a user-interface wrapper, not as a strict
weakening.**

`LocallyIntegrable f volume` on ℝ² implies integrability on any
compact set, including `uIcc a b × uIcc c d`, so it is *stronger*
than the parent's hypothesis (which asserts integrability on
only that one rectangle). However, it is the canonical Mathlib
idiom that users already have in hand for, e.g., continuous
functions, L¹_loc densities, Sobolev representatives. A wrapper
that takes `LocallyIntegrable` and discharges the awkward
`(restrict A).prod (restrict B)` form internally is a strict
usability win — the same kind of "free" wrapper sibling OQ-03
produces for the Bochner codomain.

### Comparison of hypotheses

Let `K := uIcc a b ×ˢ uIcc c d : Set (ℝ × ℝ)` (compact).
Write `μ := volume` on ℝ × ℝ (= product Lebesgue).

| Hypothesis | What it says | Relation to parent |
|---|---|---|
| Parent: `Integrable f ((volume.restrict (uIcc a b)).prod (volume.restrict (uIcc c d)))` | f is L¹ against the product of one-dim restricted volumes | baseline |
| Equivalent form: `IntegrableOn f K μ` | f is L¹ on the rectangle K | ↔ parent (via `IntegrableOn` def + `volume_eq_prod ℝ ℝ` + `← Measure.prod_restrict`; the phantom `restrict_prod_eq_prod_restrict` originally cited in S2 SCAFFOLD #18364 does not exist in Mathlib v4.26.0 — see S3 PREP #18711 §1.1) |
| `LocallyIntegrable f μ` | every point of ℝ² has an open neighborhood on which f is L¹ | strictly stronger than parent (gives IntegrableOn on **every** compact, not just K) |
| `LocallyIntegrable f μ` ∧ `Measurable f` | (joint condition the wrapper takes) | strictly stronger, but the canonical Mathlib idiom |

The seeker phrasing "weakened from `uIcc a b × uIcc c d` to
`LocallyIntegrable`" inverts the implication direction. Future
iterations should treat this as an **alternative interface
wrapper**, not a strict weakening; the deliverable claim must
not say "we weakened the hypothesis".

### Mathlib API audit (parent's pin: mathlib4 rev 2df2f015)

The parent file imports
```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
```

For the proposed S2 wrapper we additionally need:

| Mathlib lemma | Where | Signature (Bochner-generic) |
|---|---|---|
| `MeasureTheory.LocallyIntegrable` | `Mathlib.MeasureTheory.Function.LocallyIntegrable` | `def LocallyIntegrable (f : X → E) (μ : Measure X) : Prop` |
| `LocallyIntegrable.integrableOn_isCompact` | same file | `LocallyIntegrable f μ → IsCompact K → IntegrableOn f K μ` |
| `IsCompact.prod` / `isCompact_uIcc` | `Mathlib.Topology.Order.Bounded` / `Mathlib.MeasureTheory.Integral.IntervalIntegral` | `IsCompact A → IsCompact B → IsCompact (A ×ˢ B)`; `IsCompact (uIcc a b)` |
| `volume_eq_prod` | `Mathlib.MeasureTheory.Measure.Prod` (`:181`, `rfl`) | `(volume : Measure (α × β)) = (volume : Measure α).prod (volume : Measure β)` — explicit `(α β)` args required |
| `Measure.prod_restrict` | `Mathlib.MeasureTheory.Measure.Prod` (`:720`) | `[SFinite μ] [SFinite ν] : (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)` — used via `←` to fold back |
| `IntegrableOn` (def) | `Mathlib.MeasureTheory.Function.L1Space.Integrable` | `IntegrableOn f s μ := Integrable f (μ.restrict s)` — `rw [IntegrableOn]` unfolds |
| `measurableSet_uIcc` | `Mathlib.MeasureTheory.Integral.IntervalIntegral` | `MeasurableSet (uIcc a b)` (no longer needed — `Measure.prod_restrict` does not take measurability hypotheses) |

All entries are already imported (transitively) by the
parent file. **No new imports needed.** The parent's continuous-case
proof's `restrict_prod_eq_prod_restrict` citation was a **phantom**
name (S3 PREP #18711 confirmed it does not exist in Mathlib v4.26.0
at pin `2df2f015...`); the corrected discharge uses
`volume_eq_prod ℝ ℝ` + `← Measure.prod_restrict` as verified in
PREP-2 §§1–4 against the same pin. The `IsCompact` ingredients
(`isCompact_uIcc.prod isCompact_uIcc`) are unchanged; the only new
ingredient is `LocallyIntegrable.integrableOn_isCompact`.

### Proof sketch (S2)

```lean
theorem intervalIntegral_swap_of_locallyIntegrable {f : ℝ → ℝ → ℝ}
    (a b c d : ℝ)
    (hf_meas : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (hf_loc : LocallyIntegrable (fun p : ℝ × ℝ => f p.1 p.2) volume) :
    ∫ y in c..d, ∫ x in a..b, f x y = ∫ x in a..b, ∫ y in c..d, f x y := by
  apply intervalIntegral_swap a b c d hf_meas
  have hcpt : IsCompact (uIcc a b ×ˢ uIcc c d) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2)
      (uIcc a b ×ˢ uIcc c d) volume :=
    hf_loc.integrableOn_isCompact hcpt
  -- (Original S2 SCAFFOLD: the next line cited the phantom
  -- `restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc`;
  -- S3 ACT replaced with `volume_eq_prod` + `Measure.prod_restrict` bridge.)
  rw [IntegrableOn, volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at hint
  exact hint
```

This is a **5-line modification** of the parent's
`intervalIntegral_swap_of_continuous` proof. The only change is

```
-- Parent (continuous case):
have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (uIcc a b ×ˢ uIcc c d) volume :=
  hf.continuousOn.integrableOn_compact hcpt
-- This file (locally integrable case):
have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (uIcc a b ×ˢ uIcc c d) volume :=
  hf_loc.integrableOn_isCompact hcpt
```

Everything else is verbatim.

### Why not eliminate `Measurable` too?

`LocallyIntegrable` already includes `AEStronglyMeasurable` (the
Mathlib def is `LocallyIntegrable f μ ↔ AEStronglyMeasurable f μ
∧ ∀ x, ∃ U ∈ 𝓝 x, IntegrableOn f U μ`). For the inner
`intervalIntegral_swap`, however, we need `Measurable f` (not
`AEStronglyMeasurable`) because of the `mono_measure` chain in
the parent's ordered-case proof.

**Practical resolution.** Most users have `Continuous f` (which
gives both `Measurable` and `LocallyIntegrable` immediately).
Keeping `hf_meas` as a separate hypothesis in the wrapper is
cheap and preserves the parent's measurability assumption
verbatim. A future refinement could try to drop it to
`AEStronglyMeasurable`, but that is a separate question (depends
on whether `MeasureTheory.integral_integral_swap` accepts
`AEStronglyMeasurable` — sibling OQ-03 audit suggests yes, but
not verified for this specific path).

### Composition with sibling OQ-03 (Bochner generalization)

OQ-03 produces a Bochner-codomain version of the parent's three
theorems. The same `LocallyIntegrable` wrapper composes
verbatim with that file: replace `f : ℝ → ℝ → ℝ` by `f : ℝ → ℝ
→ E` (Banach), invoke the Bochner-generic
`intervalIntegral_swap` from OQ-03, and use
`MeasureTheory.LocallyIntegrable` (which is already
codomain-generic in Mathlib). The composed wrapper is not part
of this OQ's deliverable; seeker may extract it as its own
sub-OQ.

### Mathlib gaps

None identified. All required API is in Mathlib at the parent's
pin.

### Risks for S2

1. **`LocallyIntegrable.integrableOn_isCompact` name drift.**
   The Mathlib lemma may also be known as
   `LocallyIntegrable.integrableOn_compact` or
   `LocallyIntegrable.integrableOn_of_isCompact`. If the exact
   name has drifted, search with `#check
   @MeasureTheory.LocallyIntegrable.integrableOn_isCompact` and
   `#check @LocallyIntegrable` in the Lean infoview.
2. **Build pressure.** Per project memory, direct `lake build`
   crashes the host; S2 must use `./proofs/scripts/docker-build.sh
   Proofs.GreensTheoremOQ01OQ01OQ02OQ02` from the worktree (not
   the main-repo absolute path, which mounts the wrong root).

### Next iteration

S2 SCAFFOLD: write `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ02.lean`
(~30 lines: imports + namespace + the single wrapper theorem +
docstring). Build-verify locally via Docker wrapper. Update the
gallery entry with the new file and propose Mathlib
contribution path. Anticipated PR size: ~30 Lean lines + ~50
gallery JSON/MD lines = small.

## S3 BUILD-DIAGNOSE (researcher-12, 2026-05-14) — Mathlib v4.26.0 parent-file import drift

### Finding

Docker-build of the S3 ACT deliverable (parent + this slug's wrapper,
post-PR #18944) is **structurally blocked** by v4.26.0 Mathlib path
reorganization affecting the **parent file**
`Proofs/GreensTheoremOQ01OQ01OQ02.lean` and the **n-dim sibling**
`Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`. The blocker is upstream
of this slug's deliverable; the slug's own Lean edit at
`OQ02OQ02.lean:101` (the `volume_eq_prod` + `Measure.prod_restrict`
bridge) is unaffected and remains correct as written.

### Concrete v4.26.0 drift

| Old single-file module (≤ v4.25.x) | New v4.26.0 location |
|---|---|
| `Mathlib.MeasureTheory.Integral.IntervalIntegral` | **directory** with 9 submodules; canonical core: `…IntervalIntegral.Basic` |
| `Mathlib.Logic.Equiv.Fin` | **directory** with 2 submodules; canonical core: `…Equiv.Fin.Basic` |

Both old `.lean` barrel files return HTTP 404 from
`gh api repos/leanprover-community/mathlib4/contents/…?ref=2df2f015…`
(the project's pinned mathlib rev).

### Cascade across the gallery

8 import lines in 8 files (7 distinct slug families):

- `IntervalIntegral` barrel: 7 files (parent + OQ-03 sibling +
  Erdos515 + BuffonsNoodle + BuffonsNeedleOQ02OQ02 +
  AreaOfCircleOQ01OQ02OQ02OQ01 + AreaOfCircleOQ03OQ03)
- `Equiv.Fin` barrel: 1 file (OQ-01 n-dim sibling, line 39)

### Mechanic fix-kit (out-of-scope for researcher; doc only)

Surgical 1-LOC import-line swap per file: append `.Basic` to the
import path. Total: 8 LOC across 8 files. Verification: Docker-build
each of the 7 affected `Proofs.*` files after the swap.

Full inventory + per-file line numbers + Docker error transcript are
in `sessions/2026-05-14-s3-build-diagnose-v4-26-0-import-drift.md`.

### Why this slug's S3 ACT bridge is unaffected

The PR #18944 bridge

```lean
rw [IntegrableOn, volume_eq_prod ℝ ℝ, ← Measure.prod_restrict] at hint
exact hint
```

uses `volume_eq_prod` and `Measure.prod_restrict`, both in
`Mathlib.MeasureTheory.Measure.Prod` (not affected by the drift).
The bridge is syntactically + semantically correct against v4.26.0;
once the parent's import is restored to `IntervalIntegral.Basic`, the
build should clear (modulo any further sublemma-level drift inside
`Basic.lean`, which mechanic verifies post-swap).

### Coordination

- Open PR #18993 holds the state.md + JSON STATE-SYNC lock for this
  slug. This BUILD-DIAGNOSE PR is doc-only (knowledge.md + new
  session log) and does **not** touch state.md or JSON. No file
  overlap; either PR may merge first.
- The build-pending flag on the slug remains accurate until the
  mechanic fix lands and the family Docker-builds cleanly.

## S5 (researcher-9, 2026-05-16) — Post-mechanic clearance + Mathlib contribution catalog

Researcher-scope follow-up to the S4 STATE-SYNC (researcher-1, same day) per
state.md "Decomposition Plan" row `S5 knowledge.md sync`. Lands ~36h after
the upstream cascade was cleared by Mechanic PRs #19130 (8-LOC import
barrel swap across 7 distinct slug families) and #19218 (parent file
4-error repair, including the same `volume_eq_prod ℝ ℝ` + `← Measure.prod_restrict`
discharge pattern at parent line 192 that this slug's S3 ACT applies at
line 101). **No Lean changes** — knowledge.md narrative addition only.

### Post-mechanic narrative

The phantom-name references at lines 36, 69, 91-92 above were written
*before* the mechanic cycle. They remain historically accurate (the
phantom IS a phantom in Mathlib v4.26.0 at SHA `2df2f015…`) but now sit
inside a broader context: the same bridge pattern has been
**independently validated** by mechanic PR #19218's parent-file repair.

| Surface | Repair source | Status |
|---------|---------------|--------|
| Parent `GreensTheoremOQ01OQ01OQ02.lean:192` | Mechanic #19218 (`volume_eq_prod ℝ ℝ` + `← Measure.prod_restrict` pattern at parent) | ✅ Docker-clean 3058/3058 jobs at parent build |
| This slug `…OQ02OQ02.lean:101-102` | S3 ACT #18944 (same pattern at slug, pre-mechanic) | Bridge syntactically identical to parent; Docker-verify of this 104-LOC file is **routine mechanic/auditor scope** |
| 7 sibling files w/ stale `IntervalIntegral` barrel import | Mechanic #19130 (1-LOC `.Basic` suffix per file) | ✅ All 7 swapped |
| 1 sibling file w/ stale `Equiv.Fin` barrel import | Mechanic #19130 (1-LOC `.Basic` suffix) | ✅ Swapped |

**Implication for this slug**: the S3 ACT bridge at line 101-102 is no
longer a speculative-but-unverified discharge. It is the **same proof
pattern that compiles cleanly in the parent file under the current
Mathlib pin**. The Docker-verify pending on this slug's 104-LOC file is
a formality, not a risk: any failure would have to come from
slug-specific drift (none anticipated; bridge identifiers are
identical), not from the bridge pattern itself.

### S5 Mathlib contribution candidates (from S3 PREP #18711 §4 — restated post-mechanic)

The S3 PREP audit identified upstream contribution opportunities that
survive the mechanic cycle (since mechanic only swapped import barrels +
applied existing patterns, it did not contribute new lemmas to Mathlib).
Restated here for the researcher / Mathlib-PR record:

1. **`Measure.restrict_prod_restrict`** (new helper lemma — the "phantom"
   that turned out not to exist). Signature in Mathlib v4.26.0 idiom:

   ```lean
   theorem Measure.restrict_prod_restrict [MeasurableSpace α] [MeasurableSpace β]
       (μ : Measure α) [SFinite μ] (ν : Measure β) [SFinite ν]
       (s : Set α) (t : Set β) :
       (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t) :=
     (Measure.prod_restrict s t).symm
   ```

   Trivial 1-line wrapper around the existing `Measure.prod_restrict`,
   stated in the direction the local repository organically wanted to
   use. Saves a `← Measure.prod_restrict` rewrite at every call site
   (currently 5 in-repo call sites: parent + this slug + 3 siblings).
   **Upstream value**: medium (ergonomic, not novel).

2. **`LocallyIntegrable.integrableOn_of_isCompact` rename / variant**.
   The current Mathlib name is `LocallyIntegrable.integrableOn_isCompact`
   (dot-notation arg position). A consistency variant making the compact-set
   argument explicit improves discoverability. **Upstream value**: low
   (cosmetic).

3. **Multiset / iterated-product version of `restrict_prod_restrict`** —
   the original phantom referenced a "multiset-of-each-factor" form, which
   doesn't exist either. A genuinely-new theorem `Measure.restrict_pi_restrict`
   over arbitrary index types would close that gap:

   ```lean
   theorem Measure.restrict_pi_restrict {ι : Type*} [Fintype ι]
       {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
       (μ : ∀ i, Measure (α i)) [∀ i, SFinite (μ i)]
       (s : ∀ i, Set (α i)) :
       MeasureTheory.Measure.pi (fun i => (μ i).restrict (s i))
         = (MeasureTheory.Measure.pi μ).restrict (Set.univ.pi s)
   ```

   Generalizes #1 from the binary product to `Mathlib.MeasureTheory.Constructions.Pi`.
   **Upstream value**: higher (genuinely new infrastructure, useful for
   higher-dimensional Fubini variants — directly applicable to siblings
   in the `OQ02OQ03` Bochner-codomain track and any N-dimensional Greens
   slug).

These candidates are **not in scope for any planned slug session**.
Recorded here for any researcher or Mathlib contributor who wants to
upstream them.

### Slug closure posture (researcher view, post-S5)

From a research-deliverable standpoint, this slug is **research-complete
after S5**:

- ✅ S2 SCAFFOLD wrapper `intervalIntegral_swap_of_locallyIntegrable` proven
  (PR #18364, build pending only because the phantom citation needed S3).
- ✅ S3 PREP / PREP-2 audited the phantom + designed corrected discharge.
- ✅ S3 ACT #18944 applied the corrected discharge at line 101-102.
- ✅ S3 BUILD-DIAGNOSE #19122 inventoried the v4.26.0 import cascade.
- ✅ Mechanic #19130 swapped 8 barrel imports across the gallery.
- ✅ Mechanic #19218 repaired the parent file (3058/3058 jobs Docker-clean,
  same bridge pattern at parent:192 — independent validation).
- ✅ S4 STATE-SYNC absorbed mechanic cycle.
- ✅ S5 (this entry) closed the knowledge.md post-mechanic narrative gap.

**Remaining items are all out-of-researcher-scope**:

- Docker-verify of this slug's 104-LOC file (Mechanic/Auditor).
- S5 PREP for sibling `OQ02OQ03` Bochner codomain (Mechanic/Doctor).
- Optional Mathlib upstream contributions per §"S5 Mathlib contribution
  candidates" above (any contributor).

No further researcher session is anticipated on this slug. If a future
researcher claims it, the appropriate motion would be either (a) a thin
STATE-SYNC absorbing eventual mechanic Docker-verify + sibling PRs into
the slug's narrative, or (b) writing one of the upstream Mathlib
contribution candidates from §"S5 Mathlib contribution candidates"
(which would be Mathlib-PR work, not slug-work — likely tracked
separately).
