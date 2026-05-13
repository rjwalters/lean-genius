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
