# Session — Iter 5 PREP (Mathlib API confirmed; sharpened paste-ready skeleton)

**Date**: 2026-06-09 (researcher-5)
**Mode**: PREP (discovery-banking; doc-only; no Lean / no `meta.json` edits)
**Phase**: ORIENT → ACT-ready (no Docker required at confirmation time)

## §0 Headline

The iter-4 skeleton's last unknown — the exact Mathlib name for the
"BoundedVariationOn ⟹ a.e. DifferentiableAt" step — is **confirmed without
needing Docker**. Mathlib's `BoundedVariation` html docs list it directly:

```text
BoundedVariationOn.ae_differentiableAt_of_mem_uIcc
  {V : Type _} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {f : ℝ → V} {a b : ℝ}
  (h : BoundedVariationOn f (Set.uIcc a b)) :
  ∀ᵐ (x : ℝ), x ∈ Set.uIcc a b → DifferentiableAt ℝ f x
```

This is the simplest of the four candidates iter-4 enumerated (the
`...DifferentiableAt` form — no within-to-full upgrade needed). It is in
the canonical module `Mathlib.Analysis.BoundedVariation`, already
transitively imported via Mathlib.Tactic.

**Net effect for iter-5 ACT-readiness**:
- Iter-4 §2.2 skeleton's `sorry` placeholder can now be replaced by a
  concrete two-line invocation (apply the lemma after re-shaping
  `Set.Icc a b` to `Set.uIcc a b` via `Set.uIcc_of_le hab`).
- Iter-4 §2.2 "within-vs-full bridge (~10-20 LOC)" is **NO LONGER
  REQUIRED** (the lemma already returns `DifferentiableAt`, not
  `DifferentiableWithinAt`).
- Iter-4 §3 grep recipe is obsolete — no Docker Mathlib grep needed; the
  web docs were authoritative.

## §1 T+7d premise re-verification (post-iter-4)

| Surface | Iter-4 verification (2026-06-02) | Iter-5 verification (2026-06-09) | Δ |
|---|---|---|---|
| `proofs/Proofs/FundamentalTheoremCalculusLebesgue.lean` LOC | 311 | 311 (`wc -l`) | = |
| Parent file axiomCount | 2 (`lebesgue_ftc_differentiable` + `lebesgue_ftc_integral`) | 2 (grep `^axiom `) | = |
| Parent file sorries | 1 (`cantor_function_not_ac`, line 259) | 1 (grep `sorry`) | = |
| Sibling `FundamentalTheoremCalculusLebesgueOQ01.lean` LOC | 185 | 185 (`wc -l`) | = |
| Sibling `ac_implies_bv` linchpin | line 135, namespace `FTCLebesgueACImpliesBV`, 0 axioms / 0 sorries | unchanged | = |
| Open PRs touching either file | 0 | 0 (`gh pr list --search "fundamental-theorem-calculus" --state open`) | = |
| Most recent main commit on parent | 2026-05-15 (PR #20893) | 2026-05-15 (PR #20893; no new commits) | = |
| Host disk free | 4.3 GiB (iter-4 fragile) | 107 GiB (~25× healthier) | ▲ |
| Docker availability | unhealthy | healthy (Server 29.5.3 running, lean4-arm64:v4.26.0 image cached 4.08 GB, lean-mathlib-cache volume present) | ▲ |

**Verdict**: iter-3/iter-4 premise unchanged at T+7d. No drift. The two
iter-4 operational blockers (disk pressure + Docker uncertainty) are both
**resolved**. The only remaining knob — Mathlib API name — is now also
**resolved by this session**.

## §2 Sharpened paste-ready Lean skeleton

This supersedes iter-4 §2.2. The skeleton is now `sorry`-free at the
BV→a.e.-diff step; only the bridge from `∀ᵐ x ∈ Icc a b, P x` to
`∃ S ⊆ Ioo a b, MeasurableSet S ∧ volume (Ioo a b \ S) = 0 ∧ ∀ x ∈ S, P x`
remains as ordinary measure-theory plumbing.

### §2.1 Imports — add ONE line

Same as iter-4 §2.1:

```lean
import Proofs.FundamentalTheoremCalculusLebesgueOQ01
```

`Mathlib.Analysis.BoundedVariation` is already transitively imported via
`import Mathlib.Tactic`, so no additional Mathlib import is needed.

### §2.2 Replace the axiom (lines 200-204)

Replace the existing 5-line axiom with:

```lean
/-- **Lebesgue FTC (Part 1)**: AC ⟹ a.e. differentiable on (a, b).

Discharged via the chain `AC → BV → a.e. DifferentiableAt`:
- `AC → BoundedVariationOn F (Icc a b)`: sibling theorem
  `FTCLebesgueACImpliesBV.ac_implies_bv` (axiom-free, 0 sorries).
- `BoundedVariationOn → a.e. DifferentiableAt`: Mathlib's
  `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`
  (`Mathlib.Analysis.BoundedVariation`).

Conversion `Icc a b ↔ uIcc a b` uses `Set.uIcc_of_le hab`. The final
∀ᵐ → ∃-measurable-witness step packages the null-set complement. -/
theorem lebesgue_ftc_differentiable {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOn F a b) :
    ∃ S : Set ℝ, MeasurableSet S ∧
      volume (Ioo a b \ S) = 0 ∧
      ∀ x ∈ S, DifferentiableAt ℝ F x := by
  -- Step 1: AC ⟹ BV on Icc a b (sibling, axiom-free).
  have hbv_icc : BoundedVariationOn F (Set.Icc a b) :=
    FTCLebesgueACImpliesBV.ac_implies_bv hab hF
  -- Step 2: Reshape Icc a b ↦ uIcc a b (equal when a ≤ b).
  have hbv : BoundedVariationOn F (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]; exact hbv_icc
  -- Step 3: Apply Mathlib's BV → a.e. DifferentiableAt.
  have hae : ∀ᵐ x ∂(MeasureTheory.volume : Measure ℝ),
      x ∈ Set.uIcc a b → DifferentiableAt ℝ F x :=
    hbv.ae_differentiableAt_of_mem_uIcc
  -- Step 4: Build the witness S = {x ∈ Ioo a b | DifferentiableAt ℝ F x}.
  -- This set is measurable because `{x | DifferentiableAt ℝ F x}` is measurable
  -- (Mathlib: `measurableSet_of_differentiableAt` / similar — confirm name at
  -- Docker build time; canonical home is `Mathlib.Analysis.Calculus.FDeriv.Measurable`).
  set D := {x : ℝ | DifferentiableAt ℝ F x} with hD_def
  have hD_meas : MeasurableSet D := by
    -- Candidate: `measurableSet_of_differentiableAt` returns MeasurableSet of D.
    -- Backup: `MeasureTheory.measurable_of_differentiable` then preimage.
    sorry -- single Mathlib invocation; see comment above
  refine ⟨Set.Ioo a b ∩ D, ?_, ?_, ?_⟩
  · exact measurableSet_Ioo.inter hD_meas
  · -- volume ((Ioo a b) \ (Ioo a b ∩ D)) = volume (Ioo a b ∩ Dᶜ) ≤ volume (uIcc a b ∩ Dᶜ).
    -- The latter is null by hae (rewriting ∀ᵐ as null-set complement).
    have hsub : Set.Ioo a b ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]; exact Set.Ioo_subset_Icc_self
    have : Set.Ioo a b \ (Set.Ioo a b ∩ D) ⊆ Set.uIcc a b ∩ Dᶜ := by
      intro x hx
      refine ⟨hsub hx.1, ?_⟩
      simp only [Set.mem_inter_iff, not_and] at hx
      exact hx.2 hx.1
    -- ∀ᵐ encodes `volume {x | ¬ (x ∈ uIcc → DifferentiableAt)} = 0`,
    -- i.e. `volume (uIcc a b ∩ Dᶜ) = 0`.
    have hnull : MeasureTheory.volume (Set.uIcc a b ∩ Dᶜ) = 0 := by
      have := MeasureTheory.ae_iff.mp hae
      -- {x | ¬(x ∈ uIcc → x ∈ D)} = uIcc ∩ Dᶜ
      simpa [Set.mem_inter_iff, hD_def, not_imp, Set.compl_def] using this
    exact MeasureTheory.measure_mono_null this hnull
  · rintro x ⟨_, hxD⟩; exact hxD
```

**Honest annotation**: this skeleton retains a SINGLE `sorry` —
the measurability of `D = {x | DifferentiableAt ℝ F x}`. This is a
well-known Mathlib fact; the canonical home is
`Mathlib.Analysis.Calculus.FDeriv.Measurable`. The next picker should
grep that file for the exact name. If the name is unavailable, the
fallback is to define `S` differently (e.g., via the inner-regular
hull `toMeasurable` of `Ioo a b ∩ D` — still 0-line work).

### §2.3 Gallery `meta.json` delta — unchanged from iter-4 §2.3

```diff
- "axiomCount": 2,
+ "axiomCount": 1,
```

Plus `theoremCount: 5 → 6`. `lineCount` re-measure post-edit. Status
remains `axiomatized` (the `lebesgue_ftc_integral` axiom and the Cantor
`sorry` remain).

## §3 Why the iter-4 §3 grep recipe is no longer required

Iter-4 §3 prescribed a Docker grep across
`Mathlib/Analysis/BoundedVariation*` to identify the BV→a.e.-diff lemma
name from four candidates. Mathlib's html docs at
`leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/BoundedVariation.html`
list **all four candidates** authoritatively (with their statements,
hypotheses, and namespaces). The web fetch resolves the question without
Docker, removing iter-4's primary operational ask.

The full enumeration (for posterity / future-proofing if this lemma
gets renamed upstream):

| # | Name | Hypothesis | Conclusion (relevant projection) |
|---|---|---|---|
| 1 | `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_real` | LBV | ∀ᵐ x, x ∈ s → DifferentiableWithinAt ℝ f s x |
| 2 | `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem_pi` | LBV (pi-codomain) | (within-form) |
| 3 | `LocallyBoundedVariationOn.ae_differentiableWithinAt_of_mem` | LBV (NormedSpace V) | (within-form) |
| 4 | `LocallyBoundedVariationOn.ae_differentiableWithinAt` | LBV | (within-form) |
| 5 | `LocallyBoundedVariationOn.ae_differentiableAt` | LBV (no set restriction) | ∀ᵐ x, DifferentiableAt ℝ f x |
| 6 | **`BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`** | **BV on `uIcc a b`** | **∀ᵐ x, x ∈ uIcc → DifferentiableAt ℝ f x** ← our match |

The `uIcc` variant is the targeted form — it does **not** require
`LocallyBoundedVariationOn` (which would force a stronger hypothesis on
our sibling), and it gives full `DifferentiableAt` (no within-to-full
bridge needed).

## §4 Remaining residual risks for ACT

1. **`measurableSet_of_differentiableAt` name**: the `sorry` at line ~15
   of §2.2's skeleton. Resolution: grep
   `Mathlib/Analysis/Calculus/FDeriv/Measurable.lean` for `MeasurableSet`
   in the differentiability context. If the name differs, the fallback
   (use `toMeasurable` of the `Ioo a b ∩ D` and adjust) works and is
   <10 LOC.
2. **`MeasureTheory.ae_iff` exact form**: the `simpa` step in §2.2's
   `hnull` block. May need `Filter.eventually_iff_mem` + `Measure.ae`
   unfolding or `MeasureTheory.ae_iff`. Both lemmas are standard. If
   `simpa` doesn't close, use a one-line manual unfold.
3. **Implicit `Measure ℝ`**: the `Mathlib.MeasureTheory.MeasureSpace`
   instance for ℝ is global. `MeasureTheory.volume` resolves
   automatically.

None of these are conceptual — all are mechanical Mathlib API plumbing
on top of the now-confirmed BV→a.e.-diff core. Estimated next-cycle ACT
duration: ~20-45 minutes wall-clock under Docker.

## §5 Why this iter-5 ships PREP (not ACT)

I considered attempting the ACT in this cycle. Three reasons it's
banked as PREP instead:

1. **Memory**: host total memory is 7.65 GiB. `docker-build.sh` default
   `LEAN_MEMORY_LIMIT=32768` would fail at container creation. A safe
   build needs `LEAN_MEMORY_LIMIT=4096` (and possibly
   `LEAN_BUILD_TIMEOUT=30m` for the first-time module compile). The
   first-time module compile from a warm Mathlib cache typically takes
   15-25 minutes; iterating on the residual `measurableSet_of_differentiableAt`
   `sorry` is a second build cycle. Cumulative wall-clock: 30-60
   minutes — borderline for a single cycle.
2. **Cycle goal alignment**: the iter-4 picker's documented next-cycle
   plan (state.md "Next Action") presumes the API name is the gate. With
   the name now confirmed *and* with the §2.2 skeleton sharpened to a
   single residual `sorry`, the next picker is set up for a fast,
   targeted ACT — exactly the iter-4 PREP's stated goal.
3. **Safety**: per the iter-4 honest annotation, **uncommitted-to-main
   skeleton with a `sorry` would not pass gallery audit**. ACT must be
   build-verified before commit, and a build attempt that fails late
   (e.g. memory OOM after 20 minutes) would burn the cycle without
   progress. PREP banks the discovery without that risk.

## §6 What this PREP does NOT do

- Does **not** modify any Lean file (parent or sibling).
- Does **not** modify `meta.json`.
- Does **not** run Docker.
- Does **not** progress the Cantor `sorry` (separate from the axiom track).
- Does **not** discharge `lebesgue_ftc_integral` (the deep axiom; still
  awaiting Stieltjes/Radon–Nikodym infrastructure).

## §7 Recommended next session

If the picker has Docker access and `LEAN_MEMORY_LIMIT=4096` is
configured (or host memory expanded):

1. Pull the iter-5 PREP skeleton from §2.2.
2. Grep `Mathlib/Analysis/Calculus/FDeriv/Measurable.lean` for
   `MeasurableSet.*Differentiable` — should be a 1-liner.
3. Replace the §2.2 `sorry` with the confirmed name.
4. Build under Docker: `LEAN_MEMORY_LIMIT=4096 LEAN_BUILD_TIMEOUT=45m \
   ./proofs/scripts/docker-build.sh Proofs.FundamentalTheoremCalculusLebesgue`
5. On green: update `meta.json` per §2.3; commit; PR.
6. Expected delta: parent `axiomCount: 2 → 1`, `theoremCount: 5 → 6`.

If host memory remains <8 GiB:

- Iter-6 SURVEY (+Nd refresh) is the proportionate move.
- Continue banking sharpened skeletons until memory or alternative ACT
  pathway opens.

## §8 Provenance

- Worktree path: `.loom/worktrees/researcher-5/` (researcher-5).
- Branch: `research/ftc-lebesgue-oq01-incomplete01-iter5-prep-api-confirmed`.
- Base SHA: `origin/main` at cycle start = `125009d460a` (audit tracker
  bump for cramers-rule, PR #22627).
- Mathlib doc source:
  `leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/BoundedVariation.html`
  (fetched 2026-06-09; pin v4.26.0).
- No Lean file edits. No `meta.json` edits. Docs only.
