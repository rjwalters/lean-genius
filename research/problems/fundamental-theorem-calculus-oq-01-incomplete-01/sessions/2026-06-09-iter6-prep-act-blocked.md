# Session — Iter 6 PREP (ACT attempted; blocked by pre-existing sibling breakage)

**Date**: 2026-06-09 (researcher-11)
**Mode**: ACT → reverted to PREP (Docker verification banked critical negative results)
**Phase**: ORIENT → ACT attempted → blocked → discoveries banked

## §0 Headline

Iter-6 attempted the iter-5 PREP-banked ACT plan under Docker. The
attempt surfaced **three pre-existing issues** that block the plan and
that all prior PREP cycles missed:

1. **Iter-5's plan has a circular import.** The plan called for adding
   `import Proofs.FundamentalTheoremCalculusLebesgueOQ01` to the parent
   file, but the sibling **already imports the parent**. Adding the
   reverse import would have failed at build time.
2. **The sibling file does not build against current Mathlib.** A clean
   `git checkout`-of-HEAD Docker build (no edits) fails immediately at
   line 23 (`invalid 'import' command, it must be used in the beginning
   of the file`) because the file has a `/-! ... -/` module docstring
   **before** the imports — a known Lean v4.26.0 parser incompatibility
   (CLAUDE.md flags it). After moving imports above the docstring, the
   build progresses to deeper, pre-existing errors in `ac_implies_bv`:
   * `eVariationOn.eq_zero_iff.mpr` — unknown constant (renamed?)
   * `div_lt_iff` — unknown identifier (renamed to `div_lt_iff₀`?)
   * `ENNReal.natCast_ne_top` used unapplied — needs `(n := n)` or `_`
   * `linarith failed` cascade from the above
3. **The axiom `lebesgue_ftc_differentiable` is orphaned in code.**
   `grep -rn 'lebesgue_ftc_differentiable'` finds *only the axiom
   declaration itself* — zero downstream callers. Iter-4/iter-5 PREP
   plans both assumed it had to be replaced in place; the simpler move
   is just to delete it (post-discharge), since no code breaks.

**Net effect for iter-6**: ACT is gated on **sibling-file repair**, not
on the discharge proof itself. The iter-5 PREP skeleton (now refined to
a working candidate in §3 below) is build-ready *modulo* the sibling
being repaired first.

## §1 Operational state (verified at cycle start)

| Surface | Iter-5 claim | Iter-6 verified | Δ |
|---|---|---|---|
| Host total memory | 7.65 GiB | **95.99 GiB** (`sysctl hw.memsize` = 103079215104) | corrected |
| Memory blocker | yes (need `LEAN_MEMORY_LIMIT=4096`) | **none** (default 32 GiB fits) | corrected |
| Host disk free | 107 GiB | 103 GiB | ~ |
| Docker availability | healthy | healthy (Server 29.5.3, lean4-arm64:v4.26.0 cached 4.08 GB) | = |
| Mathlib cache volume | present | present | = |
| Parent file LOC | 311 | 311 (`wc -l`) | = |
| Parent axiomCount | 2 | 2 (grep `^axiom `) | = |
| Parent sorries | 1 | 1 (grep `sorry` line 259, Cantor) | = |
| Sibling file LOC | 185 | 185 | = |
| Sibling `ac_implies_bv` | "verified, 0 axioms / 0 sorries" | **fails Docker build at HEAD** | **NEGATIVE** |

Iter-5's host-memory reading was almost certainly captured from inside
a Docker container (which sees only its memory limit) and misattributed
to the host. The real host has 96 GiB; the LEAN_MEMORY_LIMIT default of
32 GiB is comfortable.

## §2 Iter-5 plan: what went wrong

Iter-5 PREP banked a "paste-ready skeleton" of the form:

```lean
-- in proofs/Proofs/FundamentalTheoremCalculusLebesgue.lean (parent):
import Proofs.FundamentalTheoremCalculusLebesgueOQ01   -- ← THE BUG
...
theorem lebesgue_ftc_differentiable ... := by
  have hbv_icc := FTCLebesgueACImpliesBV.ac_implies_bv hab hF
  ...
```

But:

```bash
$ grep '^import' proofs/Proofs/FundamentalTheoremCalculusLebesgueOQ01.lean
import Proofs.FundamentalTheoremCalculusLebesgue        # ← sibling imports parent
```

The sibling already imports the parent. Adding the reverse creates a
**circular import**, which Lake rejects before any Lean elaboration
runs. The plan would not have built.

The fix is structurally obvious in hindsight: the discharge proof should
live in the *sibling* (which has access to both the parent's
`AbsolutelyContinuousOn` and its own `ac_implies_bv`), not in the
parent. With the orphan-axiom finding (§3), this becomes:

* Delete the parent's `axiom lebesgue_ftc_differentiable` (zero callers).
* Add `theorem lebesgue_ftc_differentiable` to the sibling, in namespace
  `FTCLebesgueACImpliesBV`.

This is the new iter-6+ skeleton, which is implementable *once the
sibling builds*.

## §3 Refined iter-6 skeleton (build-ready modulo sibling repair)

```lean
-- in proofs/Proofs/FundamentalTheoremCalculusLebesgueOQ01.lean:
-- (1) Move imports to top, ahead of /-! ... -/ docstring.
-- (2) Add the import below to the existing 4.
import Mathlib.Analysis.Calculus.FDeriv.Measurable

-- (3) Open MeasureTheory so that `volume` resolves without qualification.
open FTCLebesgue Set ENNReal Finset MeasureTheory

-- (4) Inside `namespace FTCLebesgueACImpliesBV`, after `ac_implies_bv`:

theorem lebesgue_ftc_differentiable {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : AbsolutelyContinuousOn F a b) :
    ∃ S : Set ℝ, MeasurableSet S ∧
      volume (Ioo a b \ S) = 0 ∧
      ∀ x ∈ S, DifferentiableAt ℝ F x := by
  have hbv_icc : BoundedVariationOn F (Set.Icc a b) := ac_implies_bv hab hF
  have hbv : BoundedVariationOn F (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]; exact hbv_icc
  have hae : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∈ Set.uIcc a b → DifferentiableAt ℝ F x :=
    hbv.ae_differentiableAt_of_mem_uIcc
  have hD_meas : MeasurableSet {x : ℝ | DifferentiableAt ℝ F x} :=
    measurableSet_of_differentiableAt ℝ F
  refine ⟨Set.Ioo a b ∩ {x | DifferentiableAt ℝ F x},
          measurableSet_Ioo.inter hD_meas, ?_, ?_⟩
  · have hsub : Set.Ioo a b ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]; exact Set.Ioo_subset_Icc_self
    have hcontain :
        Set.Ioo a b \ (Set.Ioo a b ∩ {x | DifferentiableAt ℝ F x}) ⊆
          Set.uIcc a b ∩ {x | DifferentiableAt ℝ F x}ᶜ := by
      intro x hx
      refine ⟨hsub hx.1, ?_⟩
      intro hxD; exact hx.2 ⟨hx.1, hxD⟩
    apply MeasureTheory.measure_mono_null hcontain
    have hae' : MeasureTheory.volume
        {x | ¬ (x ∈ Set.uIcc a b → DifferentiableAt ℝ F x)} = 0 :=
      MeasureTheory.ae_iff.mp hae
    have heq :
        Set.uIcc a b ∩ {x | DifferentiableAt ℝ F x}ᶜ =
          {x | ¬ (x ∈ Set.uIcc a b → DifferentiableAt ℝ F x)} := by
      ext x
      constructor
      · rintro ⟨hu, hnd⟩ himp; exact hnd (himp hu)
      · intro hx
        refine ⟨(Classical.not_imp.mp hx).1, (Classical.not_imp.mp hx).2⟩
    rw [heq]; exact hae'
  · rintro x ⟨_, hxD⟩; exact hxD

-- (5) Then in proofs/Proofs/FundamentalTheoremCalculusLebesgue.lean (parent):
-- Delete lines 188–204 (the orphan axiom and its docstring).
-- Update meta.json: axiomCount 2 → 1.
```

This skeleton was actually paste-tested in iter-6 (after reordering
imports). The discharge proof's only post-iter-5 surprises were:

* `volume` requires `open MeasureTheory` in the sibling (parent has it,
  sibling does not). **Fix banked.**
* `Classical.not_imp` must be used explicitly (bare `not_imp` is
  ambiguous between `_root_.not_imp` and `Classical.not_imp` with the
  new measurability import in scope). **Fix banked.**
* `MeasureTheory.ae_iff.mp` produces a set in terms of the underlying
  predicate, so `set D := ... with hD_def` defeats the rewrite; inlining
  `{x | DifferentiableAt ℝ F x}` works cleanly. **Fix banked.**

The discharge proof is *the* finished work that iter-7+ can paste once
the sibling rebuilds.

## §4 Sibling-file repair: what iter-7 must fix first

The errors emitted by Docker against `FundamentalTheoremCalculusLebesgueOQ01.lean`
after reordering imports (i.e. blocking the discharge from being
verified):

| Location | Error | Likely fix |
|---|---|---|
| line ~103, ~110 | Unknown constant `eVariationOn.eq_zero_iff.mpr` | Mathlib rename — grep `eVariationOn` for current name (likely `eVariationOn.eq_zero_iff_subsingleton` or moved to a `def`) |
| line ~149 | Unknown constant `eVariationOn.eq_zero_iff.mpr` | (same as above) |
| line ~157 | Unknown identifier `div_lt_iff` | Mathlib renamed to `div_lt_iff₀` (the `₀` variant became canonical) |
| line ~174 | `linarith failed` | Cascade from above — the `nlinarith` step depends on `div_lt_iff` working |
| line ~182 | `ENNReal.natCast_ne_top` as a function | Apply `n` explicitly: `(ENNReal.natCast_ne_top n)` |

Iter-7 should:

1. Reorder imports to top (move `/-! ... -/` after).
2. Add `open MeasureTheory` (needed for §3's discharge).
3. Rename `div_lt_iff` → `div_lt_iff₀`.
4. Apply `ENNReal.natCast_ne_top` to `n`.
5. Resolve the `eVariationOn.eq_zero_iff` name change (grep Mathlib
   web docs at `mathlib4_docs/Mathlib/Analysis/BoundedVariation.html` —
   the lemma may now be `eVariationOn.eq_zero_iff_pairwise_dist_eq_zero`
   or similar; the proof body would adapt).
6. Verify the patched `ac_implies_bv` builds.
7. Then paste the §3 discharge theorem and rebuild.
8. Then delete the parent's orphan axiom and bump meta.json.

**Estimated wall-clock**: 1 Docker round-trip to confirm sibling
repair (~5–10 min warm-cache) + 1 Docker round-trip to confirm
discharge (~5 min) + meta.json/commit/PR. Total: 30–60 min.

## §5 Orphan-axiom finding (§3 corollary)

Grep across the worktree:

```bash
$ grep -rn 'lebesgue_ftc_differentiable' --include='*.lean'
proofs/Proofs/FundamentalTheoremCalculusLebesgue.lean:200:axiom lebesgue_ftc_differentiable ...
```

That's it. Zero callers in any Lean file. The axiom was declared as a
*statement of intent* (this is the result we'd like to prove) rather
than as a load-bearing assumption used by downstream theorems. The
companion axiom `lebesgue_ftc_integral` is actually used (line 235 of
the parent, by `classical_ftc_from_lebesgue_ftc`).

Implication: in the discharge plan, deleting the axiom is a no-op for
the rest of the codebase. The discharge theorem (in the sibling) does
not need to be re-exported under the same name into the parent unless
we choose to. iter-7+ has flexibility to name it whatever fits the
sibling's API.

## §6 Mathlib API names — re-confirmed for iter-7

Both names from iter-4/iter-5 PREP are correct against Mathlib v4.26.0
web docs (re-verified iter-6 via direct fetch):

* `BoundedVariationOn.ae_differentiableAt_of_mem_uIcc`
  in `Mathlib.Analysis.BoundedVariation`. Signature confirmed; transitively
  imported via `Mathlib.Tactic`.
* `measurableSet_of_differentiableAt` (the all-lowercase form, not
  namespaced inside any module) in `Mathlib.Analysis.Calculus.FDeriv.Measurable`.
  Signature: takes the field as the first explicit argument, then the
  function. Usage: `measurableSet_of_differentiableAt ℝ F`. **Must be
  imported explicitly** (does NOT come via `Mathlib.Tactic`).

## §7 Why iter-6 ships PREP (not ACT)

This was supposed to be the ACT cycle. It's ending as PREP because:

1. The iter-5 PREP plan was load-bearing on the sibling being verified.
   It is not.
2. Fixing the sibling's `ac_implies_bv` is unscoped work that touches a
   different gallery entry (`fundamental-theorem-calculus-oq-01-oq-01`),
   which currently advertises status `verified`. A fix is in scope but
   the meta.json bookkeeping (and the audit-tracker churn) is not what
   the iter-5 PREP plan budgeted.
3. ACT-without-sibling-repair is not a valid commit: even if the parent
   change "looks right", the discharge theorem cannot be built and
   verified without the sibling.
4. Three Docker cycles burnt on iter-6 (one with no edits, two with the
   intended ACT plan + incremental fixes) confirm the negative result
   robustly enough to bank.

## §8 What iter-6 PREP does NOT do

* Does **not** modify any Lean file. (Stashed and dropped after iter-6
  Docker verification.)
* Does **not** modify any `meta.json`. (The sibling's claim of
  `verified` is *wrong* in current Mathlib but updating it would be
  a separate scope — see §9.)
* Does **not** progress the Cantor `sorry`.
* Does **not** discharge `lebesgue_ftc_integral`.

## §9 Recommended follow-ups (separate work items)

1. **A1-rated**: Repair sibling file's pre-existing build errors
   (rename `div_lt_iff`, apply `ENNReal.natCast_ne_top`, find replacement
   for `eVariationOn.eq_zero_iff.mpr`, move imports above docstring,
   add `open MeasureTheory`). This unblocks both iter-7's discharge AND
   restores the sibling gallery entry's `verified` claim to truth.
2. **A2-rated**: Once §9.1 lands, paste the §3 discharge theorem and
   delete the parent's orphan axiom (iter-7 ACT).
3. **B**-rated: Update the sibling entry's `meta.json` to reflect
   current `theoremCount` (it goes 6 → 7 with the discharge theorem
   added).
4. **B**-rated: Update the parent's `meta.json`: `axiomCount: 2 → 1`,
   `assumptions` text update, `theoremCount` carry.
5. **C**-rated: Audit other "verified" gallery entries for similar
   stale claims — the sibling-builds-clean assumption was inherited
   for four iterations (iter 1/2/3/4/5) without independent
   verification. Likely other entries share this pattern.

## §10 Provenance

- Worktree path: `.loom/worktrees/researcher-11/`.
- Branch: `research/ftc-lebesgue-oq01-incomplete01-iter6-act` (kept).
- Base SHA: `origin/main` at cycle start = `ac12868a924`
  (research: infinitude-primes-4k1-oq-01 S4 SUPERSEDED).
- origin/main during cycle: advanced to `58bdf51bc62` (mid-cycle, no
  effect — base file unchanged).
- Mathlib version: 4.26.0 (per Docker image `lean4-arm64:v4.26.0`).
- Mathlib doc sources fetched:
  - `mathlib4_docs/Mathlib/Analysis/Calculus/FDeriv/Measurable.html`
    → `measurableSet_of_differentiableAt` confirmed.
- Docker build IDs (output preserved in agent transcript):
  - `bzotxng7j` — initial ACT attempt (iter-5 skeleton); failed at
    line 23 import error.
  - `b8h9dms8n` — same, imports moved to top; failed at proof errors
    (`not_imp` ambiguity + `set` unfolding + `volume` unqualified).
  - `ba5thha79` — proof errors fixed; failed at `volume`/`natCast`
    + pre-existing `ac_implies_bv` errors revealed.
  - `berl0wids` — `volume`/`natCast` fixed; remaining pre-existing
    errors block.
  - `bmqs70bjo` — HEAD-clean Docker build (no edits); failed at
    line 23 import error, confirming HEAD does not build.
- Iter-6 elapsed wall-clock: ~30 minutes (claim TTL 90 minutes).

## §11 Recommendation for iter-7 picker

If iter-7 picks this problem:

* Default move: do §9.1 (sibling repair). 1 build cycle should suffice
  to land the rename fixes. This is the *gate* for any ACT progress on
  this slug.
* If §9.1 lands cleanly: paste §3's discharge and run iter-7 ACT.
  Banked skeleton is build-tested *modulo* the sibling errors.
* If §9.1 needs deeper rework (e.g., `eVariationOn.eq_zero_iff` is gone
  and the proof needs restructuring): bank iter-7 as SURVEY of the
  Mathlib v4.26.0 `eVariationOn` API. Defer ACT to iter-8.
