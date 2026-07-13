# Session S11 ACT step-1-contingency — `haarT2 = volume` bridge

**Date**: 2026-05-31
**Researcher**: researcher-1
**Iteration**: 10 (bump from 9)
**Phase**: ACT
**Mode**: REVISIT (continuing S10 + S9 ACT recipe progression)
**Prior Status**: ACT (S10 ACT step-2 landed `coeFn_finset_sum_haarT2`, PR #21252 MERGED)

## Summary

Discharged **step 1 contingency** of the S7 audit §4 ACT recipe — the
`haarT2 = volume` measure-equality bridge on `Fin 2 → AddCircle 1`. Adds
one sorry-free, axiom-free public theorem `haarT2_eq_volume` (+33 LOC
including section docstring) to `proofs/Proofs/FourierSeriesOQ04OQ01.lean`
(413 → 446 lines, 11 → 12 theorems). Build verified (Docker, 7743 jobs
clean; only the pre-existing L²-sorry warning at line 148 remains).

With S9 (cofinality, step 3) + S10 (`Lp.coeFn_finset_sum` helper, step 2)
+ S11 (this iter, step 1 contingency), **3 of 6 recipe steps are now
landed**. Remaining ACT scope: 25-45 LOC for steps 1-setup + 4 + 5 + 6.

## What Landed

### New theorem

```lean
/-- **`haarT2 = volume`** — the product Haar measure on `𝕋²` equals the
    standard `volume` measure on `Fin 2 → AddCircle 1`. -/
theorem haarT2_eq_volume : haarT2 = (volume : Measure T2) := by
  have key : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
  show Measure.pi (fun _ : Fin 2 => (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))))
       = (volume : Measure T2)
  simp_rw [key]
  rfl
```

Public theorem in a new section after `coeFn_finset_sum_haarT2`. Build-verified.

### Mathematics

The proof exploits two `rfl` Mathlib lemmas:

1. **`AddCircle.volume_eq_smul_haarAddCircle`** (`AddCircle.lean:92`):
   ```lean
   (volume : Measure (AddCircle T)) = ENNReal.ofReal T • (@haarAddCircle T _) := rfl
   ```
   At `T = 1`: `ENNReal.ofReal 1 = 1` (via `ENNReal.ofReal_one`), and
   `(1 : ℝ≥0∞) • μ = μ` (via `one_smul`). So `volume = haarAddCircle` on
   `AddCircle 1`. Three tactic steps, one rewrite chain.

2. **`volume_pi`** (`Pi.lean:652`):
   ```lean
   (volume : Measure (∀ i, α i)) = Measure.pi fun _ => volume := rfl
   ```
   This is *also* a `rfl` lemma (the `MeasureSpace.pi` instance defines it
   that way at `Pi.lean:214`). So once we rewrite `haarAddCircle` to
   `volume` inside the `fun _ =>` binder, the resulting
   `Measure.pi (fun _ => volume) = volume` closes by `rfl`.

The bridge is two-line mathematics: collapse the scaling at `T = 1`,
extend to the product. The S7 audit §2.5 had flagged this as an "errata"
deferred to a contingency step; in practice it required no additional
machinery beyond what Mathlib already exposes.

### Why this is the "step 1 contingency"

The S7 audit §4 ACT recipe enumerates 6 steps to discharge
`sphPartialSum_L2_norm_converge`. Step 1 has two parts:
- 3-5 LOC: "Setup" — imports for `AddCircleMulti` and `l2Space`
- 3-5 LOC: "haarT2/volume contingency" — bridge between our `haarT2` and
  Mathlib's default `volume` on `Fin 2 → AddCircle 1`

The Mathlib engine `hasSum_mFourier_series_L2` (verified at pin v4.26.0
`AddCircleMulti.lean:224`) is stated over `L²(UnitAddTorus d) := d → UnitAddCircle =
d → AddCircle 1` with the **default `volume` measure** (via the
local-instance-overridden `MeasureSpace UnitAddCircle := ⟨haarAddCircle⟩`
that is *not* exported outside that file). To invoke it on our
`haarT2`-stated theorems we need the measure-equality bridge — this
iteration delivers it.

The "Setup" sub-step is deferred until next ACT (it's a single
`import Mathlib` confirmation; no work needed).

## Build Status

**Docker-built and verified** at this iteration's worktree HEAD:

```
✔ Built Proofs.FourierSeriesOQ04OQ01
warning: Proofs/FourierSeriesOQ04OQ01.lean:148:8: declaration uses 'sorry'
Build completed successfully (7743 jobs).
```

Single expected warning (the pre-existing `sphPartialSum_L2_norm_converge`
sorry); no new warnings from the bridge addition; build cached at
[120s] for the Mathlib cache-get and elaborated cleanly.

## File Changes

| Path | Δ | Description |
|---|---|---|
| `proofs/Proofs/FourierSeriesOQ04OQ01.lean` | +33 LOC | S11 step-1-contingency section + `haarT2_eq_volume` theorem |
| `src/data/proofs/fourier-series-oq-04-oq-01/meta.json` | sync | lineCount 413→446; theoremCount 11→12; new section + originalContribution |
| `src/data/research/problems/fourier-series-oq-04-oq-01.json` | sync | iteration 9→10; focus/progressSummary/builtItems/lastUpdate refreshed |
| `research/problems/fourier-series-oq-04-oq-01/state.md` | sync | bumped iter; new Current Focus; old Current → Previous Focus header |
| `research/problems/fourier-series-oq-04-oq-01/sessions/2026-05-31-s11-act-step1-contingency-haart2-volume.md` | NEW | this file |

## Knowledge Added

### Insights

1. **`volume = haarAddCircle` on `AddCircle 1` is two-line**: the `rfl`
   nature of `volume_eq_smul_haarAddCircle` combined with `T = 1`
   trivialisation makes this far simpler than the S2f PREP / S7 audit
   had budgeted (the audit had allocated 3-5 LOC of "contingency" for
   this; the actual proof is 1 tactic line for `key`, then 3 lines for
   the product-side bridge).

2. **`volume_pi` is `rfl`**: the `Pi.lean:652` theorem
   `(volume : Measure (∀ i, α i)) = Measure.pi fun _ => volume` is a
   definitional equality, not a proof. This means `Measure.pi (fun _ =>
   volume) = volume` closes by `rfl` once the inner function is volume
   (after rewriting `haarAddCircle` to `volume` under the binder).

3. **`simp_rw` under binder + `rfl` is the cleanest pattern**: avoiding
   `congr 1` (which can fail on `Measure.pi` due to its
   `irreducible_def`) and `funext` (which would require an explicit
   measure-equality argument), the `simp_rw [key]; rfl` pattern keeps
   the proof concise and avoids any irreducibility friction.

### Built Items

- `haarT2_eq_volume` (sorry-free, axiom-free, public, build-verified)

### Next Steps

- **S2e ACT close** (~25-45 LOC remaining; 3 of 6 steps done): the
  Plancherel-tail engine via `hasSum_mFourier_series_L2`. Wire up
  `haarT2_eq_volume` + `coeFn_finset_sum_haarT2` + S9 cofinality with
  the Mathlib `mFourierBasis.hasSum_repr` (`l2Space.lean:443`) and
  `Lp.norm_def` (`LpSpace/Basic.lean:215`). Tractable single-iteration
  target.

- **Alternative S2b**: Bochner-Riesz a.e. convergence for δ > 1/2 in n=2
  (Stein 1958, ~300-500 lines, 2-3 iterations).

- **S2-Gauss-sharp**: extend S2-Gauss-real's `(2|R|+3)²` qualitative
  bound to `card ≤ ⌈π·R²⌉ + O(R)` via boundary-lattice / two-squares
  analysis (~80-150 lines).

## Honest Assessment

- **Mode**: REVISIT (continuing a multi-session ACT recipe)
- **Mathematical novelty**: zero. The bridge is two `rfl` Mathlib lemmas
  chained with `ENNReal.ofReal_one` and `one_smul`. The work is in
  *recognising* that the bridge is this simple.
- **Recipe progress**: 3/6 steps now landed. Steps 4-6 are wire-up; the
  hard mathematical bearer (`hasSum_mFourier_series_L2`) is supplied by
  Mathlib. A future single-iteration close is plausible.
- **Status delta**: same axiom/sorry surface (1 axiom, 1 sorry). No
  unconditional progress on the L² norm convergence sorry itself —
  this is infrastructure that *enables* closing it.
- **PR target**: research label, build-verified. No `loom:review-requested`
  (math PR — deployer-merged).
