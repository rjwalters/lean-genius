# S7 ACT — Polymorphic Bridge 1 (`riemannianVolumeBall_eq_nBallVolumeFn`)

**Date**: 2026-05-31
**Researcher**: researcher-1
**Phase**: ACT (Lean code — paste of S3 PREP §3.2 recipe)
**Predecessors**: S6 (gallery-wiring, this researcher, same day),
S5 STATE-SYNC, S3 PREP #19136 (Workaround A erratum / proof-chain skeleton),
S2 ACT (bulk merge #19454 → main commit `ecb47b35601`).
**Mode**: REVISIT (continuing RICH-knowledge problem; KS=32 at claim).
**Outcome**: progress — polymorphic Bridge 1 theorem added to OQ-03 Lean file.
Build verification deferred per **G9 lake self-loop** in the main repo.

## Goal

Discharge the S3 ACT deliverable from the `state.md` §"Next Action" menu:
extend `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` with the
polymorphic Bridge 1 theorem under abstract
`[InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasureSpace E]
[BorelSpace E] [Nontrivial E]`, identifying the closed-ball volume
`(volume (Metric.closedBall p r)).toReal` with the parent OQ-01
polynomial `CircumferenceViaDifferentiationOQ01.nBallVolumeFn
(Module.finrank ℝ E) r`.

## Pre-flight check (re-verification of Mathlib API surface)

**S3 PREP wrote on 2026-05-14**: `InnerProductSpace.volume_closedBall`
lives at `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:372`
under pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Re-verified at the same pinned SHA on 2026-05-31** (17 days later)
via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/
MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean?ref=2df2f015…`:

| Object | S3 PREP line | 2026-05-31 line | Drift |
|--------|--------------|------------------|-------|
| `EuclideanSpace.volume_ball` (header) | 325 | 325 | 0 |
| `EuclideanSpace.volume_closedBall` | 342 | 342 | 0 |
| **`InnerProductSpace.volume_ball`** | 361 | 361 | 0 |
| **`InnerProductSpace.volume_closedBall`** | **372** | **372** | **0** |
| `InnerProductSpace.volume_ball_of_dim_even` | 377 | 377 | 0 |
| `InnerProductSpace.volume_closedBall_of_dim_even` | 383 | 383 | 0 |
| `InnerProductSpace.volume_ball_of_dim_odd` | 389 | 389 | 0 |
| `InnerProductSpace.volume_closedBall_of_dim_odd` | 399 | 399 | 0 |
| `EuclideanSpace.volume_closedBall_fin_two` | 417 | 417 | 0 |
| `EuclideanSpace.volume_closedBall_fin_three` | 427 | 427 | 0 |
| `namespace InnerProductSpace … end InnerProductSpace` | 349–405 | 349–405 | 0 |

**Net drift: 0**. The pinned SHA is identical to what S3 PREP audited;
the file content is byte-identical. The `2df2f015…` SHA has not budged
in the intervening 17 days, so S3 PREP's recipe applies verbatim.

The lemma signature at line 372 matches S3 PREP §1 exactly:

```lean
namespace InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section Nontrivial
variable [Nontrivial E]

theorem volume_closedBall (x : E) (r : ℝ) :
    volume (Metric.closedBall x r) = (.ofReal r) ^ finrank ℝ E *
      .ofReal (√π ^ finrank ℝ E / Gamma (finrank ℝ E / 2 + 1)) := by
  rw [addHaar_closedBall_eq_addHaar_ball, InnerProductSpace.volume_ball _]
```

(The `[MeasureSpace E]` typeclass is implicit downstream of `BorelSpace`
+ Mathlib's `Module.instMeasureSpace`-class infrastructure; downstream
callers (including this S3 ACT) must supply `[MeasureSpace E]` explicitly
in the variable block to access `volume`.)

## What I Did

1. **Re-verified pinned-SHA citations** (above): 0 drift since S3 PREP.

2. **Added Lean code** to `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean`:
   - **New import**: `import Proofs.CircumferenceViaDifferentiationOQ01`
     (for `nBallVolumeFn` and `unitBallVolume`).
   - **New theorem**: `riemannianVolumeBall_eq_nBallVolumeFn`, pasted
     verbatim from S3 PREP §3.2 recipe with minor formatting:
     - 6-class variable block:
       `{E} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
       [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E] [Nontrivial E]`
     - Proof body: 6-step rewrite chain (see §below).
     - `have h_sqrt_pow : Real.sqrt π ^ n = π ^ ((n : ℝ) / 2)` helper
       (5 LOC) via `Real.sqrt_eq_rpow` + `Real.rpow_natCast` +
       `Real.rpow_mul`.
   - **Updated docstring** header comment to advertise the
     polymorphic Bridge 1 deliverable; added explanation of the
     `[Nontrivial E]` typing and a pointer to S3 PREP §3.

3. **No header-text removed** — the n = 2, 3 concrete deliverables
   (4 theorems) remain unchanged in body. Only the file header and the
   theorem list at the end were extended.

## Files Modified

- `proofs/Proofs/CircumferenceViaDifferentiationOQ03.lean` (modified):
  93 LOC → 152 LOC (+59 LOC net). 4 theorems → 5 theorems.
- `research/problems/circumference-via-differentiation-oq-03/state.md`
  (updated — phase ACT-S3, iteration history extended).
- `research/problems/circumference-via-differentiation-oq-03/sessions/2026-05-31-s7-s3-act-polymorphic-bridge-1.md`
  (NEW — this file).
- `src/data/research/problems/circumference-via-differentiation-oq-03.json`
  (cursor refresh).

## The Proof-Chain in Detail

The recipe is verbatim from S3 PREP §3.2 / §3.3. Step-by-step:

| Step | Tactic | Goal-state after |
|------|--------|-------------------|
| 0 (start) | — | `(volume (closedBall p r)).toReal = nBallVolumeFn (finrank ℝ E) r` |
| 1 | `rw [InnerProductSpace.volume_closedBall p r, ENNReal.toReal_mul]` | `((.ofReal r)^n).toReal * (.ofReal (√π^n / Γ((n:ℝ)/2+1))).toReal = nBallVolumeFn n r` |
| 2 | `rw [show ((.ofReal r)^n).toReal = r^n from ?_]` then `swap; rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]` | `r^n * (.ofReal (√π^n / Γ((n:ℝ)/2+1))).toReal = nBallVolumeFn n r` |
| 3 | `have h_quot_nn := div_nonneg (pow_nonneg sqrt_pi_nn _) (Gamma_pos.le)`; `rw [ENNReal.toReal_ofReal h_quot_nn]` | `r^n * (√π^n / Γ((n:ℝ)/2+1)) = nBallVolumeFn n r` |
| 4 | `set n := Module.finrank ℝ E; unfold nBallVolumeFn unitBallVolume` | `r^n * (√π^n / Γ((n:ℝ)/2+1)) = π^((n:ℝ)/2) / Γ((n:ℝ)/2+1) * r^n` |
| 5 | `have h_sqrt_pow : √π^n = π^((n:ℝ)/2) := by rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul]; congr 1; ring`; `rw [h_sqrt_pow]` | `r^n * (π^((n:ℝ)/2) / Γ((n:ℝ)/2+1)) = π^((n:ℝ)/2) / Γ((n:ℝ)/2+1) * r^n` |
| 6 | `ring` | ✓ |

Net body: 21 LOC, of which 5 LOC are the `h_sqrt_pow` helper.

## Calibration / Status

- **Lean LOC**: 93 → 152 (+59 net, including +5 docstring header
  expansion, +30 new theorem body + docstring, +1 new import,
  re-formatting in the import block, end-namespace line preserved).
- **Theorems**: 4 → 5.
- **Sorries**: 0 → 0 (verified via `grep -c sorry`).
- **Axioms**: 0 → 0 (verified via `grep -c '^axiom '`; no
  structure-encoded assumptions either — typeclass hypotheses
  `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional E]
  [MeasureSpace E] [BorelSpace E] [Nontrivial E]` are stated on the
  individual theorem, not as ambient `axiom` declarations).
- **Build verification**: **Pending — G9 lake self-loop in the main
  repo**. The main repo's `proofs/.lake` is a self-referential symlink
  (`/Users/rwalters/GitHub/lean-genius/proofs/.lake →
  /Users/rwalters/GitHub/lean-genius/proofs/.lake`), which blocks the
  Docker build wrapper across all sharing worktrees. Per project memory,
  this is a known cross-worktree blocker; this PR ships under the
  documented "build pending — G9 lake self-loop" qualifier and does not
  attempt to fix the self-loop from a research PR.

## Risk Register (build risks at the deferred verification step)

| Risk | Probability | Mitigation |
|------|-------------|------------|
| R1: `ENNReal.toReal_pow` direction mismatch | low | S3 PREP §3.5 used the `show … from ?_` workaround precisely for this — copied verbatim |
| R2: `hr : 0 ≤ r` insufficient for `ENNReal.toReal_ofReal` | none | direct match |
| R3: `Gamma_pos_of_pos` needs `(n : ℝ)/2 + 1 > 0` | low | `[Nontrivial E]` → `n ≥ 1` → `(n : ℝ)/2 + 1 ≥ 1.5 > 0`; `positivity` should handle |
| R4: `Real.rpow_natCast` rename | low | Mathlib has had this name stable through v4.26.0; deprecation aliases also routinely exist |
| R5: `Nontrivial E` derivation | n/a | kept as explicit typeclass hypothesis |
| R6: canonical `MeasureSpace E` consistency | by design | the polymorphic theorem requires the caller to supply a canonical Haar `MeasureSpace E`; Mathlib synthesizes this for `EuclideanSpace ℝ (Fin n)`, `PiLp`, etc. |

If R1 or R4 fires at the deferred Docker step, the fix is mechanical
(swap `show … from ?_` to a more explicit ascription, or use the
deprecated alias). No mathematical content is at risk.

## What Remains

- **S4 ACT — Workaround C' polymorphic main theorem**
  (`riemannianVolumeBall_hasDerivWithinAt_nBallVolumeFn`,
  stating `dV/dr = nSphereSurfaceFn (finrank ℝ E) r` in the abstract
  `[InnerProductSpace ℝ E]` setting). Now unblocked by this S3 ACT —
  the proof composes `riemannianVolumeBall_eq_nBallVolumeFn` (this
  iteration) with `CircumferenceViaDifferentiationOQ01.nBallVolumeFn_hasDerivAt`
  via `HasDerivAt.congr` (or its `HasDerivWithinAt` variant). Estimated
  scope: ~30 LOC, one iteration.

- **R2 full-Riemannian, R3 standalone n-dim coarea**: still
  Mathlib-roadmap gaps; unchanged from S1 OBSERVE assessment.

## Next Action

(b) **S4 ACT polymorphic main** — paste over OQ01's polynomial-derivative
chain via `HasDerivAt.congr`. ETA: 1 iteration.

Once both S3 ACT (this) and S4 ACT are on main and Docker-verified
after the G9 lake-self-loop fix, the R1 vector-space deliverable
encompasses arbitrary `[InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
[Nontrivial E]` — the polymorphic generalization claimed at S1 OBSERVE.

The R2 full-Riemannian and R3 standalone n-dim coarea targets remain
Mathlib-roadmap deferred (see problem.md §"Three Routes").
