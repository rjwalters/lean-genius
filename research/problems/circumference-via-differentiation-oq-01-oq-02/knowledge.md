# Knowledge Base: circumference-via-differentiation-oq-01-oq-02

Extension of the gallery proof `circumference-via-differentiation-oq-01`
("n-Dimensional Surface Area via Differentiation of Volume") to the **L^p**
unit ball.

---

## Problem Understanding

The unit ball `B_p^n = {x ∈ ℝ^n : Σ |x_i|^p ≤ 1}` has volume
(Dirichlet/Liouville; the seeker stub attributes it to Pisier 1989)

        V_n(p) = 2^n · Γ(1/p + 1)^n / Γ(n/p + 1).

The open question: does the parent's identity **dV/dr = surface area** still hold
for the L^p surface area when `p ≠ 2`? The stub flags the difficulty as "the L^p
surface is not the radial derivative for p ≠ 2 because the surface is not a level
set of the radius function in the Euclidean sense."

**Refinement of the premise.** The dilated ball `r·B_p = {‖x‖_p ≤ r}` *is* a
level set of the L^p norm `ρ(x) = ‖x‖_p`. The real subtlety is not "level set or
not" but the **coarea weight** `1/|∇ρ|`: `|∇ρ| ≡ 1` only for the Euclidean norm.

---

## Insights

### Session 2026-06-15 (ORIENT, researcher-9) — sharp answer + Mathlib already has the volume

**Mode**: FRESH (EMPTY → ORIENT). **Outcome**: complete mathematical answer with
an all-pass independent numerical verifier, plus the discovery that Mathlib v4.26
already proves the volume formula, which makes the volume/derivative half a thin
ACT.

#### The answer (it depends on which surface measure)

1. **Volume + radial scaling — fully tractable.** For `1 ≤ p`,
   `Vol{‖x‖_p ≤ r} = V_n(p) · r^n`, hence by the power rule

        dV/dr = n · V_n(p) · r^(n-1).                                       (★)

2. **Which "surface area" does (★) equal?** By the coarea formula for `ρ = ‖·‖_p`,

        dV/dr = ∫_{‖x‖_p = r} 1/|∇ρ(x)| dℋ^{n-1}(x),                    (coarea)

   with `|∇ρ|` the **Euclidean** gradient norm. On the unit sphere
   `∂ρ/∂x_i = sgn(x_i)·|x_i|^{p-1}`, so

        |∇ρ|^2 = Σ |x_i|^{2p-2},

   which is identically `1` on `Σ|x_i|^p = 1` **iff p = 2** (then `2p-2 = p = 2`).
   Therefore:
   - **p = 2**: weight `= 1`, so (★) **equals** the Euclidean Hausdorff `(n-1)`-
     surface measure of the sphere — this is exactly the parent theorem.
   - **p ≠ 2** (finite): the weight `1/|∇ρ|` varies, so (★) is a
     `|∇ρ|^{-1}`-**weighted** surface integral, **NOT** the Euclidean Hausdorff
     surface measure of `{‖x‖_p = r}`.
   - **p = ∞** (cube): `|∇‖·‖_∞| = 1` ℋ^{n-1}-a.e. on the open faces, so the
     identity holds again (degenerately).

   **Conclusion: the naive "dV/dr = Euclidean surface area" identity is FALSE for
   every finite p ≠ 2, and TRUE for p = 2 (and a.e. for p = ∞).** The always-true
   statement is the coarea-weighted one.

   **Anchor witness** (n=2, p=1, the L^1 diamond): `V_2(1) = 2`, `dV/dr = 4`, but
   the Euclidean perimeter is `4√2 ≈ 5.657`. The coarea-weighted surface is
   `(4√2)/√2 = 4 = dV/dr`. ✔

#### Durable verification

`verify_lp_ball.py` (Python stdlib, exact Γ via `math.gamma`, deterministic
Simpson in n=2 + Monte-Carlo cross-checks in n=2,3,4) — **ALL PASS**:
- (A) Lebesgue volume vs the Dirichlet closed form (n=2 Simpson; n=3,4 MC).
- (B) radial scaling `dV/dr = n·V_n(p)·r^(n-1)`.
- (C) for `p ∈ {1, 1.5, 2, 3, 4}` in n=2: coarea-weighted surface `== dV/dr` for
  ALL p, while Euclidean perimeter `== dV/dr` ONLY for p = 2 (the symmetry-
  reduced quadrature integrates only the smooth half `x ∈ [0,(½)^{1/p}]` and ×8
  to avoid the vertical-tangent endpoint).

#### Mathlib bearers (confirmed against v4.26.0, pin `2df2f0150c27`)

- **The volume formula is ALREADY in Mathlib**:
  `MeasureTheory.volume_sum_rpow_le` (and `..._lt`) in
  `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`:

        volume {x : ι → ℝ | (∑ i, |x i|^p)^(1/p) ≤ r}
          = ofReal r ^ card ι
            * ofReal ((2 * Γ(1/p + 1))^card ι / Γ(card ι/p + 1))     (1 ≤ p)

  At `r = 1`, `card ι = n`, this is **verbatim** the Dirichlet `V_n(p)`, and the
  `ofReal r ^ card ι` factor is the `r^n` scaling. Companion lemmas:
  `MeasureTheory.measure_unitBall_eq_integral_div_gamma`,
  `volume_sum_rpow_lt_one`, and the Euclidean specializations
  `EuclideanSpace.volume_ball/volume_closedBall`.
- **Derivative**: the same power-rule API the parent OQ-01 uses —
  `hasDerivAt_pow`, `HasDerivAt.const_mul`, `HasDerivAt.deriv`. (Done below.)
- **Coarea / surface measure is a GENUINE GAP**: Mathlib v4.26 has
  `MeasureTheory/Measure/Hausdorff.lean` (Hausdorff measure) but **no coarea
  formula** (no `Coarea` file; tree grep at the tag returns nothing). So the
  always-true weighted identity (coarea) — and any faithful statement of the
  surface side — cannot yet be expressed in Lean.

#### Lean artifact (build-pending, UNREGISTERED)

`proofs/Proofs/CircumferenceViaDifferentiationOQ01OQ02.lean`:
- `lpUnitBallVolume n p := (2·Γ(1/p+1))^n / Γ(n/p+1)` and
  `lpBallVolumeFn n p r := lpUnitBallVolume n p · r^n` — defined to match
  `volume_sum_rpow_le` verbatim so a future live session can `rw` that lemma to
  prove `volume = lpBallVolumeFn` with only `ENNReal.toReal` bookkeeping.
- `lpBallVolumeFn_hasDerivAt` / `deriv_lpBallVolume` — proof of (★), mirroring the
  verified parent `nBallVolumeFn_hasDerivAt` (only the constant differs).
- The surface side is documented, not stated as a theorem (coarea gap above). The
  false Euclidean identity is recorded only as prose.

Build-pending under a Docker + Aristotle blackout this session; intentionally not
added to `Proofs/Proofs.lean` until it compiles live.

---

## Next steps

1. **ACT (live, ~30 min once Docker returns).** Build the file; add a bridge
   theorem `volume {x | (∑|x i|^p)^(1/p) ≤ r} = ENNReal.ofReal (lpBallVolumeFn n p r)`
   by `rw [volume_sum_rpow_le]` + `ENNReal.ofReal` arithmetic, then register it.
2. **Surface side is BLOCKED on Mathlib infrastructure.** A faithful Lean
   treatment needs a coarea formula (or at least the `|∇ρ|^{-1}`-weighted surface
   integral); neither is in Mathlib v4.26. Either wait for upstream or scope a
   narrow n=2 perimeter computation as a separate sub-question.
3. (Optional) state the `p = 2` recovery as a corollary once a surface-measure
   API exists, tying back to the parent.

## Dead Ends / Non-starters

- Trying to prove `dV/dr = Euclidean surface area` for general p: **false**
  (n=2, p=1 already breaks it, 4 ≠ 4√2). The correct invariant is the coarea-
  weighted surface.
- Re-deriving the volume formula from scratch: unnecessary —
  `MeasureTheory.volume_sum_rpow_le` already has it.
- A faithful Lean statement of the surface side this session: blocked (no coarea
  formula in Mathlib v4.26).

## Session 2026-06-15 (researcher-1) — VERIFY: confirmed volume_sum_rpow_le matches the file; deriv theorem build-ready

**Mode**: REVISIT (MODERATE; dual blackout: `docker info` times out, Aristotle MCP `prove` → 404).
**Outcome**: de-risk — the build-pending `CircumferenceViaDifferentiationOQ01OQ02.lean` (0 axioms /
0 sorries, unregistered) confirmed build-ready against authoritative Mathlib.

- **The keystone dependency exists with a matching statement.**
  `MeasureTheory.volume_sum_rpow_le [Nonempty ι] {p} (hp : 1 ≤ p) (r)`
  (`Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:221`):
  `volume {x : ι→ℝ | (∑ i, |x i|^p)^(1/p) ≤ r} = (.ofReal r)^card ι · .ofReal ((2·Γ(1/p+1))^card ι /
  Γ(card ι/p+1))`. The file's `lpUnitBallVolume`/`lpBallVolumeFn` reproduce this RHS verbatim ⇒ the
  planned bridge `rw [volume_sum_rpow_le]` will go through (only `ENNReal.ofReal` bookkeeping left).
- **The derivative theorem is robust.** `lpBallVolumeFn_hasDerivAt` uses only `hasDerivAt_pow` +
  `HasDerivAt.const_mul` + `ring` (mirrors the verified parent `nBallVolumeFn_hasDerivAt`).
- Surface side remains BLOCKED (no coarea formula in Mathlib 4.26) — unchanged; the false Euclidean
  identity stays prose-only (correct).

### Next Steps (Docker-gated)
- Build the file, add the bridge theorem `volume {…} = ENNReal.ofReal (lpBallVolumeFn n p r)` via
  `rw [volume_sum_rpow_le]`, register. Then the volume side is a `verified` entry.
