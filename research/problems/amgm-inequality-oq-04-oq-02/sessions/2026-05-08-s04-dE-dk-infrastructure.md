## Session 2026-05-08 (Session 4, ACT) — dE/dk infrastructure

**Mode**: ACT (Lean code added; no axioms eliminated yet — that lands in S5).
**Outcome**: progress (≈115 lines new code, 0 sorries added, 0 axioms added).

### Goal

Provide the gallery-side ingredients to apply
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(pinned in S3) to prove `dE/dk = (E - K)/k` for `0 < k < 1`. This session
delivers the *pure-algebra and pointwise-derivative* ingredients; the
parametric-integral application itself (bound construction, `h_bound`,
`bound_integrable`) is left for S5.

### What landed in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`

A new `§ 8` containing five definitions/lemmas:

1. **`dIntegrandE k θ`** (`noncomputable def`): the partial derivative
   `∂_k √(1 - k² sin²θ) = -k sin²θ / √(1 - k² sin²θ)`.

2. **`dIntegrandE_continuous`** / **`dIntegrandE_integrable`** (`Continuous.div₀`,
   `.intervalIntegrable`): regularity, valid on the entire domain `k² < 1`
   (the radicand is bounded below by `1 - k² > 0`, so the denominator stays
   away from 0).

3. **`integrandE_hasDerivAt_in_k`**: the pointwise chain-rule fact for fixed
   θ. Uses `hasDerivAt_pow`, `HasDerivAt.mul_const`, `HasDerivAt.sub`, and
   `HasDerivAt.sqrt` (the last requires `radicand ≠ 0`, supplied by the
   existing `denom_pos` lemma in `AmgmInequalityOQ04OQ01`). The Mathlib API
   yields `(-(2 k sin²θ)) / (2 √(...))`, which `field_simp; ring` reduces to
   `dIntegrandE k θ` form.

4. **`dIntegrandE_mul_k`** (the algebraic-split lemma):
   ```
   k · dIntegrandE k θ = ellipticIntegrandE k θ - ellipticIntegrand k θ
   ```
   Proof: with `s := √(1 - k² sin²θ)` and `s² = 1 - k² sin²θ`, multiplying both
   sides by `s` yields `-k² sin²θ = s² - 1`, which is the Pythagorean identity
   rearranged. Closed with `field_simp` plus `linear_combination -hs_sq`.

5. **`integral_dIntegrandE_eq`** (the integral identity for `0 < k < 1`):
   ```
   ∫₀^{π/2} dIntegrandE k θ dθ = (ellipticE k - ellipticK k) / k
   ```
   Proof outline: by (4), the integrand equals `(E_int - K_int) / k`; pull the
   `1/k` outside via `intervalIntegral.integral_div`; split the difference via
   `intervalIntegral.integral_sub` (using `ellipticE_integrable` and
   `ellipticK_integrable`); recognize the resulting integrals as
   `ellipticE k` and `ellipticK k` definitionally.

### Why this matters

The conclusion of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, when
applied to the E-integrand, gives:

```
HasDerivAt ellipticE (∫₀^{π/2} dIntegrandE k θ dθ) k
```

Lemma (5) above rewrites the integral on the right to `(ellipticE k - ellipticK k) / k`,
yielding the target

```
HasDerivAt ellipticE ((ellipticE k - ellipticK k) / k) k.
```

So the Lean-side bridge from "Mathlib gives me the derivative as some integral" to
"and that integral simplifies to (E - K)/k" is now in place.

### What S5 still has to do

The 7 hypotheses of `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
that this session does NOT discharge:

- `ε_pos`, `hF_meas`: trivial after picking `δ` and using
  `Continuous.aestronglyMeasurable`.
- `hF_int`: `(integrandE_continuous k).intervalIntegrable` (already exists).
- `hF'_meas`: `(dIntegrandE_continuous hk).aestronglyMeasurable` (uses S4 lemma).
- `bound_integrable`: integrability of the *uniform majorant* of `dIntegrandE`
  on a small ball around `k₀`. The natural choice is
  `bound θ = (k₀ + δ) · sin²θ / √(1 - (k₀ + δ)² sin²θ)` for some
  `0 < δ < 1 - k₀`; integrability is again
  `Continuous.intervalIntegrable`. ~10 lines.
- `h_bound`: the pointwise majorization
  `‖dIntegrandE κ θ‖ ≤ bound θ` for `κ ∈ ball k₀ δ`. Numerator increases in
  `|κ|`, denominator decreases (since the radicand is antitone in `κ²`); standard
  monotonicity. ~20–30 lines.
- `h_diff`: the pointwise chain rule for κ ∈ ball k₀ δ — directly from
  `integrandE_hasDerivAt_in_k`. ~5 lines.

Total S5: ~50–80 lines (down from the original ~75–100 estimate, because
S4 took on the chain-rule + algebraic-split pieces).

### Build status

Build kicked off via `./proofs/scripts/docker-build.sh Proofs.AmgmInequalityOQ04OQ02`.
Pending result at PR-creation time. PR title is tagged `[BUILD UNVERIFIED]`
if not confirmed before merge.

### Files modified

- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (≈+115 lines, 0 sorries, 0 axioms;
  new section `§ 8`).
- `research/problems/amgm-inequality-oq-04-oq-02/state.md` (next-action: S5).
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-08-s04-dE-dk-infrastructure.md` (this report).
- `src/data/research/problems/amgm-inequality-oq-04-oq-02.json` (knowledge updates).

### Honest assessment

- This session does NOT eliminate the `legendre_relation` axiom — it adds
  *infrastructure* for the future axiom elimination.
- The `dE_dk` theorem itself is NOT yet in the file; it is constructed in S5.
- Algebraic and chain-rule scaffolding is now done, which is roughly 30-40% of
  the work toward eliminating the axiom; S5 (bound + parametric-integral
  application) is the larger remaining piece.
- No claim of "verified" or "complete"; this is mid-stream ACT progress.

---
