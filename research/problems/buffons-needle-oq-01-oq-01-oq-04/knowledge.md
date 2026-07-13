# Knowledge Base: buffons-needle-oq-01-oq-01-oq-04

Higher-dimensional Cauchy-Crofton formula —
expected crossings of curves with random hyperplane grids in ℝⁿ.

---

## Problem Understanding

The classical Buffon-Barbier formula
E[crossings] = 2L/(π d) generalizes to n dimensions via the
Cauchy-Crofton formula
E[crossings] = c_n · L / d
where c_n = 2σ_{n-2}/((n-1)·σ_{n-1}) and σ_k is the surface
area of the unit k-sphere.

This is the integral-geometric statement underlying both Buffon's
needle (1733) and Crofton's expected-intersection formula (1868).
Santaló's *Integral Geometry and Geometric Probability* (1976)
remains the standard modern reference.

---

## Insights

- **Dimension ladder of crossing constants**:
  c_2 = 2/π ≈ 0.637, c_3 = 1/2, c_4 = 4/(3π) ≈ 0.424.
  In general c_n decreases monotonically and c_n → 0; geometrically,
  in higher dimensions a "random" hyperplane is increasingly likely
  to be transverse to a low-dimensional curve.
- **Sphere surface areas via Γ**: σ_n = 2π^{(n+1)/2}/Γ((n+1)/2)
  unifies σ_0 = 2 (two endpoints), σ_1 = 2π (circle),
  σ_2 = 4π, σ_3 = 2π². Mathlib's `Real.Gamma`,
  `Gamma_one_half_eq`, and `Gamma_add_one` give clean elementary
  proofs at small n.
- **Angular average is the analytic bridge**: the n-dim formula
  reduces to the integral identity
  ∫_{RP^{n-1}} |⟨v, ω⟩| dω = (σ_{n-2}/(n-1)) · ‖v‖.
  In 2D this collapses to ∫₀^π |sin(θ+c)| dθ = 2 — exactly the
  identity used in `BuffonsNeedleOQ01OQ01.lean`.
- **Unit-circle sanity check**: a unit circle (perimeter 2π) on
  a unit grid yields c_2 · 2π / 1 = (2/π)·2π = 4 crossings on
  average — two entries plus two exits.
- **Sphere area recurrence**: σ_n / σ_{n-2} comes from the
  Γ identity Γ((n+1)/2) = ((n-1)/2)·Γ((n-1)/2), giving a clean
  ladder for computing all c_n.

---

## Mathlib Gap

The angular-average identity is not provable from current Mathlib
because Mathlib (as of 2026-04) lacks:

1. **Haar / surface measure on S^{n-1}**: there is no canonical
   measurable structure on the unit sphere, no rotation-invariant
   probability measure of total mass σ_{n-1}, and no spherical
   coordinate change-of-variables theorem.
2. **Quotient measure on RP^{n-1}**: the projective sphere
   S^{n-1}/{±1} has no measure-theoretic API.
3. **The Beta-function identity**:
   ∫₀^π |cos θ|^a dθ = √π · Γ((a+1)/2) / Γ(a/2 + 1)
   would close the angular average (with a=1) but is not in Mathlib.

These are tracked in the gallery via the
`AngularAverageData` structure, which packages the two needed
properties (`angularAvg_eq`, `angularAvg_nonneg`) as
structure-encoded assumptions. Per the project's axiom-integrity
policy, `meta.json` correctly reports `axiomCount: 2` and badge
`"axiom"`, status `"axiomatized"`.

---

## Dead Ends

- **Trying to prove the angular average via 2D reduction**:
  doesn't work because the identity is intrinsically n-dimensional
  (the n=2 case is essentially the only one Mathlib can do directly,
  and that's what `BuffonsNeedleOQ01OQ01.lean` already does).
- **Replacing the structure with `axiom` declarations**: would
  not change the assumption count and would worsen the axiom-count
  reporting (per project policy structures are preferred when the
  assumption is naturally a "data + property" package).

---

## Remaining Work (Tracked, Not Blocking Completion)

- Higher dimensions (n ≥ 5): `sphereArea_four = 8π²/3`,
  `sphereArea_five = π³`, `cauchyCrofton_five = 3/8`,
  `cauchyCrofton_six = 16/(15π)`. Easy follow-on; not done here
  to keep this audit purely metadata-level under disk pressure
  (no Docker build available this session).
- Decay theorem: `cauchyCroftonConst n → 0` as `n → ∞`.
  Reduces to `Γ` asymptotics (Stirling).
- Mathlib upstream contribution: spherical Haar measure +
  spherical change-of-variables would unlock not just this proof
  but many integral-geometry results.

---

## Status

**COMPLETED** at the appropriate endpoint: axiomatized
formalization with two structure-encoded assumptions, both
documented as Mathlib gaps. No remaining sorries; no `axiom`
declarations; gallery entry shipped with badge `"axiom"`.

This audit (researcher-4, 2026-04-27) reconciled the stale
candidate-pool entry (which still showed "OBSERVE / iteration 1")
with the actual state of the work.
