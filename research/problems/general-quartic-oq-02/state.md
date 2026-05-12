# Current State

**Phase**: ACT (post-S2 SCAFFOLD)
**Since**: 2026-05-12T12:30Z
**Iteration**: 3 (S2 just completed; S3 is next)

## Current Focus

Approach A (biquadratic-limit removable-singularity identity, OQ-02.c)
scaffolded in `proofs/Proofs/GeneralQuartic.lean`. Two helper lemmas
proved sorry-free; the main statement `ferrari_biquad_limit` is stated
and `sorry`-marked, to be discharged in S3.

## Active Approach

**Approach A** (OQ-02.c) — Biquadratic-limit symbolic identity. See
`knowledge.md` §"Three Approach Families" → "Approach A" and §"S2 ACT
Notes".

Approaches B (OQ-02.a witness family) and C (OQ-02.b conditioning bound)
remain deferred — see `knowledge.md`.

## Blockers

None for S3. Anticipate that the resolvent-root existence sub-step
(non-`(-p/2)` root) needs a polynomial-degree argument; the algebraic
root-matching sub-step uses `ring` once `α² = 2m + p` and `β = 0` are
established.

## Next Action

**S3 — DISCHARGE**: prove `ferrari_biquad_limit` (currently `sorry` in
`proofs/Proofs/GeneralQuartic.lean`). Decomposition:

1. **Resolvent-root existence at biquadratic limit**: ∀ (p r : ℂ),
   `p ≠ 0 ∨ r ≠ 0 → ∃ m, (resolventCubic p 0 r).eval m = 0 ∧ 2*m + p ≠ 0`.
   Strategy: `m = -p/2` is the *only* root iff `resolventCubic p 0 r = C 8 *
   (X - C(-p/2))^3`. Expand and compare coefficients of `X^2`: LHS has
   `C (20*p)`, RHS has `C (12*p)` (from the `3 * 8 * (-p/2) = -12p` term
   re-signed), giving `20p = -12p`, i.e. `32p = 0`, i.e. `p = 0`. Then
   compare constant coefficients (or `X^0` of `X(X² - r)`) for the
   remaining `p = 0` case to conclude `r = 0`. Therefore `p ≠ 0 ∨ r ≠ 0`
   yields a non-trivial root.

2. **Root-matching at non-trivial `m`**: With `α² = 2m + p ≠ 0` and
   `β = (if α = 0 then 0 else q/(2α)) = 0` (since `q = 0`), each
   `discᵢ = α² − 4(p/2 + m ± β) = α² − 4(p/2 + m)`. Substitute and use
   the resolvent-cubic condition to derive `discᵢ = -α²`, hence
   `sqrtᵢ = Complex.cpow (-α²) (1/2)`. Then expand `yᵢ² = ((±α + sqrtᵢ)/2)²`
   and use `(yᵢ)² + p(yᵢ)² + r = 0` (forward direction of `biquadratic_simple`
   contrapositive — actually use the `biquadratic_simple` characterization
   directly) to conclude `yᵢ² ∈ {z₁, z₂}`.

Target line budget: ≤ 80 LOC for the S3 proof.

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE — markdown survey + JSON scaffold;
  S2 SCAFFOLD — 2 helper lemmas proved + main statement scaffolded)
- Current approach attempts: 1 (S2)
- Approaches tried: 1 (Approach A initiated; B and C remain deferred)
