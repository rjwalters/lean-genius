# Current State

**Phase**: ACT (post-S3 DISCHARGE)
**Since**: 2026-05-12T16:35Z
**Iteration**: 4 (S3 just completed; S4 is next)

## Current Focus

Approach A (biquadratic-limit removable-singularity identity, OQ-02.c)
fully discharged in `proofs/Proofs/GeneralQuartic.lean` (Part VI.5). The
S2 `sorry` on `ferrari_biquad_limit` is now closed; the file's sorry
count is 0.

## Active Approach

**Approach A** (OQ-02.c) — Biquadratic-limit symbolic identity.
Discharged via:

- Sub-step A: `∃ u, u² = r` (FTA on `X² + C(-r)`), then case-split on
  whether `m₁ = -p + u` is non-degenerate. Otherwise `r = p²/4` forces
  `p ≠ 0`, and `m₂ = -p - u = -3p/2` is non-degenerate.
- Sub-step B: `ferrari_roots_are_roots` + `biquadratic_simple` (each
  Ferrari root squared automatically lands in the biquadratic root pair).

Approaches B (OQ-02.a witness family) and C (OQ-02.b conditioning bound)
remain deferred — see `knowledge.md`.

## Blockers

None for S4. Next-action candidates listed below.

## Next Action

**S4 candidate menu** (highest-leverage first):

1. **Galois-theoretic context expansion** (gallery-only): add a
   `relatedProofs` cross-reference from `general-quartic` to
   `abel-ruffini` and `solution-of-cubic` (and back). Update
   `crossReferences` in `src/data/proofs/general-quartic/meta.json` with
   a fourth entry tying the S₄ solvable derived series to the
   resolvent-cubic depression. **Pure docs**, low collision risk.

2. **OQ-02.a witness scaffold** (Lean SCAFFOLD, defer proof): state
   `∃ (p_t q_t r_t : ℝ → ℂ) (continuous), tendsto (β t) atTop atTop`
   where `β t := q t / (2 * Complex.cpow (2 * m₀ t + p t) (1/2 : ℂ))`
   and `m₀ t` is a continuous resolvent-root selection. The actual
   asymptotic-rate proof remains deferred (requires `Filter.Tendsto`
   plumbing); just stating the candidate witness family is ≤ 40 LOC.

3. **Mathlib gap audit**: survey Mathlib for `Polynomial.discriminant`
   (cubic specifically), `Complex.cpow_two_eq_self`, and
   `Filter.IsLittleO`-style asymptotic comparison for parameter
   families. Produce a tabulated knowledge.md section listing exact
   declaration names that exist vs proposed signatures we'd need.

4. **S3 corollary — quartic biquadratic special case (full)**: bundle
   `ferrari_biquad_limit` with `biquadratic_simple` and
   `depressed_quartic_forward/backward` into a single user-facing
   theorem `quartic_biquadratic_roots`, showing that for the GENERAL
   quartic `x⁴ + ax³ + bx² + cx + d = 0` with depression coefficients
   satisfying `q = 0`, the four roots are `r = -a/4 ± √z` with
   `z ∈ {(-p + √(p² − 4r))/2, (-p − √(p² − 4r))/2}`. ~30 LOC, no new
   axioms.

**Recommendation**: S4 picks (1) or (4) for a tight gallery-facing
deliverable. (2) is more ambitious; defer unless filter API survey
(3) shows the asymptotic plumbing is tractable.

## Attempt Counts

- Total attempts: 3 (S1 OBSERVE — markdown survey + JSON scaffold;
  S2 SCAFFOLD — 2 helper lemmas proved + main statement scaffolded;
  S3 DISCHARGE — `ferrari_biquad_limit` proved, 1 sorry removed)
- Current approach attempts: 2 (S2 SCAFFOLD + S3 DISCHARGE)
- Approaches tried: 1 (Approach A discharged; B and C remain deferred)
