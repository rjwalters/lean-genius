# Problem: Buffon's Noodle (OQ-01-OQ-01-OQ-01-OQ-02) — Additivity of Expected Crossings over Concatenation

**Slug**: buffons-needle-oq-01-oq-01-oq-01-oq-02
**Lean file**: `proofs/Proofs/BuffonsNeedleOQ01OQ01OQ01OQ02.lean`
**Parent**: `buffons-needle-oq-01-oq-01-oq-01` (axiom-free smooth Buffon–Barbier)

## Origin

This slug was minted by the seeker as an open-question descendant of
`BuffonsNeedleOQ01OQ01OQ01.lean` but shipped with no problem statement. The
statement below is **derived** from the parent during this research session.

## The Parent

`BuffonsNeedleOQ01OQ01OQ01.lean` proves the Buffon–Barbier formula, axiom-free,
for an arbitrary C¹ curve γ : ℝ → ℝ × ℝ on [a, b]:

  concreteSmoothExpectedCrossings γ a b d = 2 · arcLength(γ) / (π · d),

where the concrete expected-crossing functional is the double integral

  concreteSmoothExpectedCrossings γ a b d
    = (1/(π·d)) · ∫_a^b ∫_0^π |γ'ₓ(t)·sin θ + γ'_y(t)·cos θ| dθ dt.

The parent fixes the *value* of the functional. It never records the
structural property that drives Barbier's classical argument.

## Derived Open Question

Prove that the expected-crossing functional is **additive over concatenation of
the parameter interval**:

1. (split)     `E(γ, a, b, d) = E(γ, a, c, d) + E(γ, c, b, d)`
2. (partition) `E(γ, pts m, pts n, d) = Σ_{k=m}^{n-1} E(γ, pts k, pts (k+1), d)`

with the minimal integrability hypotheses on the angular integrand stated
explicitly. This is the formal "a noodle is a sum of needles" decomposition;
combined with the parent's shape-independence it gives a second route to
Barbier's constant 2/(π·d).

## Approach

The inner angular integral and the constant 1/(π·d) are inert; additivity is a
direct consequence of additivity of the *outer* interval integral. Key Mathlib:
`intervalIntegral.integral_add_adjacent_intervals` (two pieces),
`intervalIntegral.sum_integral_adjacent_intervals_Ico` (n pieces),
`Finset.mul_sum`, `IntervalIntegrable.trans`, `Continuous.intervalIntegrable`.

## Tractability: HIGH (structural lemma, routine once stated)
