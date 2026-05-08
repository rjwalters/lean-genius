# Current State

**Phase**: ACT
**Since**: 2026-05-08
**Iteration**: 4

## Current Focus

Discharging the **first half** of the van der Poorten denominator
analysis (route F): proving
  `∃ m : ℤ, (lcmRange n)^3 · H_n^{(3)} = m`,
i.e. the cubed-harmonic-sum half of `denominator_control`.

## Active Approach

**Route (F)**: van der Poorten closed form for `aperyA n`.

Session 4 (this session) discharged the H_n^{(3)} half:

- Proved `harmonicCubed_lcm_clear_nat`: explicit identity
  `(lcmRange n)^3 · H_n^{(3)} = (∑ k ∈ range n, (lcmRange n)^3 / (k+1)^3 : ℕ)`,
  per-term via `Nat.cast_div` + `pow_dvd_lcmRange_pow` (Part 2).
- Derived `harmonicCubed_lcm_clear`: existential `∃ m : ℤ, …` form
  matching the shape of `denominator_control`.

The next sessions will tackle the alternating-bilinear "second
summand" (the `cnk(n,k)` half) and the closed-form expansion of
`aperyA n`.

## Blockers

None for the H_n^{(3)} half (now proved).

For the full `denominator_control`, the remaining infrastructure is:
1. `vdpAlternatingSum_lcm_clear`: clear denominators in
   `∑_{k=0}^{n} ∑_{m=1}^{k} (-1)^{m-1}/(2 m^3 C(n,m) C(n+m,m))`
   via the central-binomial telescoping identity.
2. `aperyA_explicit_formula`: state and validate (numerically)
   the vdP closed form.

## Next Action

Session 5: stub `vdpAlternatingSum_lcm_clear` with the
classical denominator telescoping identity. Begin with the
binomial-denominator divisibility lemma
  `m · C(n, m) ∣ lcmRange n`.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 1 (route F, session 4 succeeded)
- Approaches tried: 2 (recurrence-induction ruled out via
  cancellation gap analysis in session 1; van der Poorten closed
  form being executed in sessions 2-4+)
