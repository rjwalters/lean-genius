# Knowledge Base: basel-problem-oq-01-oq-01-oq-02-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: prove the integrality identity
$$
  \exists\, m \in \mathbb{Z},\quad
  \mathrm{lcm}(1,2,\dots,n)^3 \cdot a_n \in m,
$$
where `aₙ` is the Apéry rational sequence
  `aₙ = ∑_{k=0}^n C(n,k)² C(n+k,k)² · cₙₖ`
with
  `cₙₖ = ∑_{m=1}^n 1/m³ + ∑_{m=1}^k (-1)^(m-1)/(2 m³ C(n,m) C(n+m,m))`.

This is one of the five open axioms blocking the unconditional
formalization of Apéry's irrationality of ζ(3) in
`Proofs/BaselProblemOQ01OQ01OQ02.lean` (line 385).

---

## Strategy: Van der Poorten Closed Form (Route F)

Pointwise recurrence-induction is **ruled out** at the n=2→n=4 step
(see "Dead Ends"). The denominator analysis splits cleanly along the
two summands of the closed form:

- **H_n^{(3)} half** (this OQ-02-OQ-02): `(lcmRange n)^3 · H_n^{(3)} ∈ ℤ`.
  Each summand `1/(k+1)^3` clears against `(k+1)^3 ∣ (lcmRange n)^3`
  (via `pow_dvd_lcmRange_pow`).

- **Alternating-bilinear half** (deferred): the `(-1)^(m-1)/(2 m^3
  C(n,m) C(n+m,m))` part. Clears via the central-binomial telescoping
  identity (vdP 1979 §6).

---

## Sessions

### Session 1 (OBSERVE, 2026-04-26)

Surveyed the Apéry literature; identified the van der Poorten path.
Initially proposed line-by-line port of `denominator_control_factorial`,
later corrected (see Dead Ends).

### Session 2 (ORIENT, 2026-05-07)

Built infrastructure lemmas in
`Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean`:
- `dvd_lcmRange`, `pow_dvd_lcmRange_pow`, `cube_dvd_lcmRange_cube`,
  `succ_cube_dvd_lcmRange_succ_cube`,
- numerical witnesses `lcmRange_zero/one/two/three/four/five`.

Corrected session 1's strategy — see Dead Ends.

### Session 3 (ORIENT continued, 2026-05-08)

Added `harmonicCubed` (the cubed-harmonic sum) plus base values,
non-negativity, and monotonicity. Scaffolded
`harmonicCubed_lcm_clear` but Docker build timed out twice; deferred.

### Session 4 (ACT, 2026-05-08)

**Discharged the H_n^{(3)} half.** Proved:

1. `harmonicCubed_lcm_clear_nat (n : ℕ)`:
   ```
   ((lcmRange n : ℕ) : ℚ)^3 * harmonicCubed n
       = ((∑ k ∈ Finset.range n, (lcmRange n)^3 / (k + 1)^3 : ℕ) : ℚ)
   ```
   Each summand is an exact natural-number division because
   `pow_dvd_lcmRange_pow` gives `(k+1)^3 ∣ (lcmRange n)^3` for
   `k+1 ≤ n`.

2. `harmonicCubed_lcm_clear (n : ℕ)`:
   ```
   ∃ m : ℤ, ((lcmRange n : ℕ) : ℚ)^3 * harmonicCubed n = m
   ```
   matches the shape of the parent's `denominator_control` axiom.

**Proof technique**. Per-term identity flow:
  `Finset.mul_sum` → `Nat.cast_sum` → per-term
  `Nat.cast_div hdvd hk1ne` → `mul_one_div` → `push_cast; ring`.
The key is that `Nat.cast_div` requires `(k+1)^3 ∣ (lcmRange n)^3`
which is exactly `pow_dvd_lcmRange_pow`. No `Int.div` casts, no
`Int.cast_div_floor` complications — the proof stays in the
`ℕ ↪ ℚ` chain end-to-end.

**Pedagogical note**. Session 3's planned helper-lemma split was
correct in spirit but needed the helper restated in `push_cast`
normal form (`(↑k + 1)^3` not `((k+1 : ℕ) : ℚ)^3`). Inlining the
helper into the main theorem avoids that form mismatch.

---

## Insights

### From parent problem (`basel-problem-oq-01-oq-01-oq-02`)

`Proofs/BaselProblemOQ01OQ01OQ02.lean` already proves
`denominator_control_factorial : ∃ m : ℤ, (n.factorial : ℚ)^3 * aperyA n = m`
(Part XIX). The factorial proof works because `(n+2)! = (n+2)·(n+1)!`
is **exactly** multiplicative — multiplying through the recurrence by
`(n+1)!^3` produces `(n+2)!^3` on the LHS with no leftover `(n+2)^3`
to absorb. The lcm version has no such factorisation:
`lcm(1..n+2) ≠ (n+2) · lcm(1..n+1)` in general (e.g.
`lcm(1..4) = 12 ≠ 4 · 6 = 24`).

### Sibling file infrastructure

`Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` already provides
`lcmRange_succ`, `lcmRange_dvd_lcmRange_of_le`, `lcmRange_monotone`,
`lcmRange_dvd_factorial`. These cover the basic Nat-arithmetic side;
this file (OQ-02-OQ-02) adds the powered version
`pow_dvd_lcmRange_pow` specifically needed for denominator analysis.

### Mathlib lemmas relied on

- `Mathlib.Data.Nat.GCD.Basic`: `Finset.lcm`, `Finset.dvd_lcm`.
- `Nat.cast_div` (with explicit `n ∣ m` hypothesis, divisorᵠ ≠ 0).
- `pow_dvd_pow_of_dvd`.
- `Finset.mul_sum`, `Finset.sum_congr`, `Finset.mem_range`.

### Watch-outs

- `lcmRange n = (Finset.range n).lcm (· + 1)` so `lcmRange n` covers
  integers 1 through n (not 0 through n-1). `lcmRange 0 = 1`.
- The defining equation `lcmUpTo_dvd_of_le` (in parent) gives
  `lcm(1..n) ∣ lcm(1..m)` for `n ≤ m`.

---

## Dead Ends

### Pointwise recurrence-induction (ruled out 2026-05-07)

With `L = lcmRange (n+2)`, `l = lcmRange (n+1)`, `m = lcmRange n`,
the recurrence rearranges to
  `L^3 · aₙ₊₂ · (n+2)^3 = (L/l)^3 · c · A − (L/m)^3 · (n+1)^3 · B`
where `A = l^3·aₙ₊₁ ∈ ℤ`, `B = m^3·aₙ ∈ ℤ`, `c = aperyRecCoeff(n+1)`.

Concrete failure at n=2→n=4: `L=12, l=6, m=2, c=1463`,
`A = 6^3 · (62531/36) = 375186`, `B = 2^3 · (351/4) = 702`. Each
summand has residue 48 mod (n+2)^3=64; the **difference** has residue 0.

So term-wise (n+2)^3-divisibility fails; only the cancellation closes
integrality. Any direct induction must therefore track numerators
modulo (n+2)^3 — a strengthened invariant tracking p-adic valuations
for each prime ≤ n+2. **Not recommended; route (F) is cleaner.**
