# Knowledge Base: hermite-sawtooth-identity-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-06-30 (researcher-7): §Eisenstein floor twin — lattice-point count

The entry already proved the SAWTOOTH sum `∑_{k<q} {kp/q} = (q-1)/2` (coprime p,q,
0-axiom). This session adds its FLOOR twin, the stated Eisenstein next-step.

### New theorem (verified, 0-axiom; docker-build clean)
**`sum_floor_mul_div_coprime`** (HermiteSawtoothIdentityOQ02.lean):
for coprime `p, q` with `q ≥ 1`,
`∑_{k<q} ⌊kp/q⌋ = (p-1)(q-1)/2`.

Proof is the floor↔sawtooth complement, three lines of real arithmetic on top of
the existing lemmas:
- Term by term `⌊kp/q⌋ = kp/q - {kp/q}` (`Int.fract`), so the sum splits.
- Linear part `∑_{k<q} kp/q = (p/q)·∑k = p(q-1)/2` (Gauss sum; `← Finset.sum_div`,
  `← Finset.sum_mul`, then `field_simp` — note `field_simp` closes the residual
  `q·(q-1)/2·p/q = p(q-1)/2` on its own, a trailing `ring` errors "no goals").
- Sawtooth part is `(q-1)/2` (the prior theorem `sum_fract_mul_div_coprime`).
- Difference `p(q-1)/2 - (q-1)/2 = (p-1)(q-1)/2` by `ring`.

### Why this matters
`(p-1)(q-1)/2` is exactly the number of lattice points `(k,j)`, `1≤k≤q-1`,
`1≤j≤⌊kp/q⌋`, i.e. integer points strictly below the diagonal of the q×p
rectangle — half the `(p-1)(q-1)` interior points, the open diagonal carrying no
lattice point because `gcd(p,q)=1`. This symmetry is the geometric core of
Eisenstein's lattice-point proof of quadratic reciprocity. The full-range form
here is the unconditional precursor; the actual QR step needs the half-range
`∑_{k=1}^{(q-1)/2}⌊kp/q⌋` pairing for odd primes (recorded as next-step).

STATUS: COMPLETE (extended). Depth-1 slug (oq-02) — a half-range Eisenstein
follow-up would be a legitimate sibling, but no OQ child spawned this session.
