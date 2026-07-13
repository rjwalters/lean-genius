# Knowledge Base: area-of-circle-oq-03-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Archimedes' half-angle doubling method for computing π, formalized constructively in
`Proofs/AreaOfCircleOQ03OQ02OQ01.lean`. Core entry (doubling radicals, hexagon seed,
nested-radical realization, monotonicity/upper bound/convergence, and an explicit
`O(1/m²)` rate) was already complete and 0-axiom. Two open questions remained: (1) recover
the rational `223/71` bound from the doubling recurrence without `pi_gt_d4`; (2) sharpen the
convergence-rate constant `7/32 → 1/6`.

---

## Insights

- **Open question 2 is resolved by NOT being lossy.** The existing `pi_sub_halfPerimeter_le`
  proves `π − p(m) ≤ (7/32)π³/m²` by taking `Real.sin_bound`
  (`sin x ≥ x − x³/6 − (5/96)x⁴`) and absorbing `x⁴ ≤ x³` into the cubic term
  (`1/6 + 5/96 = 7/32`). Keeping the quartic remainder **separate** and scaling by `m`
  (`m·x = π`, `m·x³ = π³/m²`, `m·x⁴ = π⁴/m³`) gives the sharp two-term bound
  `π − p(m) ≤ π³/(6m²) + (5/96)·π⁴/m³` with the **exact** leading coefficient `1/6`
  (`pi_sub_halfPerimeter_le_sharp`).
- **Factored "1/6 + o(1)" form**: `π − p(m) ≤ (π³/(6m²))·(1 + 5π/(16m))`
  (`pi_sub_halfPerimeter_le_sharp_factored`) — the bracket `→ 1`, so the second-order
  coefficient is exactly `1/6`. Derived from the two-term bound by a single algebraic
  identity (`field_simp; ring`) and `le.trans_eq`.
- **Consistency**: for `m ≥ 4` one has `π/m ≤ 1`, so `(5/96)π⁴/m³ ≤ (5/96)π³/m²` and the
  sharp bound collapses to the earlier `7/32` bound — the old result is the `m ≥ 4`
  specialization of the new one.

## Reusable techniques

- **Don't pre-absorb Taylor remainders if you want the sharp constant.** Scaling each Taylor
  term by `m` separately preserves the exact leading coefficient; absorbing `xⁿ⁺¹ ≤ xⁿ`
  (valid for `x ≤ 1`) is only for a single-term bound and inflates the constant.
- **`m`-scaling identities in one shot**: `have key : (m:ℝ)*(x - x³/6 - x⁴*(5/96)) = π - π³/(6m²) - (5/96)π⁴/m³ := by rw [hx]; field_simp`. With `x = π/m` and `m ≠ 0`, `field_simp` alone closes it (do NOT append `ring` — it errors with "No goals").
- `Real.sin_bound (hx : |x| ≤ 1) : |sin x − (x − x³/6)| ≤ |x|⁴·(5/96)`; combine
  `abs_of_pos` + `(abs_le.mp …).1` to extract the lower bound.

---

## Dead Ends

- Appending `ring` after `field_simp` on the `key` `m`-scaling identity fails with
  "No goals to be solved" — `field_simp` fully discharges that particular goal. (The
  factored-form `heq` identity, by contrast, does need the trailing `ring`.)

---

## Session log

- **2026-06-30 (researcher-3)**: Added `pi_sub_halfPerimeter_le_sharp` and
  `pi_sub_halfPerimeter_le_sharp_factored` (answers open question 2). File now 329 LOC,
  11 thm, 1 def, 0 axiom, 0 sorry. Slug is depth-3 (`-oq-03-oq-02-oq-01`) → no new OQ
  children proposed; enriched the existing entry in place. Verified host `lake env lean`
  (docker down), `#print axioms` = propext/Classical.choice/Quot.sound only.
