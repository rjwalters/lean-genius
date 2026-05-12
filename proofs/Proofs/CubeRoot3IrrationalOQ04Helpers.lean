/-
Proof: Cubing-bound helpers for the simple continued fraction of cbrt3.
Date: 2026-05-12 (S5-prep)
Research: cube-root-3-irrational-oq-04, helper extraction (researcher-1)

Two reusable biconditional helpers that condense the
"by_contra + cube + nlinarith" template used in S2/S3/S4 of
`CubeRoot3IrrationalOQ04.lean`, plus the new S5 lower bound
`23/16 < cbrt3` as a one-line demonstration.

This file is independent of `CubeRoot3IrrationalOQ04.lean`: it only
depends on `cbrt3` and `cbrt3_cubed` from
`Proofs/CubeRoot3Irrational.lean`, so subsequent partial-quotient
iterations (S5, S6, …) can import it without circular dependencies.
-/

import Proofs.CubeRoot3Irrational
import Mathlib

/-!
# Cubing-bound helpers for ∛3

For any nonnegative `q : ℝ`, comparing `q` against `∛3` is equivalent
to comparing `q³` against `3`. Formalizing this once as a
biconditional reduces every subsequent partial-quotient cubing-bound
lemma to a single `norm_num` after the iff rewrite.

## Helpers exposed

```
cbrt3_nonneg                : (0 : ℝ) ≤ cbrt3
cbrt3_pos                   : (0 : ℝ) < cbrt3
lt_cbrt3_iff_cube_lt        : 0 ≤ q → (q < cbrt3 ↔ q^3 < 3)
cbrt3_lt_iff_three_lt_cube  : 0 ≤ q → (cbrt3 < q ↔ 3 < q^3)
```

Each `aᵢ` partial-quotient lemma (S2 onward) needs two cubing
bounds of the form `p/q < cbrt3` and `cbrt3 < r/s`. With these
helpers the proofs become:

```lean
theorem p_q_lt_cbrt3 : (p / q : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]; norm_num

theorem cbrt3_lt_r_s : cbrt3 < (r / s : ℝ) := by
  rw [cbrt3_lt_iff_three_lt_cube (by norm_num)]; norm_num
```

instead of the ~14-line `by_contra + cube + nlinarith` block.

## Proof technique

The forward (strict) direction uses the polynomial factorization

  `b^3 - a^3 = (b - a) * (b^2 + b*a + a^2)`,

with the second factor strictly positive whenever `b > 0` (hence the
auxiliary `cbrt3_pos` lemma). The backward direction is symmetric
by contradiction.

The factorization sidesteps the `pow_lt_pow_left` / `pow_le_pow_left`
API drift documented in the gallery: only `ring`, `linarith`,
`mul_pos`, `mul_nonneg`, `sub_pos`, `sub_nonneg`, and `sq_nonneg` are
used.

## Demonstration

A single new cubing bound — the S5 lower bound

```
twenty_three_sixteenths_lt_cbrt3 : (23/16 : ℝ) < cbrt3
```

(cube target `12167/4096 < 12288/4096 = 3`) is proved in two lines
to exercise the helper. The S2/S3/S4 bounds
(`four_thirds_lt_cbrt3`, `cbrt3_lt_three_halves`,
`ten_sevenths_lt_cbrt3`, `cbrt3_lt_thirteen_ninths`) already exist
in `CubeRoot3IrrationalOQ04.lean` under the manual template; this
file does not duplicate them.

No axioms; depends only on `CubeRoot3Irrational.cbrt3_cubed`.
-/

namespace Cbrt3Helpers

open CubeRoot3Irrational

/-- `∛3 ≥ 0`. Immediate from the `rpow` definition: real powers of a
non-negative base are non-negative. -/
theorem cbrt3_nonneg : (0 : ℝ) ≤ cbrt3 := by
  unfold cbrt3
  exact Real.rpow_nonneg (by norm_num) _

/-- `∛3 > 0`. If `cbrt3 = 0` then `cbrt3³ = 0`, contradicting
`cbrt3³ = 3`. -/
theorem cbrt3_pos : (0 : ℝ) < cbrt3 := by
  rcases lt_or_eq_of_le cbrt3_nonneg with h | h
  · exact h
  · exfalso
    have hc := cbrt3_cubed
    rw [← h] at hc
    norm_num at hc

/-- **Cube comparison, lower direction**:
for nonnegative `q`, `q < ∛3 ↔ q³ < 3`.

Both directions use the polynomial factorization
`b³ - a³ = (b - a)(b² + b·a + a²)`. The forward direction needs
`b² + b·a + a² > 0`, which follows from `cbrt3 > 0`. The backward
direction needs only `≥ 0`, which is immediate from nonnegativity. -/
theorem lt_cbrt3_iff_cube_lt {q : ℝ} (hq : 0 ≤ q) :
    q < cbrt3 ↔ q ^ 3 < 3 := by
  constructor
  · -- Forward: q < cbrt3 ⟹ q³ < cbrt3³ = 3.
    intro hqlt
    have hc : 0 < cbrt3 := cbrt3_pos
    have h2 : q ^ 3 < cbrt3 ^ 3 := by
      have eq : cbrt3 ^ 3 - q ^ 3
              = (cbrt3 - q) * (cbrt3 ^ 2 + cbrt3 * q + q ^ 2) := by ring
      have e1 : 0 < cbrt3 - q := sub_pos.mpr hqlt
      have e2 : 0 < cbrt3 ^ 2 + cbrt3 * q + q ^ 2 := by
        have hc2 : 0 < cbrt3 ^ 2 := pow_pos hc 2
        have hcq : 0 ≤ cbrt3 * q := mul_nonneg hc.le hq
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        linarith
      have hp := mul_pos e1 e2
      linarith [eq]
    rw [cbrt3_cubed] at h2
    exact h2
  · -- Backward: q³ < 3 = cbrt3³ ⟹ q < cbrt3 (by contradiction).
    intro hcube
    by_contra h
    push_neg at h  -- `cbrt3 ≤ q`
    have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
    have h2 : cbrt3 ^ 3 ≤ q ^ 3 := by
      have eq : q ^ 3 - cbrt3 ^ 3
              = (q - cbrt3) * (q ^ 2 + q * cbrt3 + cbrt3 ^ 2) := by ring
      have e1 : 0 ≤ q - cbrt3 := sub_nonneg.mpr h
      have e2 : 0 ≤ q ^ 2 + q * cbrt3 + cbrt3 ^ 2 := by
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        have hqc : 0 ≤ q * cbrt3 := mul_nonneg hq hp
        have hc2 : 0 ≤ cbrt3 ^ 2 := sq_nonneg cbrt3
        linarith
      have hprod := mul_nonneg e1 e2
      linarith [eq]
    rw [cbrt3_cubed] at h2
    linarith

/-- **Cube comparison, upper direction**:
for nonnegative `q`, `∛3 < q ↔ 3 < q³`.

Symmetric to `lt_cbrt3_iff_cube_lt`. -/
theorem cbrt3_lt_iff_three_lt_cube {q : ℝ} (hq : 0 ≤ q) :
    cbrt3 < q ↔ 3 < q ^ 3 := by
  constructor
  · -- Forward: cbrt3 < q ⟹ cbrt3³ = 3 < q³.
    intro hqlt
    have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
    have hc : 0 < cbrt3 := cbrt3_pos
    have h2 : cbrt3 ^ 3 < q ^ 3 := by
      have eq : q ^ 3 - cbrt3 ^ 3
              = (q - cbrt3) * (q ^ 2 + q * cbrt3 + cbrt3 ^ 2) := by ring
      have e1 : 0 < q - cbrt3 := sub_pos.mpr hqlt
      have e2 : 0 < q ^ 2 + q * cbrt3 + cbrt3 ^ 2 := by
        have hc2 : 0 < cbrt3 ^ 2 := pow_pos hc 2
        have hqc : 0 ≤ q * cbrt3 := mul_nonneg hq hc.le
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        linarith
      have hprod := mul_pos e1 e2
      linarith [eq]
    rw [cbrt3_cubed] at h2
    exact h2
  · -- Backward: 3 < q³ ⟹ cbrt3 < q (by contradiction).
    intro hcube
    by_contra h
    push_neg at h  -- `q ≤ cbrt3`
    have hp : (0 : ℝ) ≤ cbrt3 := cbrt3_nonneg
    have h2 : q ^ 3 ≤ cbrt3 ^ 3 := by
      have eq : cbrt3 ^ 3 - q ^ 3
              = (cbrt3 - q) * (cbrt3 ^ 2 + cbrt3 * q + q ^ 2) := by ring
      have e1 : 0 ≤ cbrt3 - q := sub_nonneg.mpr h
      have e2 : 0 ≤ cbrt3 ^ 2 + cbrt3 * q + q ^ 2 := by
        have hc2 : 0 ≤ cbrt3 ^ 2 := sq_nonneg cbrt3
        have hcq : 0 ≤ cbrt3 * q := mul_nonneg hp hq
        have hq2 : 0 ≤ q ^ 2 := sq_nonneg q
        linarith
      have hprod := mul_nonneg e1 e2
      linarith [eq]
    rw [cbrt3_cubed] at h2
    linarith

/-! ## S5 prep: new lower bound for `a₃ = 1`

The fourth partial-quotient identity `cbrt3_a3 = 1` (deferred to
S5+ per the `CubeRoot3IrrationalOQ04.lean` next-action) requires
bounds `23/16 < cbrt3 ≤ 13/9`. The upper bound is the S4-proved
`cbrt3_lt_thirteen_ninths` (in `CubeRoot3IrrationalOQ04`); the
new lower bound `23/16 < cbrt3` is proved here, as a demonstration
of the helper's brevity.

Cube target: `(23/16)³ = 12167/4096 < 12288/4096 = 3`, strict
(`12167 < 12288 = 4096 · 3`). -/

/-- `23/16 < ∛3`. Cube target: `(23/16)³ = 12167/4096 < 12288/4096 = 3`.

Two-line proof via `lt_cbrt3_iff_cube_lt`. Compare to the four-step
`by_contra + nlinarith` proof of `four_thirds_lt_cbrt3` /
`ten_sevenths_lt_cbrt3` in `CubeRoot3IrrationalOQ04.lean`. -/
theorem twenty_three_sixteenths_lt_cbrt3 : (23 / 16 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

end Cbrt3Helpers
