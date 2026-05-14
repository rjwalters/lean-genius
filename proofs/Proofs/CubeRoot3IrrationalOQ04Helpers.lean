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

/-! ## S6 prep: new bounds for `a₄ = 4`

The fifth partial-quotient identity `cbrt3_a4 = 4` requires the
two-sided tight sandwich

  `62/43 < cbrt3 < 75/52`

— the fifth and (semi-)sixth convergents of the simple CF
`[1; 2, 3, 1, 4, …]` of OEIS A002945. Both boundaries are within
~10⁻³ of `3` after cubing.

Cube targets:

  `(62/43)³ = 238328/79507 < 238521/79507 = 3`   (strict, diff 193).
  `(75/52)³ = 421875/140608 > 421824/140608 = 3` (strict, diff 51).

Two-line proofs each via the cubing-iff helpers. -/

/-- `62/43 < ∛3`. Cube target: `(62/43)³ = 238328/79507 < 238521/79507 = 3`
(strict: `238328 < 3 · 79507 = 238521`). The fifth convergent of the
simple CF of `∛3`. -/
theorem sixty_two_over_forty_three_lt_cbrt3 : (62 / 43 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

/-- `∛3 < 75/52`. Cube target: `(75/52)³ = 421875/140608 > 421824/140608 = 3`
(strict: `3 · 140608 = 421824 < 421875`). The semi-convergent of the
simple CF of `∛3` corresponding to `a₄ = 4`. -/
theorem cbrt3_lt_seventy_five_over_fifty_two : cbrt3 < (75 / 52 : ℝ) := by
  rw [cbrt3_lt_iff_three_lt_cube (by norm_num)]
  norm_num

/-! ## S7 prep: new lower bound for `a₅ = 1`

The sixth partial-quotient identity `cbrt3_a5 = 1` requires the
two-sided sandwich

  `437/303 < cbrt3 < 75/52`

— the upper bound is the S6 helper `cbrt3_lt_seventy_five_over_fifty_two`
above; the new lower bound `437/303 < cbrt3` is the sixth convergent
`p₆/q₆ = 437/303` of the simple CF `[1; 2, 3, 1, 4, 1, …]` of OEIS
A002945 (here `a₅ = 1`). After cubing, the sandwich

  `(437/303)³ = 83453453/27818127 < 3 = 83454381/27818127`
  `(75/52)³  =  421875/140608   > 3 =  421824/140608`

is tighter than S6's `62/43 < cbrt3 < 75/52` (gap `2.4·10⁻³`) on the
lower side: the new lower cube gap `928/27818127 ≈ 3.3·10⁻⁵` is about
two orders of magnitude tighter, consistent with `437/303` being the
sixth convergent.

Two-line proof via the cubing-iff helper. -/

/-- `437/303 < ∛3`. Cube target: `(437/303)³ = 83453453/27818127
< 83454381/27818127 = 3` (strict: `3 · 27818127 = 83454381 > 83453453`,
gap `928`). The sixth convergent of the simple CF of `∛3`. -/
theorem four_thirty_seven_over_three_oh_three_lt_cbrt3 :
    (437 / 303 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

/-! ## S8 prep: new upper bound for `a₆ = 5`

The seventh partial-quotient identity `cbrt3_a6 = 5` requires the
two-sided sandwich

  `437/303 < cbrt3 < 512/355`

— the lower bound is the S7 helper `four_thirty_seven_over_three_oh_three_lt_cbrt3`
above (reused unchanged); the new upper bound `cbrt3 < 512/355`
is the seventh convergent `p₇/q₇ = 512/355` of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, …]` of OEIS A002945. The convergent
recursion `p_n = a_n · p_{n-1} + p_{n-2}` with `a₇ = 1` gives

  `q₇ = 1 · q₆ + q₅ = 1 · 303 + 52 = 355`
  `p₇ = 1 · p₆ + p₅ = 1 · 437 + 75 = 512`

(Note: `2260/1567 = (5·437+75)/(5·303+52)` would be a semi-convergent
testing the value `a₇ = 5`, but the actual `a₇ = 1` per OEIS A002945.
The seventh convergent is `512/355`, which lies on the *upper* side
of `cbrt3` alternating with the lower-side `437/303`.)

After cubing,

  `(512/355)³ = 134217728/44738875`
  `3          = 134216625/44738875`

so `512³ = 134_217_728 > 134_216_625 = 3 · 355³` (strict, diff
`1103`). Note `512 = 2⁹`, so `512³ = 2²⁷ = 134_217_728` exactly. The
new cube gap `1103 / 44_738_875 ≈ 2.5·10⁻⁵` is comparable to S7's
lower-side gap of `928/27818127 ≈ 3.3·10⁻⁵`, both well within
`norm_num`'s reach.

Two-line proof via the cubing-iff helper. -/

/-- `∛3 < 512/355`. Cube target: `(512/355)³ = 134217728/44738875
> 134216625/44738875 = 3` (strict: `3 · 355³ = 134216625 < 512³ = 134217728`,
gap `1103`). Note `512 = 2⁹`, so `512³ = 2²⁷` exactly. The seventh
convergent of the simple CF of `∛3` (using `a₇ = 1` per OEIS A002945). -/
theorem cbrt3_lt_five_twelve_over_three_fifty_five :
    cbrt3 < (512 / 355 : ℝ) := by
  rw [cbrt3_lt_iff_three_lt_cube (by norm_num)]
  norm_num

/-! ## S9 prep: new lower bound for `a₇ = 1`

The eighth partial-quotient identity `cbrt3_a7 = 1` requires the
two-sided tighter sandwich

  `949/658 < cbrt3 < 512/355`

— the upper bound `512/355` is the S8 helper
`cbrt3_lt_five_twelve_over_three_fifty_five` above (reused unchanged);
the new lower bound `949/658 < cbrt3` is the eighth convergent
`p₈/q₈ = 949/658` of the simple CF `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]`
of OEIS A002945. The convergent recursion `p_n = a_n · p_{n-1} + p_{n-2}`
with `a₈ = 1` gives

  `q₈ = 1 · q₇ + q₆ = 1 · 355 + 303 = 658`
  `p₈ = 1 · p₇ + p₆ = 1 · 512 + 437 = 949`

After cubing,

  `(949/658)³ = 854_670_349 / 284_890_312`
  `3          = 854_670_936 / 284_890_312`

so `949³ = 854_670_349 < 854_670_936 = 3 · 658³` (strict, diff `587`).
The new lower cube gap `587 / 284_890_312 ≈ 2.06·10⁻⁶` is roughly
one order of magnitude tighter than S8's upper-side gap of
`1103/44_738_875 ≈ 2.47·10⁻⁵`, consistent with `949/658` being the
even-index eighth convergent (lower side of `cbrt3`), one rung
beyond S8's `437/303`.

(Math correction: an earlier S8 next-action sketch suggested
`2485/1723 = (4·512+437)/(4·355+303)` as the eighth convergent,
computed with `a₈ = 4`. The actual `a₈ = 1` per OEIS A002945
(verified independently by `decimal.Decimal` to 50 digits in S9-prep
PR #19011); the proposed `2485/1723` is in fact *above* `cbrt3`
not below, so a `norm_num` proof of `(2485/1723 : ℝ) < cbrt3` would
have failed. The correct eighth convergent is `949/658`, with
`949³ < 3 · 658³` confirming `949/658 < cbrt3` (below, as expected
for the even-index convergent).)

Two-line proof via the cubing-iff helper. -/

/-- `949/658 < ∛3`. Cube target: `(949/658)³ = 854_670_349/284_890_312
< 854_670_936/284_890_312 = 3` (strict: `3 · 658³ = 854_670_936
> 949³ = 854_670_349`, gap `587`). The eighth convergent of the simple
CF of `∛3` (using `a₈ = 1` per OEIS A002945). -/
theorem nine_forty_nine_over_six_fifty_eight_lt_cbrt3 :
    (949 / 658 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

end Cbrt3Helpers
