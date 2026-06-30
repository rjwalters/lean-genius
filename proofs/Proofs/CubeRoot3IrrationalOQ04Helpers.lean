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

/-! ## S10 prep: new upper bound for `a₈ = 1`

The ninth partial-quotient identity `cbrt3_a8 = 1` requires the
two-sided tighter sandwich

  `949/658 < cbrt3 < 6206/4303`

— the lower bound `949/658` is the S9 helper
`nine_forty_nine_over_six_fifty_eight_lt_cbrt3` above (reused
unchanged); the new upper bound `cbrt3 < 6206/4303` is the ninth
convergent `p₉/q₉ = 6206/4303` of the simple CF
`[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, …]` of OEIS A002945. The convergent
recursion `p_n = a_n · p_{n-1} + p_{n-2}` with `a₉ = 6` gives

  `q₉ = 6 · q₈ + q₇ = 6 · 658 + 355 = 4303`
  `p₉ = 6 · p₈ + p₇ = 6 · 949 + 512 = 6206`

After cubing,

  `(6206/4303)³ = 239_020_589_816 / 79_673_526_127`
  `3            = 239_020_578_381 / 79_673_526_127`

so `6206³ = 239_020_589_816 > 239_020_578_381 = 3 · 4303³` (strict,
diff `11_435`). The new upper cube gap
`11_435 / 79_673_526_127 ≈ 1.43·10⁻⁷` is roughly one order of
magnitude tighter than S9's lower-side gap of
`587/284_890_312 ≈ 2.06·10⁻⁶`, consistent with `6206/4303` being the
odd-index ninth convergent (upper side of `cbrt3`), one rung beyond
S8's `512/355`.

(Note on the convergent recursion direction: per
`feedback_researcher_cf_convergent_recursion_direction_trap` and the
S7/S8 math-correction history in `CubeRoot3IrrationalOQ04.lean`, the
9th convergent computed at the point of proving `a₈` uses `a₉` (the
*next* partial quotient), not `a₈`. Per OEIS A002945, `a₉ = 6`,
giving `p₉/q₉ = 6206/4303`. Pre-claim Python sanity check:
`6206³ = 239_020_589_816`, `3·4303³ = 239_020_578_381`, diff
`+11_435 > 0` confirming `(6206/4303)³ > 3`, hence
`6206/4303 > cbrt3` as required for an upper bound.)

Two-line proof via the cubing-iff helper. -/

/-- `∛3 < 6206/4303`. Cube target: `(6206/4303)³ =
239_020_589_816 / 79_673_526_127 > 239_020_578_381 / 79_673_526_127
= 3` (strict: `3 · 4303³ = 239_020_578_381 < 6206³ =
239_020_589_816`, gap `11_435`). The ninth convergent of the simple
CF of `∛3` (using `a₉ = 6` per OEIS A002945). -/
theorem cbrt3_lt_six_two_oh_six_over_four_three_oh_three :
    cbrt3 < (6206 / 4303 : ℝ) := by
  rw [cbrt3_lt_iff_three_lt_cube (by norm_num)]
  norm_num

/-! ## S11 prep: new lower bound for `a₉ = 6` (the tenth partial quotient)

The tenth CF convergent of `∛3` (using `a₁₀ = 1` per OEIS A002945) is
`p₁₀/q₁₀ = (a₁₀·p₉ + p₈) / (a₁₀·q₉ + q₈) = (1·6206 + 949) / (1·4303 + 658)
= 7155/4961`.

This convergent is even-index, so it lies on the LOWER side of `∛3`
(alternating with the upper-side ninth convergent `6206/4303` from
S10).

Convergent recursion (with `a₁₀ = 1`):

  `q₁₀ = 1 · q₉ + q₈ = 1 · 4303 + 658 = 4961`
  `p₁₀ = 1 · p₉ + p₈ = 1 · 6206 + 949 = 7155`

After cubing,

  `(7155/4961)³ = 366_293_248_875 / 122_097_755_681`
  `3            = 366_293_267_043 / 122_097_755_681`

so `7155³ = 366_293_248_875 < 366_293_267_043 = 3 · 4961³` (strict,
diff `18_168`). The new lower cube gap
`18_168 / 122_097_755_681 ≈ 1.488·10⁻⁷` is slightly tighter than
S10's upper-side gap of `11_435 / 79_673_526_127 ≈ 1.43·10⁻⁷`,
consistent with `7155/4961` being the even-index tenth convergent
(lower side of `cbrt3`), one rung beyond S10's `6206/4303`.

(Note on the convergent recursion direction: per
`feedback_researcher_cf_convergent_recursion_direction_trap` and the
S7/S8 / S8→S9 / S10→S11 math-correction history in
`CubeRoot3IrrationalOQ04.lean`, the 10th convergent computed at the
point of proving `a₉` uses `a₁₀` (the *next* partial quotient), not
`a₉`. Per OEIS A002945, `a₁₀ = 1`, giving `p₁₀/q₁₀ = 7155/4961`.
Pre-claim Python sanity check: `7155³ = 366_293_248_875`,
`3 · 4961³ = 366_293_267_043`, diff `+18_168 > 0` confirming
`(7155/4961)³ < 3`, hence `7155/4961 < cbrt3` as required for a
lower bound. The post-S10 next-action sketch in PR #19420 (doc-only
PREP MATH-CORRECTION) caught and corrected three magnitude errors
in the cube digits before this S11a helper was pasted.)

Two-line proof via the cubing-iff helper. -/

/-- `7155/4961 < ∛3`. Cube target: `(7155/4961)³ =
366_293_248_875 / 122_097_755_681 < 366_293_267_043 / 122_097_755_681
= 3` (strict: `7155³ = 366_293_248_875 < 366_293_267_043 = 3 · 4961³`,
gap `18_168`). The tenth convergent of the simple CF of `∛3` (using
`a₁₀ = 1` per OEIS A002945). -/
theorem seven_one_five_five_over_four_nine_six_one_lt_cbrt3 :
    (7155 / 4961 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

/-! ## S12a prep: new lower bound for `a₁₀ = 2` (the eleventh partial quotient)

The eleventh CF convergent of `∛3` (using `a₁₀ = 2` per OEIS A002945
prefix `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, …]`, 0-indexed) is

  `p₁₀/q₁₀ = (a₁₀·p₉ + p₈) / (a₁₀·q₉ + q₈)`
  `       = (2 · 6206 + 949) / (2 · 4303 + 658)`
  `       = 13361 / 9264`.

This convergent is even-index (10), so it lies on the LOWER side of
`∛3` (alternating with the upper-side ninth convergent `6206/4303`
from S10).

Convergent recursion (with `a₁₀ = 2`):

  `q₁₀ = 2 · q₉ + q₈ = 2 · 4303 + 658 = 9264`
  `p₁₀ = 2 · p₉ + p₈ = 2 · 6206 + 949 = 13361`

After cubing,

  `(13361/9264)³ = 2_385_156_564_881 / 795_052_191_744`
  `3              = 2_385_156_575_232 / 795_052_191_744`

so `13361³ = 2_385_156_564_881 < 2_385_156_575_232 = 3 · 9264³`
(strict, diff `10_351`). The new lower cube gap
`10_351 / 795_052_191_744 ≈ 1.30·10⁻⁸` (relative-to-`3·q³`:
`≈ 4.34·10⁻⁹`) is roughly an order of magnitude tighter than S11a's
lower-side gap of `18_168 / 122_097_755_681 ≈ 1.49·10⁻⁷` — consistent
with `13361/9264` being the true 11th convergent (one rung beyond
S11a's semi-convergent `7155/4961`, which the S11a comment
incorrectly framed as the 10th convergent with `a₁₀ = 1`; the actual
`a₁₀ = 2` per OEIS A002945 entry 11 = 2). The S11a proof
`(7155/4961 : ℝ) < cbrt3` is numerically true regardless — it lands
between the 9th and 11th true convergents — and provided a valid
lower bound for the S11b ACT sandwich proving `cbrt3_a9 = 6`.

(Pre-claim Python sanity check:
`13361³ = 2_385_156_564_881`, `3 · 9264³ = 2_385_156_575_232`,
diff `-10_351 < 0` confirming `(13361/9264)³ < 3`, hence
`13361/9264 < cbrt3` as required for a lower bound. Cross-checked
against OEIS A002945 via Decimal-arithmetic CF expansion of `∛3` to
80 digits; first 15 partial quotients
`[1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3]` match independently.)

Two-line proof via the cubing-iff helper. -/

/-- `13361/9264 < ∛3`. Cube target: `(13361/9264)³ =
2_385_156_564_881 / 795_052_191_744 < 2_385_156_575_232 / 795_052_191_744
= 3` (strict: `13361³ = 2_385_156_564_881 < 2_385_156_575_232 =
3 · 9264³`, gap `10_351`). The eleventh convergent of the simple CF
of `∛3` (using `a₁₀ = 2` per OEIS A002945). -/
theorem one_three_three_six_one_over_nine_two_six_four_lt_cbrt3 :
    (13361 / 9264 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

/-! ## S12b prep: new upper bound for the eleventh partial quotient (the twelfth convergent)

The twelfth CF convergent of `∛3` (using `a₁₁ = 5` per OEIS A002945
prefix `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, …]`, 0-indexed) is

  `p₁₁/q₁₁ = (a₁₁·p₁₀ + p₉) / (a₁₁·q₁₀ + q₉)`
  `       = (5 · 13361 + 6206) / (5 · 9264 + 4303)`
  `       = 73011 / 50623`.

This convergent is odd-index (11), so it lies on the UPPER side of
`∛3` (alternating with the lower-side eleventh convergent `13361/9264`
from S12a).

Convergent recursion (with `a₁₁ = 5`):

  `q₁₁ = 5 · q₁₀ + q₉ = 5 · 9264 + 4303 = 50623`
  `p₁₁ = 5 · p₁₀ + p₉ = 5 · 13361 + 6206 = 73011`

After cubing,

  `(73011/50623)³ = 389_192_883_500_331 / 129_730_961_154_367`
  `3              = 389_192_883_463_101 / 129_730_961_154_367`

so `73011³ = 389_192_883_500_331 > 389_192_883_463_101 = 3 · 50623³`
(strict, diff `+37_230`). The new upper cube gap
`37_230 / 129_730_961_154_367 ≈ 2.87·10⁻¹⁰` is roughly two orders
of magnitude tighter than S10's upper-side gap of
`11_435 / 79_673_526_127 ≈ 1.44·10⁻⁷` — consistent with `73011/50623`
being the next true upper convergent two rungs beyond `6206/4303`.

(Pre-claim Python sanity check (this S12b session):
`73011³ = 389_192_883_500_331`, `3 · 50623³ = 389_192_883_463_101`,
diff `+37_230 > 0` confirming `(73011/50623)³ > 3`, hence
`73011/50623 > cbrt3` as required for an upper bound. **Math-correction
precedent #FIVE** for this slug: the post-S12a `nextAction` sketch
in `state.md` and JSON `currentState.nextAction` claimed
`73011³ - 3·50623³ = +64_599_490`. The actual value is `+37_230`
(off by a factor of ~1734×). The DIRECTION of the bound
(`73011/50623 > cbrt3`, valid upper bound for proving
`cbrt3_a10 = 2`) is unchanged. Cross-checked against OEIS A002945
via Decimal-arithmetic CF expansion of `∛3` to 200 digits; first
20 partial quotients
`[1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4]`
match independently.)

Two-line proof via the cubing-iff helper. -/

/-- `∛3 < 73011/50623`. Cube target: `(73011/50623)³ =
389_192_883_500_331 / 129_730_961_154_367 > 389_192_883_463_101 /
129_730_961_154_367 = 3` (strict: `73011³ = 389_192_883_500_331 >
389_192_883_463_101 = 3 · 50623³`, gap `+37_230`). The twelfth
convergent of the simple CF of `∛3` (using `a₁₁ = 5` per OEIS
A002945). -/
theorem cbrt3_lt_seven_three_oh_one_one_over_five_oh_six_two_three :
    cbrt3 < (73011 / 50623 : ℝ) := by
  rw [cbrt3_lt_iff_three_lt_cube (by norm_num)]
  norm_num

/-! ## S13 prep: new lower bound for `a₁₁ = 5` (the twelfth partial quotient)

The thirteenth CF convergent of `∛3` (using `a₁₂ = 8` per OEIS A002945
prefix `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, …]`, 0-indexed) is

  `p₁₂/q₁₂ = (a₁₂·p₁₁ + p₁₀) / (a₁₂·q₁₁ + q₁₀)`
  `       = (8 · 73011 + 13361) / (8 · 50623 + 9264)`
  `       = 597449 / 414248`.

This convergent is even-index (12), so it lies on the LOWER side of
`∛3` (alternating with the upper-side twelfth convergent `73011/50623`
from S12b).

Convergent recursion (with `a₁₂ = 8`):

  `q₁₂ = 8 · q₁₁ + q₁₀ = 8 · 50623 + 9264 = 414248`
  `p₁₂ = 8 · p₁₁ + p₁₀ = 8 · 73011 + 13361 = 597449`

After cubing,

  `(597449/414248)³ = 213_256_617_080_909_849 / 71_085_539_027_220_992`
  `3                = 213_256_617_081_662_976 / 71_085_539_027_220_992`

so `597449³ = 213_256_617_080_909_849 < 213_256_617_081_662_976 =
3 · 414248³` (strict, diff `-753_127`). The new lower cube gap
`753_127 / 71_085_539_027_220_992 ≈ 1.06·10⁻¹¹` (relative-to-`3·q³`:
`≈ 3.53·10⁻¹²`) is roughly an order of magnitude tighter than S12b's
upper-side gap of `37_230 / 129_730_961_154_367 ≈ 2.87·10⁻¹⁰` —
consistent with `597449/414248` being the next true convergent one
rung beyond `73011/50623`.

(Pre-claim Python sanity check (this S13 session):
`597449³ = 213_256_617_080_909_849`, `3 · 414248³ =
213_256_617_081_662_976`, diff `-753_127 < 0` confirming
`(597449/414248)³ < 3`, hence `597449/414248 < cbrt3` as required
for a lower bound. Cross-checked against OEIS A002945 via
Decimal-arithmetic CF expansion of `∛3` to 200 digits (independent
re-derivation matching the S12a/S12b 200-digit witnesses); first
13 partial quotients `[1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8]`
match. No math-correction was needed this iteration — both the
recursion arithmetic `(8 · 73011 + 13361 = 597449,
8 · 50623 + 9264 = 414248)` and the cube digits matched the
post-S12b sketch on the first pass.)

Two-line proof via the cubing-iff helper. -/

/-- `597449/414248 < ∛3`. Cube target: `(597449/414248)³ =
213_256_617_080_909_849 / 71_085_539_027_220_992 <
213_256_617_081_662_976 / 71_085_539_027_220_992 = 3` (strict:
`597449³ = 213_256_617_080_909_849 < 213_256_617_081_662_976 =
3 · 414248³`, gap `753_127`). The thirteenth convergent of the
simple CF of `∛3` (using `a₁₂ = 8` per OEIS A002945). -/
theorem five_nine_seven_four_four_nine_over_four_one_four_two_four_eight_lt_cbrt3 :
    (597449 / 414248 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

/-! ## S14a prep: new upper bound for `a₁₂ = 8` (the thirteenth partial quotient)

The fourteenth CF convergent of `∛3` (using `a₁₃ = 3` per OEIS A002945
prefix `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, …]`, 0-indexed) is

  `p₁₃/q₁₃ = (a₁₃·p₁₂ + p₁₁) / (a₁₃·q₁₂ + q₁₁)`
  `       = (3 · 597449 + 73011) / (3 · 414248 + 50623)`
  `       = 1_865_358 / 1_293_367`.

This convergent is odd-index (13), so it lies on the UPPER side of
`∛3` (alternating with the lower-side thirteenth convergent
`597449/414248` from S13).

Convergent recursion (with `a₁₃ = 3`):

  `q₁₃ = 3 · q₁₂ + q₁₁ = 3 · 414248 + 50623 = 1_293_367`
  `p₁₃ = 3 · p₁₂ + p₁₁ = 3 · 597449 + 73011 = 1_865_358`

After cubing,

  `1_865_358³   = 6_490_625_955_773_462_712`
  `3 · 1_293_367³ = 6_490_625_955_771_185_589`

so `1_865_358³ = 6_490_625_955_773_462_712 > 6_490_625_955_771_185_589 =
3 · 1_293_367³` (strict, diff `+2_277_123`). The new upper cube gap
(relative-to-`3·q³`: `≈ 3.51·10⁻¹³`) is roughly an order of magnitude
tighter than S13's lower-side gap of `≈ 3.53·10⁻¹²` — consistent with
`1_865_358/1_293_367` being the next true convergent one rung beyond
`597449/414248`.

(Pre-claim Python sanity check (this S14a session):
`1_865_358³ = 6_490_625_955_773_462_712`, `3 · 1_293_367³ =
6_490_625_955_771_185_589`, diff `+2_277_123 > 0` confirming
`(1_865_358/1_293_367)³ > 3`, hence `1_865_358/1_293_367 > cbrt3` as
required for an upper bound. Recursion arithmetic
`(3 · 597449 + 73011 = 1_865_358, 3 · 414248 + 50623 = 1_293_367)`
and the cube digits matched the post-S13b sketch on the first pass —
no math-correction needed this iteration.)

Two-line proof via the cubing-iff helper. -/

/-- `∛3 < 1865358/1293367`. Cube target: `(1865358/1293367)³ =
6_490_625_955_773_462_712 / 1_293_367³ > 3` (strict:
`1865358³ = 6_490_625_955_773_462_712 > 6_490_625_955_771_185_589 =
3 · 1293367³`, gap `+2_277_123`). The fourteenth convergent of the
simple CF of `∛3` (using `a₁₃ = 3` per OEIS A002945). -/
theorem cbrt3_lt_one_eight_six_five_three_five_eight_over_one_two_nine_three_three_six_seven :
    cbrt3 < (1865358 / 1293367 : ℝ) := by
  rw [cbrt3_lt_iff_three_lt_cube (by norm_num)]
  norm_num

/-! ## S15a prep: new lower bound for `a₁₃ = 3` (the fourteenth partial quotient)

The fifteenth CF convergent of `∛3` is

  `p₁₄/q₁₄ = (a₁₄·p₁₃ + p₁₂) / (a₁₄·q₁₃ + q₁₂)`
  `       = (3 · 1865358 + 597449) / (3 · 1293367 + 414248)`
  `       = 6_193_523 / 4_294_349`.

This convergent is even-index (14), so it lies on the LOWER side of
`∛3` (alternating with the upper-side fourteenth convergent
`1865358/1293367` from S14a, which is reused unchanged as the a₁₃
sandwich's upper bound).

**MATH-CORRECTION (this session).** The post-S14a sketch tail of OEIS
A002945 read `[…, 8, 3, 4, …]`, i.e. `a₁₄ = 4`. A 120-digit recomputation
of the CF algorithm for `∛3` gives the true prefix
`a₀..a₁₄ = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3]`, so `a₁₄ = 3`,
NOT `4`. With the wrong `a₁₄ = 4` the convergent would be
`8058881/5587716`, whose cube `8058881³ = 523_388_563_470_651_811_841 >
523_388_563_470_618_833_088 = 3 · 5587716³` lies ABOVE `∛3` — the WRONG
side for a lower bound (a `lt_cbrt3` proof of it would fail). The correct
even-index lower convergent is `6_193_523/4_294_349`. This repeats the
historical `a₈` typo precedent (S9-prep): when picking the next bound,
re-derive `aᵢ` from a high-precision CF computation, never re-quote a
prior sketch tail.

Convergent recursion (with `a₁₄ = 3`):

  `q₁₄ = 3 · q₁₃ + q₁₂ = 3 · 1293367 + 414248 = 4_294_349`
  `p₁₄ = 3 · p₁₃ + p₁₂ = 3 · 1865358 + 597449 = 6_193_523`

After cubing,

  `6_193_523³   = 237_581_852_386_719_346_667`
  `3 · 4_294_349³ = 237_581_852_386_724_971_647`

so `6_193_523³ = 237_581_852_386_719_346_667 < 237_581_852_386_724_971_647 =
3 · 4_294_349³` (strict, diff `+5_624_980`), hence `(6_193_523/4_294_349)³ < 3`
and `6_193_523/4_294_349 < cbrt3` as required for a lower bound. The new
lower cube gap (relative-to-`3·q³`: `≈ 2.37·10⁻¹⁴`) is roughly an order
of magnitude tighter than S14a's upper-side gap of `≈ 3.51·10⁻¹³`.

Rigorous a₁₃ check (exact `Fraction` interval propagation, this session):
with the sandwich `6193523/4294349 < cbrt3 < 1865358/1293367`, propagating
`[lo, hi]` through the map `x ↦ 1/(x - aᵢ)` for `a₀..a₁₂ =
[1,2,3,1,4,1,5,1,1,6,2,5,8]` yields a final `1/x ∈ [3, 10/3)`, forcing
`⌊1/x⌋ = 3 = a₁₃`. Two-line proof via the cubing-iff helper. -/

/-- `6193523/4294349 < ∛3`. Cube target: `(6193523/4294349)³ =
237_581_852_386_719_346_667 / 4_294_349³ < 3` (strict:
`6193523³ = 237_581_852_386_719_346_667 < 237_581_852_386_724_971_647 =
3 · 4294349³`, gap `+5_624_980`). The fifteenth convergent of the
simple CF of `∛3` (using `a₁₄ = 3` per a 120-digit CF recomputation;
NOT `a₁₄ = 4`). -/
theorem six_one_nine_three_five_two_three_over_four_two_nine_four_three_four_nine_lt_cbrt3 :
    (6193523 / 4294349 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

/-! ## S15 prep: new upper bound for `a₁₄ = 3` (the fifteenth partial quotient)

The sixteenth CF convergent of `∛3` is

  `p₁₅/q₁₅ = (a₁₅·p₁₄ + p₁₃) / (a₁₅·q₁₄ + q₁₃)`
  `       = (4 · 6193523 + 1865358) / (4 · 4294349 + 1293367)`
  `       = 26_639_450 / 18_470_763`.

This convergent is odd-index (15), so it lies on the UPPER side of
`∛3` (alternating with the lower-side fifteenth convergent
`6193523/4294349` from S15a, which is reused unchanged as the a₁₄
sandwich's lower bound).

`a₁₅ = 4` was re-derived independently from a 120-digit CF recomputation
of `∛3` (true prefix `a₀..a₁₆ = [1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8,
3, 3, 4, 2]`), per the S9-prep / S15a anti-typo discipline: never re-quote
a prior sketch tail, always recompute `aᵢ`.

Convergent recursion (with `a₁₅ = 4`):

  `q₁₅ = 4 · q₁₄ + q₁₃ = 4 · 4294349 + 1293367 = 18_470_763`
  `p₁₅ = 4 · p₁₄ + p₁₃ = 4 · 6193523 + 1865358 = 26_639_450`

After cubing,

  `26_639_450³     = 18_904_959_980_335_633_625_000`
  `3 · 18_470_763³ = 18_904_959_980_335_585_454_841`

so `26_639_450³ = 18_904_959_980_335_633_625_000 >
18_904_959_980_335_585_454_841 = 3 · 18_470_763³` (strict, diff
`+48_170_159`), hence `(26_639_450/18_470_763)³ > 3` and
`cbrt3 < 26_639_450/18_470_763` as required for an upper bound. The new
upper cube gap (relative-to-`3·q³`: `≈ 2.55·10⁻¹⁵`) is roughly an order
of magnitude tighter than S15a's lower-side gap of `≈ 2.37·10⁻¹⁴` —
consistent with `26_639_450/18_470_763` being the next true convergent
one rung beyond `6_193_523/4_294_349`.

Together with S15a's lower bound this prepares the sandwich
`6193523/4294349 < cbrt3 < 26639450/18470763` (combined gap `≈ 2.6·10⁻¹⁵`)
for the FUTURE main-ACT of the fifteenth partial quotient `cbrt3_a14 = 3`
(gated on the still-open S14b `a12 = 8` and the subsequent `a13 = 3`
landing first, since the nested-fraction chain grows one rung per
quotient). Two-line proof via the cubing-iff helper. -/

/-- `∛3 < 26639450/18470763`. Cube target: `(26639450/18470763)³ =
18_904_959_980_335_633_625_000 / 18_470_763³ > 3` (strict:
`26639450³ = 18_904_959_980_335_633_625_000 >
18_904_959_980_335_585_454_841 = 3 · 18470763³`, gap `+48_170_159`).
The sixteenth convergent of the simple CF of `∛3`
(using `a₁₅ = 4` per a 120-digit CF recomputation). -/
theorem cbrt3_lt_two_six_six_three_nine_four_five_zero_over_one_eight_four_seven_zero_seven_six_three :
    cbrt3 < (26639450 / 18470763 : ℝ) := by
  rw [cbrt3_lt_iff_three_lt_cube (by norm_num)]
  norm_num

/-! ## S25 prep: new lower bound for `a₁₇ = 6` (the eighteenth partial quotient)

The nineteenth CF convergent of `∛3` (using `a₁₈ = 4` per a 300-digit CF
recomputation, true prefix `a₀..a₁₈ =
[1, 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4]`, 0-indexed) is

  `p₁₈/q₁₈ = (a₁₈·p₁₇ + p₁₆) / (a₁₈·q₁₇ + q₁₆)`
  `       = (4 · 383473988 + 59472423) / (4 · 265886013 + 41235875)`
  `       = 1_593_368_375 / 1_104_779_927`.

This convergent is even-index (18), so it lies on the LOWER side of `∛3`
(alternating with the upper-side eighteenth convergent `383473988/265886013`,
the seventeenth partial quotient `a₁₇ = 6`).

Here `p₁₇/q₁₇ = 383473988/265886013` (the eighteenth convergent, upper) and
`p₁₆/q₁₆ = 59472423/41235875` (the seventeenth convergent, lower) are the two
prior rungs; both lie in sibling helper PRs (S24, S23) but this lower-bound
theorem is self-contained — it is discharged purely by cubing the literal
fraction, independent of whether those rungs are present in the file.

Convergent recursion (with `a₁₈ = 4`):

  `q₁₈ = 4 · q₁₇ + q₁₆ = 4 · 265886013 + 41235875 = 1_104_779_927`
  `p₁₈ = 4 · p₁₇ + p₁₆ = 4 · 383473988 + 59472423 = 1_593_368_375`

After cubing,

  `1_593_368_375³   = 4_045_279_924_912_085_586_177_734_375`
  `3 · 1_104_779_927³ = 4_045_279_924_912_085_587_552_412_949`

so `1_593_368_375³ = 4_045_279_924_912_085_586_177_734_375 <
4_045_279_924_912_085_587_552_412_949 = 3 · 1_104_779_927³` (strict, diff
`-1_374_678_574`), hence `(1_593_368_375/1_104_779_927)³ < 3` and
`1_593_368_375/1_104_779_927 < cbrt3` as required for a lower bound.

`a₁₈ = 4` was re-derived independently from a 300-digit CF recomputation of
`∛3` (cert `research/scripts/verify_cbrt3_oq04_s25_19th_convergent.py`), per the
S9-prep / S14a / S15-prep anti-typo discipline: never re-quote a prior sketch
tail, always recompute `aᵢ` and verify the cube-side direction before claiming.
Two-line proof via the cubing-iff helper. -/

/-- `1593368375/1104779927 < ∛3`. Cube target:
`(1593368375/1104779927)³ = 4_045_279_924_912_085_586_177_734_375 / 1104779927³
< 3` (strict: `1593368375³ = 4_045_279_924_912_085_586_177_734_375 <
4_045_279_924_912_085_587_552_412_949 = 3 · 1104779927³`, gap `1_374_678_574`).
The nineteenth convergent of the simple CF of `∛3` (using `a₁₈ = 4` per a
300-digit CF recomputation). -/
theorem one_five_nine_three_three_six_eight_three_seven_five_over_one_one_zero_four_seven_seven_nine_nine_two_seven_lt_cbrt3 :
    (1593368375 / 1104779927 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

/-- `8350315863/5789785648 < ∛3`. The twenty-first convergent of the simple CF
of `∛3` (using `a₂₀ = 1`).

Convergent recursion (with `a₂₀ = 1`):

  `q₂₀ = 1 · q₁₉ + q₁₈ = 1 · 4685005721 + 1104779927 = 5_789_785_648`
  `p₂₀ = 1 · p₁₉ + p₁₈ = 1 · 6756947488 + 1593368375 = 8_350_315_863`

After cubing,

  `8_350_315_863³   = 582_248_945_773_308_354_436_424_440_647`
  `3 · 5_789_785_648³ = 582_248_945_773_308_354_444_942_053_376`

so `8_350_315_863³ < 3 · 5_789_785_648³` (strict, diff `8_517_612_729`), hence
`(8350315863/5789785648)³ < 3` and `8350315863/5789785648 < cbrt3` as required
for a lower bound (even convergent index `20`).

`a₂₀ = 1` was re-derived independently from a 200-digit CF recomputation of
`∛3` (cert `research/scripts/verify_cbrt3_oq04_s27_21st_convergent.py`), per the
established anti-typo discipline: never re-quote a prior sketch tail, always
recompute `aᵢ` and verify the cube-side direction before claiming. Two-line
proof via the cubing-iff helper. -/
theorem eight_three_five_zero_three_one_five_eight_six_three_over_five_seven_eight_nine_seven_eight_five_six_four_eight_lt_cbrt3 :
    (8350315863 / 5789785648 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

/-- `∛3 < 31807895077/22054362665`. The twenty-second convergent of the simple CF
of `∛3` (using `a₂₁ = 3`), an UPPER bound (odd convergent index `21`).

Convergent recursion (with `a₂₁ = 3`):

  `q₂₁ = 3 · q₂₀ + q₁₉ = 3 · 5789785648 + 4685005721 = 22_054_362_665`
  `p₂₁ = 3 · p₂₀ + p₁₉ = 3 · 8350315863 + 6756947488 = 31_807_895_077`

After cubing,

  `31_807_895_077³   = 32_181_389_399_984_333_588_608_803_821_533`
  `3 · 22_054_362_665³ = 32_181_389_399_984_333_588_555_341_288_875`

so `3 · 22_054_362_665³ < 31_807_895_077³` (strict, diff `53_462_532_658`), hence
`3 < (31807895077/22054362665)³` and `cbrt3 < 31807895077/22054362665` as
required for an upper bound.

`a₂₁ = 3` was re-derived independently from a 200-digit CF recomputation of `∛3`
(cert `research/scripts/verify_cbrt3_oq04_s27_21st_convergent.py`, which also
records the 22nd-convergent recursion + cube direction), per the established
anti-typo discipline. Two-line proof via the upper cubing-iff helper. -/
theorem cbrt3_lt_three_one_eight_zero_seven_eight_nine_five_zero_seven_seven_over_two_two_zero_five_four_three_six_two_six_six_five :
    cbrt3 < (31807895077 / 22054362665 : ℝ) := by
  rw [cbrt3_lt_iff_three_lt_cube (by norm_num)]
  norm_num

/-- **Twenty-fourth continued-fraction convergent of `∛3`** (upper bound).

The CF of `∛3` is `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4,
1, 3, 2, 3, …]`.  With `a₂₃ = 3`, the recursion `pₖ = aₖ pₖ₋₁ + pₖ₋₂`,
`qₖ = aₖ qₖ₋₁ + qₖ₋₂` on the 22nd/23rd convergents
`31807895077/22054362665` and `71966106017/49898510978` gives the 24th
convergent

  `p₂₃ = 3·71966106017 + 31807895077 = 247_706_213_128`
  `q₂₃ = 3·49898510978 + 22054362665 = 171_749_895_599`.

After cubing,

  `247_706_213_128³  = 15_198_848_986_496_840_442_560_578_479_473_152`
  `3 · 171_749_895_599³ = 15_198_848_986_496_840_442_560_368_102_820_397`

so `3 · 171_749_895_599³ < 247_706_213_128³` (strict, diff `210_376_652_755`),
hence `3 < (247706213128/171749895599)³` and
`cbrt3 < 247706213128/171749895599` as required for an upper bound (relative gap
`≈ 4.6·10⁻²⁴`).

`a₂₃ = 3` was re-derived independently from a 160-digit CF recomputation of `∛3`
(cert `research/scripts/verify_cbrt3_oq04_s29_24th_convergent.py`, which also
records the recursion + exact cube direction), per the established anti-typo
discipline.  This is the next uncontested rung above the 23rd convergent
(PR #24635); it is a routine, durable helper bound, not a deep result.  Two-line
proof via the upper cubing-iff helper. -/
theorem cbrt3_lt_two_four_seven_seven_zero_six_two_one_three_one_two_eight_over_one_seven_one_seven_four_nine_eight_nine_five_five_nine_nine :
    cbrt3 < (247706213128 / 171749895599 : ℝ) := by
  rw [cbrt3_lt_iff_three_lt_cube (by norm_num)]
  norm_num

/-- **Twenty-fifth continued-fraction convergent of `∛3`** (lower bound).

With `a₂₄ = 4`, the recursion `pₖ = aₖ pₖ₋₁ + pₖ₋₂`, `qₖ = aₖ qₖ₋₁ + qₖ₋₂`
on the 23rd/24th convergents `71966106017/49898510978` and
`247706213128/171749895599` gives the 25th convergent

  `p₂₄ = 4·247706213128 + 71966106017 = 1_062_790_958_529`
  `q₂₄ = 4·171749895599 + 49898510978 = 736_898_093_374`.

After cubing,

  `1_062_790_958_529³   = 1_200_448_555_199_027_448_961_342_537_049_069_889`
  `3 · 736_898_093_374³ = 1_200_448_555_199_027_448_961_345_650_599_152_872`

so `1_062_790_958_529³ < 3 · 736_898_093_374³` (strict, diff `3_113_550_082_983`),
hence `(1062790958529/736898093374)³ < 3` and
`1062790958529/736898093374 < cbrt3` as required for a lower bound (even
convergent index `24`; relative gap `≈ 8.6·10⁻²⁵`).

`a₂₄ = 4` was re-derived independently from a 160-digit CF recomputation of `∛3`
(cert `research/scripts/verify_cbrt3_oq04_s30_25th_convergent.py`, which also
records the recursion + exact cube direction), per the established anti-typo
discipline: never re-quote a prior sketch tail, always recompute `aᵢ` and verify
the cube-side direction before claiming.  This is the next uncontested rung above
the 24th convergent; a routine, durable helper bound, not a deep result.
Two-line proof via the lower cubing-iff helper. -/
theorem one_zero_six_two_seven_nine_zero_nine_five_eight_five_two_nine_over_seven_three_six_eight_nine_eight_zero_nine_three_three_seven_four_lt_cbrt3 :
    (1062790958529 / 736898093374 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

/-- **Twenty-seventh continued-fraction convergent of `∛3`** (lower bound).

The CF of `∛3` is `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4,
1, 3, 2, 3, 4, 1, 4, …]`.  With `a₂₆ = 4`, the recursion `pₖ = aₖ pₖ₋₁ + pₖ₋₂`,
`qₖ = aₖ qₖ₋₁ + qₖ₋₂` on the 25th/26th convergents `1062790958529/736898093374`
and `1310497171657/908647988973` gives the 27th convergent

  `p₂₆ = 4·1310497171657 + 1062790958529 = 6_304_779_645_157`
  `q₂₆ = 4·908647988973 + 736898093374 = 4_371_490_049_266`.

After cubing,

  `6_304_779_645_157³   = 250_616_544_228_682_948_175_334_960_223_187_684_893`
  `3 · 4_371_490_049_266³ = 250_616_544_228_682_948_175_334_962_924_213_859_288`

so `6_304_779_645_157³ < 3 · 4_371_490_049_266³` (strict, diff
`2_701_026_174_395`), hence `(6304779645157/4371490049266)³ < 3` and
`6304779645157/4371490049266 < cbrt3` as required for a lower bound (even
convergent index `26`; relative gap `≈ 3.6·10⁻²⁷`).

`a₂₆ = 4` was re-derived independently from a 400-digit CF recomputation of `∛3`
(cert `research/scripts/verify_cbrt3_oq04_s32_27th_convergent.py`, which also
records the recursion + exact cube direction), per the established anti-typo
discipline: never re-quote a prior sketch tail, always recompute `aᵢ` and verify
the cube-side direction before claiming.  This is the next uncontested rung above
the 26th convergent (PR #24767); a routine, durable helper bound, not a deep
result.  Two-line proof via the lower cubing-iff helper. -/
theorem six_three_zero_four_seven_seven_nine_six_four_five_one_five_seven_over_four_three_seven_one_four_nine_zero_zero_four_nine_two_six_six_lt_cbrt3 :
    (6304779645157 / 4371490049266 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

/-- **Twenty-ninth continued-fraction convergent of `∛3`** (lower bound).

The CF of `∛3` is `[1; 2, 3, 1, 4, 1, 5, 1, 1, 6, 2, 5, 8, 3, 3, 4, 2, 6, 4, 4,
1, 3, 2, 3, 4, 1, 4, 9, 1, …]`.  With `a₂₇ = 9` and `a₂₈ = 1`, the recursion
`pₖ = aₖ pₖ₋₁ + pₖ₋₂`, `qₖ = aₖ qₖ₋₁ + qₖ₋₂` builds the 28th convergent from the
27th `6304779645157/4371490049266` (PR #24782) and the 26th
`1310497171657/908647988973`,

  `p₂₇ = 9·6304779645157 + 1310497171657 = 58_053_513_978_070`
  `q₂₇ = 9·4371490049266 +  908647988973 = 40_252_058_432_367`,

then the 29th convergent from the 28th and 27th,

  `p₂₈ = 1·58053513978070 + 6304779645157 = 64_358_293_623_227`
  `q₂₈ = 1·40252058432367 + 4371490049266 = 44_623_548_481_633`.

After cubing,

  `64_358_293_623_227³     = 266_571_405_907_439_242_825_392_459_510_337_159_398_083`
  `3 · 44_623_548_481_633³ = 266_571_405_907_439_242_825_392_459_540_815_108_589_411`

so `64_358_293_623_227³ < 3 · 44_623_548_481_633³` (strict, diff
`30_477_949_191_328`), hence `(64358293623227/44623548481633)³ < 3` and
`64358293623227/44623548481633 < cbrt3` as required for a lower bound (even
convergent index `28`; relative gap `≈ 3.8·10⁻²⁹`).

`a₂₇ = 9` and `a₂₈ = 1` were re-derived independently from a 500-digit CF
recomputation of `∛3` (cert `research/scripts/verify_cbrt3_oq04_s34_29th_convergent.py`,
which recomputes BOTH the 28th and 29th convergents from the recursion and
records the exact cube direction), per the established anti-typo discipline:
never re-quote a prior sketch tail, always recompute `aᵢ` and verify the
cube-side direction before claiming.  The intermediate 28th convergent
(`a₂₇ = 9`) currently lives only in open PRs #24802/#24809, so this rung is
built on freshly re-derived integers rather than an unmerged sketch.  A routine,
durable helper bound, not a deep result.  Two-line proof via the lower
cubing-iff helper. -/
theorem six_four_three_five_eight_two_nine_three_six_two_three_two_two_seven_over_four_four_six_two_three_five_four_eight_four_eight_one_six_three_three_lt_cbrt3 :
    (64358293623227 / 44623548481633 : ℝ) < cbrt3 := by
  rw [lt_cbrt3_iff_cube_lt (by norm_num)]
  norm_num

end Cbrt3Helpers
