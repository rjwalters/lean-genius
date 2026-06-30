/-
Bridge: the per-aᵢ floor lemmas ⟷ Mathlib's canonical CF API IntFractPair.stream.

Research: cube-root-3-irrational-oq-04, open question #1 (carried since S5).
Date: 2026-06-16 (researcher-3).

STATUS: REGISTERED + build-verified 2026-06-18 (researcher-12). Elaborated
under the Docker wrapper (`Proofs.CubeRoot3IrrationalOQ04Stream`,
`✔ Built ... (158s)`, full Mathlib pulled transitively) and registered in
`proofs/Proofs.lean`, so it is now part of the gallery build. 0 sorries,
0 axioms, 0 native_decide — the parent entry stays verified/original/0-axioms.
The MATHEMATICS is also independently verified by
`research/problems/cube-root-3-irrational-oq-04/verify_intfractpair_stream.py`
(PASS: stream b-components match the proven prefix a₀..a₁₁ and the fract-chain
identity fract(xᵢ) = xᵢ - aᵢ holds exactly at 120-digit precision).

## What this file does

The slug's main file proves the partial-quotient floors as standalone nested
expressions:

  cbrt3_a0 : ⌊cbrt3⌋ = 1
  cbrt3_a1 : ⌊1/(cbrt3 - 1)⌋ = 2
  cbrt3_a2 : ⌊1/(1/(cbrt3 - 1) - 2)⌋ = 3
  ...

None of these are connected to Mathlib's *canonical* continued-fraction
machinery. Mathlib builds `GenContFract.of` on top of `IntFractPair.stream`:

  IntFractPair.of v       = ⟨b := ⌊v⌋, fr := Int.fract v⟩
  IntFractPair.stream v 0  = some (IntFractPair.of v)
  IntFractPair.stream v (n+1)
       = (stream v n).bind (fun p => if p.fr = 0 then none else some (of p.fr⁻¹))

so the n-th partial quotient of any irrational v is `(stream v n).get.b`. This
file proves, for the FULL proven prefix n = 0 … 11:

  (IntFractPair.stream cbrt3 n).map IntFractPair.b = some aₙ

tying the existing `cbrt3_aₙ` floors to the canonical API. The n = 0,1,2 base
came first (S35); the extension to n = 3 … 11 (S36, researcher-3) is mechanical:
each level reuses the step lemma `cbrt3_stream_succ` with the matching
irrationality witness `cbrt3_stream_irr_*` and floor lemma `cbrt3_aₙ`. The deep
nested expressions were generated from the recursion `Eₙ = 1/(Eₙ₋₁ - aₙ₋₁)`
(byte-checked against the merged `cbrt3_aₙ` arguments), so they carry no
transcription risk; the only unverified surface is the `simp`/`show` reductions,
uniform across all levels and identical to the n = 0,1,2 base pattern.

## Mathlib API this file depends on (names offline-verified at v4.26.0, S36)

Checked against the pinned Mathlib4 checkout `2df2f0150c` (= lakefile
`rev = "v4.26.0"`) in S36 (researcher-3):

  * `GenContFract.IntFractPair`            ✓ structure (ContinuedFractions/Computation/Basic.lean),
                                             fields `.b : ℤ`, `.fr : K`
  * `IntFractPair.of`                       ✓ (Basic.lean:125)
  * `IntFractPair.stream_zero`              ✓ (Computation/Translations.lean:64), exact form
                                             `stream v 0 = some (of v)`
  * `IntFractPair.stream_succ_of_some`      ✓ (Translations.lean:97)
  * `Irrational.ne_int`                     ✓ (NumberTheory/Real/Irrational.lean:180)
  * `Irrational.sub_intCast`                ✓ (Irrational.lean:272) — NOTE: an earlier draft
                                             cited `Irrational.sub_int`, which does NOT exist at
                                             this pin (the Int-cast subtraction lemma is
                                             `sub_intCast`). Fixed in S36.
  * `Irrational.inv`                        ✓ (Irrational.lean:332, `protected theorem inv`)
  * `Int.fract`, `inv_eq_one_div`, `sub_ne_zero`  ✓ standard

`Irrational` content lives in `Mathlib.NumberTheory.Real.Irrational` at this pin
(`Mathlib.Data.Real.Irrational` is a 5-line re-export stub) — the base file's
`import Mathlib.Data.Real.Irrational` still resolves, and this orphan pulls full
Mathlib transitively via `Proofs.CubeRoot3IrrationalOQ04`.

The numbers are cert-verified and the name drift (`sub_int`) was fixed in S36;
the file built clean on 2026-06-18 (researcher-12) with no further edits to the
tactic bodies — the `simp`/`simpa` reductions (`IntFractPair.of` / `Int.fract`
normalisation and the `⁻¹ ↔ 1/·` bridge) went through as written.
-/

import Proofs.CubeRoot3IrrationalOQ04

open CubeRoot3Irrational
open CubeRoot3IrrationalOQ04
open GenContFract

namespace CubeRoot3IrrationalOQ04Stream

/-- One reciprocation step of the stream/floor bridge.

If at level `n` the stream value is `some (IntFractPair.of x)` with `x`
irrational (so its fractional part is nonzero, the stream does not terminate)
and `⌊x⌋ = a`, then the level-`(n+1)` stream value is
`some (IntFractPair.of (x - a)⁻¹)` — exactly the next nested reciprocal whose
floor the next `cbrt3_a` lemma computes. -/
lemma cbrt3_stream_succ {n : ℕ} {x : ℝ} {a : ℤ}
    (hs : IntFractPair.stream cbrt3 n = some (IntFractPair.of x))
    (hirr : Irrational x) (hfl : ⌊x⌋ = a) :
    IntFractPair.stream cbrt3 (n + 1) = some (IntFractPair.of (x - (a : ℝ))⁻¹) := by
  have hfr : (IntFractPair.of x).fr ≠ 0 := by
    have hx : Int.fract x ≠ 0 := sub_ne_zero.mpr (by simpa using hirr.ne_int ⌊x⌋)
    simpa [IntFractPair.of] using hx
  have hstep := IntFractPair.stream_succ_of_some hs hfr
  have hval : (IntFractPair.of x).fr⁻¹ = (x - (a : ℝ))⁻¹ := by
    simp [IntFractPair.of, Int.fract, hfl]
  rw [hstep, hval]

/-- Base case: `IntFractPair.stream cbrt3 0 = some (IntFractPair.of cbrt3)`. -/
theorem cbrt3_stream_zero :
    IntFractPair.stream cbrt3 0 = some (IntFractPair.of cbrt3) :=
  IntFractPair.stream_zero cbrt3

/-- First partial quotient via the canonical CF stream: `a₀ = 1`. -/
theorem cbrt3_stream_b_zero :
    (IntFractPair.stream cbrt3 0).map IntFractPair.b = some (1 : ℤ) := by
  rw [cbrt3_stream_zero]
  show some (IntFractPair.of cbrt3).b = some 1
  show some ⌊cbrt3⌋ = some 1
  rw [cbrt3_floor_eq_one]

/-- Level-1 stream value: `some (IntFractPair.of (cbrt3 - 1)⁻¹)`. -/
theorem cbrt3_stream_one :
    IntFractPair.stream cbrt3 1 = some (IntFractPair.of (cbrt3 - 1)⁻¹) := by
  have h := cbrt3_stream_succ cbrt3_stream_zero irrational_cbrt3 cbrt3_floor_eq_one
  simpa using h

/-- Second partial quotient via the canonical CF stream: `a₁ = 2`. -/
theorem cbrt3_stream_b_one :
    (IntFractPair.stream cbrt3 1).map IntFractPair.b = some (2 : ℤ) := by
  rw [cbrt3_stream_one]
  show some (IntFractPair.of (cbrt3 - 1)⁻¹).b = some 2
  show some ⌊(cbrt3 - 1)⁻¹⌋ = some 2
  rw [inv_eq_one_div]
  exact congrArg some cbrt3_a1

/-- Level-2 stream value: `some (IntFractPair.of ((cbrt3 - 1)⁻¹ - 2)⁻¹)`. -/
theorem cbrt3_stream_two :
    IntFractPair.stream cbrt3 2
      = some (IntFractPair.of ((cbrt3 - 1)⁻¹ - 2)⁻¹) := by
  have hirr1 : Irrational ((cbrt3 - 1)⁻¹) := by
    have hsub : Irrational (cbrt3 - 1) := by simpa using irrational_cbrt3.sub_intCast 1
    exact hsub.inv
  have hfl1 : ⌊(cbrt3 - 1)⁻¹⌋ = (2 : ℤ) := by
    rw [inv_eq_one_div]; exact cbrt3_a1
  have h := cbrt3_stream_succ cbrt3_stream_one hirr1 hfl1
  simpa using h

/-- Third partial quotient via the canonical CF stream: `a₂ = 3`. -/
theorem cbrt3_stream_b_two :
    (IntFractPair.stream cbrt3 2).map IntFractPair.b = some (3 : ℤ) := by
  rw [cbrt3_stream_two]
  show some (IntFractPair.of ((cbrt3 - 1)⁻¹ - 2)⁻¹).b = some 3
  show some ⌊((cbrt3 - 1)⁻¹ - 2)⁻¹⌋ = some 3
  rw [show ((cbrt3 - 1)⁻¹ - 2)⁻¹ = 1 / (1 / (cbrt3 - 1) - 2) by
        simp only [inv_eq_one_div]]
  exact congrArg some cbrt3_a2

/-! ## Extension to the full proven prefix (n = 3 … 11) — S36, researcher-3

The reusable step lemma `cbrt3_stream_succ` chains mechanically across every
index for which the corresponding nested-floor lemma `cbrt3_aₙ` is proven in
`CubeRoot3IrrationalOQ04.lean` (currently a₀ … a₁₁, the OEIS A002945 prefix).
Each level n needs only: the irrationality witness for Uₙ₋₁ (built below), the
floor identity `cbrt3_aₙ₋₁` (re-expressed from `1/·` to `·⁻¹` form), and one
`cbrt3_stream_succ` application. The b-components match the proven aₙ exactly,
cert-verified by `verify_intfractpair_stream.py` (n = 0 … 11). -/

/- Irrationality witnesses for the nested reciprocals `Uₙ`, needed to
   feed `cbrt3_stream_succ` (the stream does not terminate). -/

/-- `Uₙ` is irrational (n = 1). -/
lemma cbrt3_stream_irr_1 : Irrational ((cbrt3 - 1)⁻¹) := by
  have hsub : Irrational (cbrt3 - 1) := by
    simpa using irrational_cbrt3.sub_intCast 1
  exact hsub.inv

/-- `Uₙ` is irrational (n = 2). -/
lemma cbrt3_stream_irr_2 : Irrational (((cbrt3 - 1)⁻¹ - 2)⁻¹) := by
  have hsub : Irrational ((cbrt3 - 1)⁻¹ - 2) := by
    simpa using cbrt3_stream_irr_1.sub_intCast 2
  exact hsub.inv

/-- `Uₙ` is irrational (n = 3). -/
lemma cbrt3_stream_irr_3 : Irrational ((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹) := by
  have hsub : Irrational (((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3) := by
    simpa using cbrt3_stream_irr_2.sub_intCast 3
  exact hsub.inv

/-- `Uₙ` is irrational (n = 4). -/
lemma cbrt3_stream_irr_4 : Irrational (((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹) := by
  have hsub : Irrational ((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1) := by
    simpa using cbrt3_stream_irr_3.sub_intCast 1
  exact hsub.inv

/-- `Uₙ` is irrational (n = 5). -/
lemma cbrt3_stream_irr_5 : Irrational ((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹) := by
  have hsub : Irrational (((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4) := by
    simpa using cbrt3_stream_irr_4.sub_intCast 4
  exact hsub.inv

/-- `Uₙ` is irrational (n = 6). -/
lemma cbrt3_stream_irr_6 : Irrational (((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹) := by
  have hsub : Irrational ((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1) := by
    simpa using cbrt3_stream_irr_5.sub_intCast 1
  exact hsub.inv

/-- `Uₙ` is irrational (n = 7). -/
lemma cbrt3_stream_irr_7 : Irrational ((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹) := by
  have hsub : Irrational (((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5) := by
    simpa using cbrt3_stream_irr_6.sub_intCast 5
  exact hsub.inv

/-- `Uₙ` is irrational (n = 8). -/
lemma cbrt3_stream_irr_8 : Irrational (((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹) := by
  have hsub : Irrational ((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1) := by
    simpa using cbrt3_stream_irr_7.sub_intCast 1
  exact hsub.inv

/-- `Uₙ` is irrational (n = 9). -/
lemma cbrt3_stream_irr_9 : Irrational ((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹) := by
  have hsub : Irrational (((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1) := by
    simpa using cbrt3_stream_irr_8.sub_intCast 1
  exact hsub.inv

/-- `Uₙ` is irrational (n = 10). -/
lemma cbrt3_stream_irr_10 : Irrational (((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹) := by
  have hsub : Irrational ((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6) := by
    simpa using cbrt3_stream_irr_9.sub_intCast 6
  exact hsub.inv

/-- Level-3 stream value: `some (IntFractPair.of Uₙ)`. -/
theorem cbrt3_stream_three :
    IntFractPair.stream cbrt3 3 = some (IntFractPair.of ((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹)) := by
  have hfl : ⌊((cbrt3 - 1)⁻¹ - 2)⁻¹⌋ = (3 : ℤ) := by
    rw [show (((cbrt3 - 1)⁻¹ - 2)⁻¹) = 1 / (1 / (cbrt3 - 1) - 2) by simp only [inv_eq_one_div]]
    exact cbrt3_a2
  have h := cbrt3_stream_succ cbrt3_stream_two cbrt3_stream_irr_2 hfl
  simpa using h

/-- Partial quotient via the canonical CF stream: `a3 = 1`. -/
theorem cbrt3_stream_b_three :
    (IntFractPair.stream cbrt3 3).map IntFractPair.b = some (1 : ℤ) := by
  rw [cbrt3_stream_three]
  show some (IntFractPair.of ((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹)).b = some 1
  show some ⌊(((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹⌋ = some 1
  rw [show ((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹) = 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) by simp only [inv_eq_one_div]]
  exact congrArg some cbrt3_a3

/-- Level-4 stream value: `some (IntFractPair.of Uₙ)`. -/
theorem cbrt3_stream_four :
    IntFractPair.stream cbrt3 4 = some (IntFractPair.of (((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹)) := by
  have hfl : ⌊(((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹⌋ = (1 : ℤ) := by
    rw [show ((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹) = 1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) by simp only [inv_eq_one_div]]
    exact cbrt3_a3
  have h := cbrt3_stream_succ cbrt3_stream_three cbrt3_stream_irr_3 hfl
  simpa using h

/-- Partial quotient via the canonical CF stream: `a4 = 4`. -/
theorem cbrt3_stream_b_four :
    (IntFractPair.stream cbrt3 4).map IntFractPair.b = some (4 : ℤ) := by
  rw [cbrt3_stream_four]
  show some (IntFractPair.of (((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹)).b = some 4
  show some ⌊((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹⌋ = some 4
  rw [show (((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹) = 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) by simp only [inv_eq_one_div]]
  exact congrArg some cbrt3_a4

/-- Level-5 stream value: `some (IntFractPair.of Uₙ)`. -/
theorem cbrt3_stream_five :
    IntFractPair.stream cbrt3 5 = some (IntFractPair.of ((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹)) := by
  have hfl : ⌊((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹⌋ = (4 : ℤ) := by
    rw [show (((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹) = 1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) by simp only [inv_eq_one_div]]
    exact cbrt3_a4
  have h := cbrt3_stream_succ cbrt3_stream_four cbrt3_stream_irr_4 hfl
  simpa using h

/-- Partial quotient via the canonical CF stream: `a5 = 1`. -/
theorem cbrt3_stream_b_five :
    (IntFractPair.stream cbrt3 5).map IntFractPair.b = some (1 : ℤ) := by
  rw [cbrt3_stream_five]
  show some (IntFractPair.of ((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹)).b = some 1
  show some ⌊(((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹⌋ = some 1
  rw [show ((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹) = 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) by simp only [inv_eq_one_div]]
  exact congrArg some cbrt3_a5

/-- Level-6 stream value: `some (IntFractPair.of Uₙ)`. -/
theorem cbrt3_stream_six :
    IntFractPair.stream cbrt3 6 = some (IntFractPair.of (((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹)) := by
  have hfl : ⌊(((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹⌋ = (1 : ℤ) := by
    rw [show ((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹) = 1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) by simp only [inv_eq_one_div]]
    exact cbrt3_a5
  have h := cbrt3_stream_succ cbrt3_stream_five cbrt3_stream_irr_5 hfl
  simpa using h

/-- Partial quotient via the canonical CF stream: `a6 = 5`. -/
theorem cbrt3_stream_b_six :
    (IntFractPair.stream cbrt3 6).map IntFractPair.b = some (5 : ℤ) := by
  rw [cbrt3_stream_six]
  show some (IntFractPair.of (((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹)).b = some 5
  show some ⌊((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹⌋ = some 5
  rw [show (((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) by simp only [inv_eq_one_div]]
  exact congrArg some cbrt3_a6

/-- Level-7 stream value: `some (IntFractPair.of Uₙ)`. -/
theorem cbrt3_stream_seven :
    IntFractPair.stream cbrt3 7 = some (IntFractPair.of ((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹)) := by
  have hfl : ⌊((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹⌋ = (5 : ℤ) := by
    rw [show (((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) by simp only [inv_eq_one_div]]
    exact cbrt3_a6
  have h := cbrt3_stream_succ cbrt3_stream_six cbrt3_stream_irr_6 hfl
  simpa using h

/-- Partial quotient via the canonical CF stream: `a7 = 1`. -/
theorem cbrt3_stream_b_seven :
    (IntFractPair.stream cbrt3 7).map IntFractPair.b = some (1 : ℤ) := by
  rw [cbrt3_stream_seven]
  show some (IntFractPair.of ((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹)).b = some 1
  show some ⌊(((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹⌋ = some 1
  rw [show ((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) by simp only [inv_eq_one_div]]
  exact congrArg some cbrt3_a7

/-- Level-8 stream value: `some (IntFractPair.of Uₙ)`. -/
theorem cbrt3_stream_eight :
    IntFractPair.stream cbrt3 8 = some (IntFractPair.of (((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹)) := by
  have hfl : ⌊(((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹⌋ = (1 : ℤ) := by
    rw [show ((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) by simp only [inv_eq_one_div]]
    exact cbrt3_a7
  have h := cbrt3_stream_succ cbrt3_stream_seven cbrt3_stream_irr_7 hfl
  simpa using h

/-- Partial quotient via the canonical CF stream: `a8 = 1`. -/
theorem cbrt3_stream_b_eight :
    (IntFractPair.stream cbrt3 8).map IntFractPair.b = some (1 : ℤ) := by
  rw [cbrt3_stream_eight]
  show some (IntFractPair.of (((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹)).b = some 1
  show some ⌊((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹⌋ = some 1
  rw [show (((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) by simp only [inv_eq_one_div]]
  exact congrArg some cbrt3_a8

/-- Level-9 stream value: `some (IntFractPair.of Uₙ)`. -/
theorem cbrt3_stream_nine :
    IntFractPair.stream cbrt3 9 = some (IntFractPair.of ((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹)) := by
  have hfl : ⌊((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹⌋ = (1 : ℤ) := by
    rw [show (((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) by simp only [inv_eq_one_div]]
    exact cbrt3_a8
  have h := cbrt3_stream_succ cbrt3_stream_eight cbrt3_stream_irr_8 hfl
  simpa using h

/-- Partial quotient via the canonical CF stream: `a9 = 6`. -/
theorem cbrt3_stream_b_nine :
    (IntFractPair.stream cbrt3 9).map IntFractPair.b = some (6 : ℤ) := by
  rw [cbrt3_stream_nine]
  show some (IntFractPair.of ((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹)).b = some 6
  show some ⌊(((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹⌋ = some 6
  rw [show ((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) by simp only [inv_eq_one_div]]
  exact congrArg some cbrt3_a9

/-- Level-10 stream value: `some (IntFractPair.of Uₙ)`. -/
theorem cbrt3_stream_ten :
    IntFractPair.stream cbrt3 10 = some (IntFractPair.of (((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹)) := by
  have hfl : ⌊(((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹⌋ = (6 : ℤ) := by
    rw [show ((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) by simp only [inv_eq_one_div]]
    exact cbrt3_a9
  have h := cbrt3_stream_succ cbrt3_stream_nine cbrt3_stream_irr_9 hfl
  simpa using h

/-- Partial quotient via the canonical CF stream: `a10 = 2`. -/
theorem cbrt3_stream_b_ten :
    (IntFractPair.stream cbrt3 10).map IntFractPair.b = some (2 : ℤ) := by
  rw [cbrt3_stream_ten]
  show some (IntFractPair.of (((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹)).b = some 2
  show some ⌊((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹⌋ = some 2
  rw [show (((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) by simp only [inv_eq_one_div]]
  exact congrArg some cbrt3_a10

/-- Level-11 stream value: `some (IntFractPair.of Uₙ)`. -/
theorem cbrt3_stream_eleven :
    IntFractPair.stream cbrt3 11 = some (IntFractPair.of ((((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹ - 2)⁻¹)) := by
  have hfl : ⌊((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹⌋ = (2 : ℤ) := by
    rw [show (((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) by simp only [inv_eq_one_div]]
    exact cbrt3_a10
  have h := cbrt3_stream_succ cbrt3_stream_ten cbrt3_stream_irr_10 hfl
  simpa using h

/-- Partial quotient via the canonical CF stream: `a11 = 5`. -/
theorem cbrt3_stream_b_eleven :
    (IntFractPair.stream cbrt3 11).map IntFractPair.b = some (5 : ℤ) := by
  rw [cbrt3_stream_eleven]
  show some (IntFractPair.of ((((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹ - 2)⁻¹)).b = some 5
  show some ⌊(((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹ - 2)⁻¹⌋ = some 5
  rw [show ((((((((((((cbrt3 - 1)⁻¹ - 2)⁻¹ - 3)⁻¹ - 1)⁻¹ - 4)⁻¹ - 1)⁻¹ - 5)⁻¹ - 1)⁻¹ - 1)⁻¹ - 6)⁻¹ - 2)⁻¹) = 1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (1 / (cbrt3 - 1) - 2) - 3) - 1) - 4) - 1) - 5) - 1) - 1) - 6) - 2) by simp only [inv_eq_one_div]]
  exact congrArg some cbrt3_a11


/-- Bundled first three partial quotients of the simple CF of `∛3`, stated
against Mathlib's canonical `IntFractPair.stream` API. This is the first
connection between the slug's ad-hoc nested-floor lemmas and the canonical CF
machinery (open question #1, carried since S5). -/
theorem cbrt3_stream_prefix :
    (IntFractPair.stream cbrt3 0).map IntFractPair.b = some (1 : ℤ) ∧
    (IntFractPair.stream cbrt3 1).map IntFractPair.b = some (2 : ℤ) ∧
    (IntFractPair.stream cbrt3 2).map IntFractPair.b = some (3 : ℤ) :=
  ⟨cbrt3_stream_b_zero, cbrt3_stream_b_one, cbrt3_stream_b_two⟩

/-- Bundled FULL proven prefix a₀ … a₁₁ of the simple CF of `∛3`, stated
against Mathlib's canonical `IntFractPair.stream` API. Extends
`cbrt3_stream_prefix` to every index whose nested-floor lemma is proven
(open question #1, carried since S5). -/
theorem cbrt3_stream_prefix_eleven :
    (IntFractPair.stream cbrt3 0).map IntFractPair.b = some (1 : ℤ) ∧
    (IntFractPair.stream cbrt3 1).map IntFractPair.b = some (2 : ℤ) ∧
    (IntFractPair.stream cbrt3 2).map IntFractPair.b = some (3 : ℤ) ∧
    (IntFractPair.stream cbrt3 3).map IntFractPair.b = some (1 : ℤ) ∧
    (IntFractPair.stream cbrt3 4).map IntFractPair.b = some (4 : ℤ) ∧
    (IntFractPair.stream cbrt3 5).map IntFractPair.b = some (1 : ℤ) ∧
    (IntFractPair.stream cbrt3 6).map IntFractPair.b = some (5 : ℤ) ∧
    (IntFractPair.stream cbrt3 7).map IntFractPair.b = some (1 : ℤ) ∧
    (IntFractPair.stream cbrt3 8).map IntFractPair.b = some (1 : ℤ) ∧
    (IntFractPair.stream cbrt3 9).map IntFractPair.b = some (6 : ℤ) ∧
    (IntFractPair.stream cbrt3 10).map IntFractPair.b = some (2 : ℤ) ∧
    (IntFractPair.stream cbrt3 11).map IntFractPair.b = some (5 : ℤ) := by
  exact ⟨cbrt3_stream_b_zero, cbrt3_stream_b_one, cbrt3_stream_b_two, cbrt3_stream_b_three, cbrt3_stream_b_four, cbrt3_stream_b_five, cbrt3_stream_b_six, cbrt3_stream_b_seven, cbrt3_stream_b_eight, cbrt3_stream_b_nine, cbrt3_stream_b_ten, cbrt3_stream_b_eleven⟩

end CubeRoot3IrrationalOQ04Stream
