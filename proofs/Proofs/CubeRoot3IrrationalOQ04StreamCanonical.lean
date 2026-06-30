/-
Canonical-object bridge for ∛3: partial denominators of `GenContFract.of cbrt3`.

Research: cube-root-3-irrational-oq-04, open question #1 (carried since S5).
Session: S37 (researcher-2, authored); S39 (researcher-11, 2026-06-18, build-verified + registered).

STATUS: BUILD-VERIFIED + REGISTERED. Authored at S37 as a standalone orphan
during a Docker blackout, importing the registered+build-verified
`Proofs.CubeRoot3IrrationalOQ04Stream`. At S39 (Docker capacity returned)
`./proofs/scripts/docker-build.sh Proofs.CubeRoot3IrrationalOQ04StreamCanonical`
compiled green (zero errors, 0 axioms, 0 sorries) and the file was registered in
`Proofs.lean`, so the canonical-CF prefix is now part of the gallery build
closure. The two translation lemmas it relies on are present at the v4.26.0 pin:
  * `GenContFract.of_h_eq_floor`
    (Mathlib/Algebra/ContinuedFractions/Computation/Translations.lean:167).
  * `GenContFract.get?_of_eq_some_of_succ_get?_intFractPair_stream`,
    signature `(stream v (n+1) = some ifp) → (of v).s.get? n = some ⟨1, ifp.b⟩`
    (same file, :232).
  * Every proof below is a mechanical clone of the merged, build-verified
    `cbrt3_stream_b_*` lemmas in the imported Stream file — identical tactic
    shape, only the index changes. No new tactic/API surface.

## What this file does

`IntFractPair.stream` sits one structural layer below Mathlib's top-level
continued-fraction object `GenContFract.of cbrt3`. Mathlib derives the latter
from the former via `of_h_eq_floor` (head term) and
`get?_of_eq_some_of_succ_get?_intFractPair_stream` (sequence terms): the `n`-th
sequence entry of `of v` is the partial-denominator pair `⟨1, (stream v (n+1)).get.b⟩`.
Combining those translation lemmas with the proven `cbrt3_stream_*` /
`cbrt3_stream_b_*` facts pins every partial quotient of the *fully canonical*
object over the proven prefix:

  (of cbrt3).h            = 1                       -- a₀
  (of cbrt3).s.get? k     = some ⟨1, a_{k+1}⟩       -- k = 0 … 10  (partial numerator 1)

This completes open question #1 in its strongest form: the CF prefix
`[1; 2,3,1,4,1,5,1,1,6,2,5]` now reads off Mathlib's canonical `GenContFract.of`,
not just the lower-level `IntFractPair.stream`.
-/
import Proofs.CubeRoot3IrrationalOQ04Stream

open CubeRoot3Irrational
open CubeRoot3IrrationalOQ04
open CubeRoot3IrrationalOQ04Stream
open GenContFract

namespace CubeRoot3IrrationalOQ04StreamCanonical

/-- Head term of the canonical CF of `∛3`: `a₀ = 1`. -/
theorem cbrt3_of_head : (GenContFract.of cbrt3).h = (1 : ℝ) := by
  rw [of_h_eq_floor, cbrt3_floor_eq_one]; norm_num

/-- Partial denominator `a1 = 2` of the canonical `GenContFract.of cbrt3`
(sequence index 0; partial numerator `1`). -/
theorem cbrt3_of_s_get_0 :
    (GenContFract.of cbrt3).s.get? 0 = some ⟨1, (2 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_one
  rw [cbrt3_stream_one] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_one, hb]
  norm_num

/-- Partial denominator `a2 = 3` of the canonical `GenContFract.of cbrt3`
(sequence index 1; partial numerator `1`). -/
theorem cbrt3_of_s_get_1 :
    (GenContFract.of cbrt3).s.get? 1 = some ⟨1, (3 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_two
  rw [cbrt3_stream_two] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_two, hb]
  norm_num

/-- Partial denominator `a3 = 1` of the canonical `GenContFract.of cbrt3`
(sequence index 2; partial numerator `1`). -/
theorem cbrt3_of_s_get_2 :
    (GenContFract.of cbrt3).s.get? 2 = some ⟨1, (1 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_three
  rw [cbrt3_stream_three] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_three, hb]
  norm_num

/-- Partial denominator `a4 = 4` of the canonical `GenContFract.of cbrt3`
(sequence index 3; partial numerator `1`). -/
theorem cbrt3_of_s_get_3 :
    (GenContFract.of cbrt3).s.get? 3 = some ⟨1, (4 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_four
  rw [cbrt3_stream_four] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_four, hb]
  norm_num

/-- Partial denominator `a5 = 1` of the canonical `GenContFract.of cbrt3`
(sequence index 4; partial numerator `1`). -/
theorem cbrt3_of_s_get_4 :
    (GenContFract.of cbrt3).s.get? 4 = some ⟨1, (1 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_five
  rw [cbrt3_stream_five] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_five, hb]
  norm_num

/-- Partial denominator `a6 = 5` of the canonical `GenContFract.of cbrt3`
(sequence index 5; partial numerator `1`). -/
theorem cbrt3_of_s_get_5 :
    (GenContFract.of cbrt3).s.get? 5 = some ⟨1, (5 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_six
  rw [cbrt3_stream_six] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_six, hb]
  norm_num

/-- Partial denominator `a7 = 1` of the canonical `GenContFract.of cbrt3`
(sequence index 6; partial numerator `1`). -/
theorem cbrt3_of_s_get_6 :
    (GenContFract.of cbrt3).s.get? 6 = some ⟨1, (1 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_seven
  rw [cbrt3_stream_seven] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_seven, hb]
  norm_num

/-- Partial denominator `a8 = 1` of the canonical `GenContFract.of cbrt3`
(sequence index 7; partial numerator `1`). -/
theorem cbrt3_of_s_get_7 :
    (GenContFract.of cbrt3).s.get? 7 = some ⟨1, (1 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_eight
  rw [cbrt3_stream_eight] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_eight, hb]
  norm_num

/-- Partial denominator `a9 = 6` of the canonical `GenContFract.of cbrt3`
(sequence index 8; partial numerator `1`). -/
theorem cbrt3_of_s_get_8 :
    (GenContFract.of cbrt3).s.get? 8 = some ⟨1, (6 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_nine
  rw [cbrt3_stream_nine] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_nine, hb]
  norm_num

/-- Partial denominator `a10 = 2` of the canonical `GenContFract.of cbrt3`
(sequence index 9; partial numerator `1`). -/
theorem cbrt3_of_s_get_9 :
    (GenContFract.of cbrt3).s.get? 9 = some ⟨1, (2 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_ten
  rw [cbrt3_stream_ten] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_ten, hb]
  norm_num

/-- Partial denominator `a11 = 5` of the canonical `GenContFract.of cbrt3`
(sequence index 10; partial numerator `1`). -/
theorem cbrt3_of_s_get_10 :
    (GenContFract.of cbrt3).s.get? 10 = some ⟨1, (5 : ℝ)⟩ := by
  have hb := cbrt3_stream_b_eleven
  rw [cbrt3_stream_eleven] at hb
  simp only [Option.map_some, Option.some.injEq] at hb
  rw [get?_of_eq_some_of_succ_get?_intFractPair_stream cbrt3_stream_eleven, hb]
  norm_num

/-- Bundled canonical continued-fraction prefix of `∛3` read directly off
Mathlib's `GenContFract.of`: head `a₀ = 1` and partial denominators
`a₁ … a₁₁ = 2,3,1,4,1,5,1,1,6,2,5` (all partial numerators `1`). This is the
fully canonical form of open question #1's prefix, one structural layer above the
`IntFractPair.stream` bundle `cbrt3_stream_prefix_eleven`. -/
theorem cbrt3_of_partquots_prefix :
    (GenContFract.of cbrt3).h = (1 : ℝ) ∧
    (GenContFract.of cbrt3).s.get? 0 = some ⟨1, (2 : ℝ)⟩ ∧
    (GenContFract.of cbrt3).s.get? 1 = some ⟨1, (3 : ℝ)⟩ ∧
    (GenContFract.of cbrt3).s.get? 2 = some ⟨1, (1 : ℝ)⟩ ∧
    (GenContFract.of cbrt3).s.get? 3 = some ⟨1, (4 : ℝ)⟩ ∧
    (GenContFract.of cbrt3).s.get? 4 = some ⟨1, (1 : ℝ)⟩ ∧
    (GenContFract.of cbrt3).s.get? 5 = some ⟨1, (5 : ℝ)⟩ ∧
    (GenContFract.of cbrt3).s.get? 6 = some ⟨1, (1 : ℝ)⟩ ∧
    (GenContFract.of cbrt3).s.get? 7 = some ⟨1, (1 : ℝ)⟩ ∧
    (GenContFract.of cbrt3).s.get? 8 = some ⟨1, (6 : ℝ)⟩ ∧
    (GenContFract.of cbrt3).s.get? 9 = some ⟨1, (2 : ℝ)⟩ ∧
    (GenContFract.of cbrt3).s.get? 10 = some ⟨1, (5 : ℝ)⟩ :=
  ⟨cbrt3_of_head, cbrt3_of_s_get_0, cbrt3_of_s_get_1, cbrt3_of_s_get_2, cbrt3_of_s_get_3, cbrt3_of_s_get_4, cbrt3_of_s_get_5, cbrt3_of_s_get_6, cbrt3_of_s_get_7, cbrt3_of_s_get_8, cbrt3_of_s_get_9, cbrt3_of_s_get_10⟩

end CubeRoot3IrrationalOQ04StreamCanonical
