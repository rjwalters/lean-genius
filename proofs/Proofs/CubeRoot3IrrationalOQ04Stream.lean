/-
Bridge: the per-aᵢ floor lemmas ⟷ Mathlib's canonical CF API IntFractPair.stream.

Research: cube-root-3-irrational-oq-04, open question #1 (carried since S5).
Date: 2026-06-16 (researcher-3).

STATUS: build-PENDING orphan. Docker was DOWN this session, so this file has
NOT been elaborated. It is intentionally NOT registered in `proofs/Proofs.lean`,
so it cannot affect the gallery build until a future Docker-up session
build-verifies it and adds the import line (the established "register-orphan"
workflow). The MATHEMATICS is independently verified by
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
file proves, for n = 0, 1, 2:

  (IntFractPair.stream cbrt3 n).map IntFractPair.b = some aₙ

tying the existing `cbrt3_aₙ` floors to the canonical API for the first time.
The reusable step lemma `cbrt3_stream_succ` makes each further index mechanical
(reuse with `cbrt3_a3, cbrt3_a4, …` plus the matching irrationality witness).

## Mathlib API this file depends on (VERIFY THESE NAMES at v4.26.0 first)

  * `GenContFract.IntFractPair`            (namespace + structure; opened below)
  * `IntFractPair.of`, fields `.b`, `.fr`
  * `IntFractPair.stream_zero`
  * `IntFractPair.stream_succ_of_some`
  * `Irrational.ne_int`, `Irrational.sub_int`, `Irrational.inv`
  * `Int.fract` (unfolds under `simp`), `inv_eq_one_div`, `sub_ne_zero`

If any name drifted, the proof structure is unchanged — only the cited lemma
needs swapping. The numbers are cert-verified, so no math re-derivation is
needed.
-/

import Proofs.CubeRoot3IrrationalOQ04

open CubeRoot3Irrational
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
    have hsub : Irrational (cbrt3 - 1) := by simpa using irrational_cbrt3.sub_int 1
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

/-- Bundled first three partial quotients of the simple CF of `∛3`, stated
against Mathlib's canonical `IntFractPair.stream` API. This is the first
connection between the slug's ad-hoc nested-floor lemmas and the canonical CF
machinery (open question #1, carried since S5). -/
theorem cbrt3_stream_prefix :
    (IntFractPair.stream cbrt3 0).map IntFractPair.b = some (1 : ℤ) ∧
    (IntFractPair.stream cbrt3 1).map IntFractPair.b = some (2 : ℤ) ∧
    (IntFractPair.stream cbrt3 2).map IntFractPair.b = some (3 : ℤ) :=
  ⟨cbrt3_stream_b_zero, cbrt3_stream_b_one, cbrt3_stream_b_two⟩

end CubeRoot3IrrationalOQ04Stream
