/-
Hilbert's 10th Problem over ℚ — OQ-01-OQ-02: the EXACT affine stabilizer of ℤ ⊂ ℚ.

The companion file `Proofs.Hilbert10OQ01OQ02IntStabilizer` records that a handful
of specific affine maps fix `IntSubset = ℤ` setwise — integer translations
`q ↦ q + n`, integer glide-reflections `q ↦ -q + n`, the reflection `q ↦ -q` —
and that the dilation `q ↦ 2q` does NOT (½ escapes).  From those partial facts its
docstring *asserts* that the stabilizer is exactly the integer infinite dihedral
group `ℤ ⋊ {±1}` ("the linear part must be a unit of `ℤ`, i.e. `±1`"), but it never
proves the full biconditional: it exhibits members and one non-member, not the
complete characterization.

This file closes that gap with the exact setwise stabilizer:

  `affinePullback a b IntSubset = IntSubset ↔ (a = 1 ∨ a = -1) ∧ ∃ n : ℤ, b = n`
      (`affinePullback_int_eq_int_iff`).

The forward direction is the new content.  Testing the pointwise equivalence
`a·q + b ∈ ℤ ⟺ q ∈ ℤ` at three rational points pins the coefficients:

  * `q = 0` forces `b ∈ ℤ`;
  * `q = 1` then forces `a ∈ ℤ`;
  * `q = ½` rules out `a = 0` (else the map is constant on `ℤ`-membership, but ½ ∉ ℤ);
  * `q = a⁻¹` forces `a⁻¹ ∈ ℤ`, and an integer whose inverse is also an integer is a
    unit of `ℤ`, i.e. `a = ±1` (`Int.isUnit_iff`).

The backward direction reuses the companion's `affinePullback_one_intCast_fixesInt`
and `affinePullback_negOne_intCast_fixesInt`.

Consequences proved here:

  * `affinePullback_int_eq_int_iff` — the exact stabilizer biconditional above.
  * `mem_intAffineStabilizer_iff` — the same, phrased as membership in the explicit
    parameter set `{(a,b) | (a = 1 ∨ a = -1) ∧ b ∈ ℤ}`.
  * `affinePullback_int_eq_int_iff_linear_isUnit` — the linear coefficient of any
    ℤ-fixing affine map is a unit of `ℤ` (the "±1 scaling" clause, isolated).
  * `affinePullback_int_ne_int_of_not_isometry` — contrapositive: a non-`±1`
    dilation never fixes `ℤ`, generalising the companion's single `a = 2` example
    to every `a ∉ {1, -1}`.

All results are `0`-sorry and do not invoke the parent's `koenigsmann_2016`
axiom (`affinePullback` and `IntSubset` are pure definitions).
-/

import Mathlib
import Proofs.Hilbert10OQ01OQ02
import Proofs.Hilbert10OQ01OQ02IntStabilizer

namespace Hilbert10OQ01OQ02IntStabilizerExact

open Hilbert10Rationals Hilbert10OQ01OQ02IntStabilizer

/-- **The exact affine setwise stabilizer of `ℤ ⊂ ℚ`.**  An affine reparametrization
`q ↦ a·q + b` fixes `IntSubset = ℤ` setwise **iff** its linear part is `±1` and its
translation part is an integer:

  `affinePullback a b IntSubset = IntSubset ↔ (a = 1 ∨ a = -1) ∧ ∃ n : ℤ, b = n`.

This is the integer infinite dihedral group `ℤ ⋊ {±1}` inside the affine group of `ℚ`.
The forward direction pins `a, b` by testing the pointwise equivalence
`a·q + b ∈ ℤ ⟺ q ∈ ℤ` at `q = 0` (⟹ `b ∈ ℤ`), `q = 1` (⟹ `a ∈ ℤ`), `q = ½`
(⟹ `a ≠ 0`) and `q = a⁻¹` (⟹ `a⁻¹ ∈ ℤ`, so `a` is a unit of `ℤ`). -/
theorem affinePullback_int_eq_int_iff (a b : ℚ) :
    affinePullback a b IntSubset = IntSubset ↔
      (a = 1 ∨ a = -1) ∧ ∃ n : ℤ, b = (n : ℚ) := by
  constructor
  · intro h
    -- The setwise equality unfolds to a pointwise equivalence of membership.
    have hiff : ∀ q : ℚ, (∃ z : ℤ, a * q + b = (z : ℚ)) ↔ (∃ z : ℤ, q = (z : ℚ)) := by
      intro q
      simpa only [affinePullback, IntSubset] using iff_of_eq (congrFun h q)
    -- `q = 0` ⟹ `b ∈ ℤ`.
    have hb : ∃ n : ℤ, b = (n : ℚ) := by
      obtain ⟨z, hz⟩ := (hiff 0).mpr ⟨0, by norm_num⟩
      rw [mul_zero, zero_add] at hz
      exact ⟨z, hz⟩
    obtain ⟨n₀, hn₀⟩ := hb
    -- `q = 1` ⟹ `a ∈ ℤ`.
    have ha_int : ∃ m : ℤ, a = (m : ℚ) := by
      obtain ⟨z, hz⟩ := (hiff 1).mpr ⟨1, by norm_num⟩
      rw [mul_one, hn₀] at hz
      refine ⟨z - n₀, ?_⟩
      push_cast
      linarith [hz]
    obtain ⟨m, hm⟩ := ha_int
    -- `q = ½` ⟹ `a ≠ 0` (otherwise `ℤ`-membership is constant, but ½ ∉ ℤ).
    have ha0 : a ≠ 0 := by
      intro ha
      obtain ⟨z, hz⟩ := (hiff (1 / 2)).mp ⟨n₀, by rw [ha, hn₀]; ring⟩
      have hc : ((2 * z : ℤ) : ℚ) = 1 := by push_cast; linarith [hz]
      have : (2 * z : ℤ) = 1 := by exact_mod_cast hc
      omega
    -- `q = a⁻¹` ⟹ `a⁻¹ ∈ ℤ`.
    have hainv : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
    have hinv : ∃ k : ℤ, a⁻¹ = (k : ℚ) := by
      apply (hiff a⁻¹).mp
      refine ⟨1 + n₀, ?_⟩
      rw [hainv, hn₀]; push_cast; ring
    obtain ⟨k, hk⟩ := hinv
    -- `a` and `a⁻¹` both integers ⟹ `a` is a unit of `ℤ` ⟹ `a = ±1`.
    have hmk_q : (m : ℚ) * (k : ℚ) = 1 := by rw [← hm, ← hk]; exact hainv
    have hmk : m * k = 1 := by exact_mod_cast hmk_q
    have hm_unit : m = 1 ∨ m = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hmk
    refine ⟨?_, n₀, hn₀⟩
    rcases hm_unit with h1 | h1
    · left; rw [hm]; exact_mod_cast h1
    · right; rw [hm]; exact_mod_cast h1
  · rintro ⟨ha, n, hn⟩
    subst hn
    rcases ha with ha | ha <;> subst ha
    · exact affinePullback_one_intCast_fixesInt n
    · exact affinePullback_negOne_intCast_fixesInt n

/-- The exact stabilizer, phrased as membership of the parameter pair `(a, b)` in the
explicit set `{(a, b) | (a = 1 ∨ a = -1) ∧ b ∈ ℤ}` — the integer infinite dihedral
group `ℤ ⋊ {±1}`. -/
theorem mem_intAffineStabilizer_iff (a b : ℚ) :
    affinePullback a b IntSubset = IntSubset ↔
      (a, b) ∈ {p : ℚ × ℚ | (p.1 = 1 ∨ p.1 = -1) ∧ ∃ n : ℤ, p.2 = (n : ℚ)} := by
  simpa [Set.mem_setOf_eq] using affinePullback_int_eq_int_iff a b

/-- **The linear coefficient of any `ℤ`-fixing affine map is a unit of `ℤ`.**  Isolating
the "±1 scaling" clause of the exact stabilizer: if `q ↦ a·q + b` fixes `ℤ` setwise then
`a` is an integer and a unit of `ℤ` (equivalently `a = ±1`). -/
theorem affinePullback_int_eq_int_iff_linear_isUnit {a b : ℚ}
    (h : affinePullback a b IntSubset = IntSubset) : a = 1 ∨ a = -1 :=
  ((affinePullback_int_eq_int_iff a b).mp h).1

/-- **No non-isometry fixes `ℤ`.**  Contrapositive of the exact stabilizer: if the linear
part `a` is neither `1` nor `-1`, then `q ↦ a·q + b` never fixes `ℤ` setwise — for any
translation `b`.  This generalises the companion's single `affinePullback_two_ne_int`
(the `a = 2` case) to every `a ∉ {1, -1}`. -/
theorem affinePullback_int_ne_int_of_not_isometry {a b : ℚ}
    (ha : a ≠ 1) (ha' : a ≠ -1) : affinePullback a b IntSubset ≠ IntSubset := by
  intro h
  rcases affinePullback_int_eq_int_iff_linear_isUnit h with h1 | h1
  · exact ha h1
  · exact ha' h1

#check @affinePullback_int_eq_int_iff
#check @mem_intAffineStabilizer_iff
#check @affinePullback_int_eq_int_iff_linear_isUnit
#check @affinePullback_int_ne_int_of_not_isometry

end Hilbert10OQ01OQ02IntStabilizerExact
