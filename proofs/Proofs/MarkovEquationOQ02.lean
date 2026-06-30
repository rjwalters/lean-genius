/-
# Mod-3 Structure of Markov Triples  (markov-equation-oq-02)

The Markov equation `x² + y² + z² = 3xyz` (classified in `Proofs.MarkovEquation`,
with pairwise coprimality in `Proofs.MarkovCoprime`) has a clean *prime-3*
arithmetic rigidity that complements the prime-2 (parity) results
`markov_at_most_one_even` / `markov_not_both_even`:

* **no coordinate of a Markov triple is divisible by `3`**, and consequently
* **every coordinate is `≡ ±1 (mod 3)`** (its square is `1` in `ZMod 3`).

The proof is the standard residue argument. Reduce the equation modulo `3`:
since `3xyz ≡ 0`, the residues satisfy `a² + b² + c² ≡ 0`. A finite `decide`
over `ZMod 3` shows that if any one residue is `0`, then *all three* are `0`.
But three coordinates simultaneously divisible by `3` contradicts pairwise
coprimality (`markov_coprime`). Hence none is divisible by `3`, and a nonzero
residue in `ZMod 3` squares to `1`.

This mirrors the mod-3 obstruction `three_dvd_all_of_hurwitz_one` of
`Proofs.MarkovHurwitzOQ03OQ01` (which, for the *unscaled* equation
`x²+y²+z² = xyz`, forces the opposite conclusion — all coordinates divisible by
`3`); the factor of `3` on the right-hand side of the genuine Markov equation
flips the residue analysis entirely.

All results are elementary and fully machine-checked (0 axioms, 0 sorries).
-/
import Mathlib
import Proofs.MarkovEquation
import Proofs.MarkovCoprime

namespace MarkovEquationOQ02

open MarkovEquation MarkovCoprime

/-- A coprime pair of integers cannot share the (non-unit) factor `3`.
    The prime-3 analogue of `MarkovCoprime.not_two_dvd_both`. -/
theorem not_three_dvd_both {a b : ℤ} (h : IsCoprime a b) :
    ¬ ((3 : ℤ) ∣ a ∧ (3 : ℤ) ∣ b) := by
  rintro ⟨ha, hb⟩
  have hu : IsUnit (3 : ℤ) := h.isUnit_of_dvd' ha hb
  rcases Int.isUnit_iff.1 hu with h1 | h1 <;> norm_num at h1

/-- **No Markov coordinate is divisible by 3.** In any positive Markov triple,
    none of the three coordinates is a multiple of `3`. -/
theorem markov_not_three_dvd {x y z : ℤ} (h : IsMarkov x y z) :
    ¬ (3 : ℤ) ∣ x ∧ ¬ (3 : ℤ) ∣ y ∧ ¬ (3 : ℤ) ∣ z := by
  have he : x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z := h.2.2.2
  obtain ⟨hxy, hyz, hxz⟩ := markov_coprime h
  -- Push the integer equation into `ZMod 3` (the right side stays `3·a·b·c`,
  -- which `decide` evaluates to `0`).
  have hcast : (x : ZMod 3) ^ 2 + (y : ZMod 3) ^ 2 + (z : ZMod 3) ^ 2
      = 3 * (x : ZMod 3) * (y : ZMod 3) * (z : ZMod 3) := by
    have hh := congrArg (Int.cast : ℤ → ZMod 3) he
    push_cast at hh
    linear_combination hh
  -- Over `ZMod 3`, the equation forces: if one residue vanishes, all do.
  have key : ∀ a b c : ZMod 3,
      a ^ 2 + b ^ 2 + c ^ 2 = 3 * a * b * c →
      (a = 0 → b = 0 ∧ c = 0) ∧ (b = 0 → a = 0 ∧ c = 0) ∧
        (c = 0 → a = 0 ∧ b = 0) := by decide
  obtain ⟨ka, kb, kc⟩ := key _ _ _ hcast
  refine ⟨?_, ?_, ?_⟩
  · intro hdx
    have hx0 : (x : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mpr hdx
    obtain ⟨hy0, _⟩ := ka hx0
    have hdy : (3 : ℤ) ∣ y := (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp hy0
    exact not_three_dvd_both hxy ⟨hdx, hdy⟩
  · intro hdy
    have hy0 : (y : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mpr hdy
    obtain ⟨hx0, _⟩ := kb hy0
    have hdx : (3 : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hx0
    exact not_three_dvd_both hxy ⟨hdx, hdy⟩
  · intro hdz
    have hz0 : (z : ZMod 3) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd z 3).mpr hdz
    obtain ⟨hx0, _⟩ := kc hz0
    have hdx : (3 : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hx0
    exact not_three_dvd_both hxz ⟨hdx, hdz⟩

/-- The first coordinate of a Markov triple is not divisible by `3`. -/
theorem markov_not_three_dvd_fst {x y z : ℤ} (h : IsMarkov x y z) :
    ¬ (3 : ℤ) ∣ x := (markov_not_three_dvd h).1

/-- **Every Markov coordinate is `≡ ±1 (mod 3)`.** Equivalently, each
    coordinate's residue squares to `1` in `ZMod 3`. -/
theorem markov_sq_eq_one_mod_three {x y z : ℤ} (h : IsMarkov x y z) :
    (x : ZMod 3) ^ 2 = 1 ∧ (y : ZMod 3) ^ 2 = 1 ∧ (z : ZMod 3) ^ 2 = 1 := by
  obtain ⟨hx, hy, hz⟩ := markov_not_three_dvd h
  have hx0 : (x : ZMod 3) ≠ 0 := fun hc =>
    hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hc)
  have hy0 : (y : ZMod 3) ≠ 0 := fun hc =>
    hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp hc)
  have hz0 : (z : ZMod 3) ≠ 0 := fun hc =>
    hz ((ZMod.intCast_zmod_eq_zero_iff_dvd z 3).mp hc)
  have sqkey : ∀ a : ZMod 3, a ≠ 0 → a ^ 2 = 1 := by decide
  exact ⟨sqkey _ hx0, sqkey _ hy0, sqkey _ hz0⟩

/-! ## Sanity checks on the small Markov triples -/

example : ¬ (3 : ℤ) ∣ 1 := (markov_not_three_dvd markov_one).1
example : ¬ (3 : ℤ) ∣ 2 := (markov_not_three_dvd markov_one_one_two).2.2
example : ¬ (3 : ℤ) ∣ 5 := (markov_not_three_dvd markov_one_two_five).2.2
example : ¬ (3 : ℤ) ∣ 29 := (markov_not_three_dvd markov_two_five_twentynine).2.2

end MarkovEquationOQ02
