import Mathlib.FieldTheory.Finite.Basic

/-! An elementary nonsquare-value lemma for quadratic polynomials. -/

namespace Erdos85

universe u

/-- Over a finite field of odd characteristic, every translated square
polynomial `t²-a`, with `a ≠ 0`, assumes a nonsquare value.  Otherwise chosen
square roots would inject the field into its strictly smaller unit group. -/
theorem exists_not_isSquare_sq_sub {K : Type u} [Field K] [Finite K]
    [DecidableEq K] (h2 : (2 : K) ≠ 0) {a : K} (ha : a ≠ 0) :
    ∃ t : K, ¬ IsSquare (t ^ 2 - a) := by
  classical
  by_contra h
  push_neg at h
  let y : K → K := fun t => Classical.choose (h t)
  have hy (t : K) : y t * y t = t ^ 2 - a :=
    (Classical.choose_spec (h t)).symm
  have hu (t : K) : t - y t ≠ 0 := by
    intro hz
    have hty : t = y t := sub_eq_zero.mp hz
    apply ha
    have ht := hy t
    rw [← hty, pow_two] at ht
    calc
      a = t * t - (t * t - a) := by ring
      _ = 0 := by rw [← ht]; ring
  let f : K → Kˣ := fun t => Units.mk0 (t - y t) (hu t)
  have hf : Function.Injective f := by
    intro s t hst
    have huv : s - y s = t - y t := by
      exact congrArg ((↑) : Kˣ → K) hst
    have hrecon (z : K) : 2 * z = (z - y z) + a / (z - y z) := by
      have hprod : (z - y z) * (z + y z) = a := by
        calc
          _ = z ^ 2 - y z * y z := by ring
          _ = a := by rw [hy]; ring
      have hquot : a / (z - y z) = z + y z := by
        apply (div_eq_iff (hu z)).2
        rw [mul_comm]
        exact hprod.symm
      rw [hquot]
      ring
    have hs := hrecon s
    have ht := hrecon t
    rw [huv] at hs
    exact mul_left_cancel₀ h2 (hs.trans ht.symm)
  letI : Fintype K := Fintype.ofFinite K
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_units] at hcard
  have hpos : 1 ≤ Fintype.card K := Fintype.card_pos_iff.mpr inferInstance
  omega

/-- In particular, `1+t²` is a nonsquare for some nonzero `t`. -/
theorem exists_ne_zero_not_isSquare_one_add_sq
    {K : Type u} [Field K] [Finite K] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) :
    ∃ t : K, t ≠ 0 ∧ ¬ IsSquare (1 + t ^ 2) := by
  obtain ⟨t, ht⟩ := exists_not_isSquare_sq_sub h2 (a := (-1 : K)) (by simp)
  refine ⟨t, ?_, ?_⟩
  · intro hz
    subst t
    simp at ht
  · simpa [add_comm] using ht

/-- The nonsquare discriminant condition rules out every root of the
quadratic governing absolute opposite endpoints in the polarity switch. -/
theorem switch_quadratic_ne_zero {K : Type u} [Field K]
    (h2 : (2 : K) ≠ 0) {t : K} (ht : ¬ IsSquare (1 + t ^ 2)) (z : K) :
    t ^ 2 * (z + 1) ^ 2 + 4 * z ≠ 0 := by
  intro hz
  apply ht
  refine ⟨(t ^ 2 * z + t ^ 2 + 2) / 2, ?_⟩
  field_simp [h2]
  ring_nf at hz ⊢
  linear_combination -t ^ 2 * hz

end Erdos85
