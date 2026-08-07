import Proofs.Erdos85SquareFamilyDescent

/-!
# Characteristic-two obstruction for the descended cyclic block

For a function `s` on an odd cyclic group, the coefficient at `2z` of its
self-convolution is congruent modulo two to `s(z)^2`: all terms away from
`z` cancel in pairs under `x ↦ 2z-x`.  Applied to a `0/1` circulant
adjacency row, this says that the odd support of the squared row has the same
cardinality as the original neighbourhood.

In the descended square-family identity that odd support is instead every
residue except `0,±1`, of cardinality `r-3=a(a-1)`.  Comparing cardinalities
forces `a=a(a-1)`, hence `a=2`; this rules out all relevant `a≥4` uniformly.
-/

namespace Erdos85

open scoped BigOperators

def cyclicSelfConvolution {r : ℕ} [NeZero r]
    (s : ZMod r → ℕ) (z : ZMod r) : ℕ :=
  ∑ x, s x * s (z - x)

/-- Frobenius cancellation for a self-convolution on an odd cyclic group. -/
theorem cyclicSelfConvolution_double_mod_two
    {r : ℕ} [NeZero r] (hr : Odd r)
    (s : ZMod r → ℕ) (z : ZMod r) :
    ((cyclicSelfConvolution s (2 * z) : ℕ) : ZMod 2) =
      (s z : ZMod 2) ^ 2 := by
  let f : ZMod r → ZMod 2 :=
    fun x ↦ (s x : ZMod 2) * (s (2 * z - x) : ZMod 2)
  let g : ZMod r → ZMod r := fun x ↦ 2 * z - x
  have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hr
  have hunit : IsUnit (2 : ZMod r) := by
    simpa using (ZMod.isUnit_iff_coprime 2 r).mpr hcop
  have hfix {x : ZMod r} (hx : g x = x) : x = z := by
    dsimp only [g] at hx
    have hz : 2 * z = x + x := (sub_eq_iff_eq_add).mp hx
    have htwo : x * 2 = z * 2 := by
      simpa [mul_two, two_mul] using hz.symm
    exact hunit.mul_left_injective htwo
  have hsumErase : ∑ x ∈ (Finset.univ.erase z), f x = 0 := by
    apply Finset.sum_involution (fun x _ ↦ g x)
    · intro x _
      dsimp only [f, g]
      rw [show 2 * z - (2 * z - x) = x by ring]
      rw [mul_comm (s (2 * z - x) : ZMod 2) (s x : ZMod 2)]
      rw [← two_mul]
      have htwozero : (2 : ZMod 2) = 0 := by decide
      rw [htwozero, zero_mul]
    · intro x hx _
      exact fun h ↦ (Finset.mem_erase.mp hx).1 (hfix h)
    · intro x hx
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro hgz
      have hxz : x = z := by
        dsimp only [g] at hgz
        have hzadd : 2 * z = z + x := (sub_eq_iff_eq_add).mp hgz
        have hzx : z + z = z + x := by simpa [two_mul] using hzadd
        exact (add_left_cancel hzx).symm
      exact (Finset.mem_erase.mp hx).1 hxz
    · intro x _
      dsimp only [g]
      ring
  have hsum : ∑ x, f x = f z := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ z), hsumErase,
      zero_add]
  change (↑(∑ x, s x * s (2 * z - x)) : ZMod 2) = _
  rw [Nat.cast_sum]
  simp only [Nat.cast_mul]
  change (∑ x, f x) = _
  rw [hsum]
  have hzsub : 2 * z - z = z := by
    rw [sub_eq_iff_eq_add]
    simp [two_mul]
  simp [f, hzsub, pow_two]

def cyclicBinarySupport {r : ℕ} [NeZero r]
    (s : ZMod r → ℕ) : Finset (ZMod r) :=
  Finset.univ.filter fun z ↦ s z = 1

def cyclicOddConvolutionSupport {r : ℕ} [NeZero r]
    (s : ZMod r → ℕ) : Finset (ZMod r) :=
  Finset.univ.filter fun z ↦ Odd (cyclicSelfConvolution s z)

/-- For a binary row on an odd cyclic group, doubling bijects its support
onto the odd support of its self-convolution. -/
theorem card_cyclicOddConvolutionSupport_eq
    {r : ℕ} [NeZero r] (hr : Odd r)
    (s : ZMod r → ℕ) (hbinary : ∀ z, s z ≤ 1) :
    (cyclicOddConvolutionSupport s).card =
      (cyclicBinarySupport s).card := by
  have hcop : Nat.Coprime 2 r := Nat.coprime_two_left.mpr hr
  have hunit : IsUnit (2 : ZMod r) := by
    simpa using (ZMod.isUnit_iff_coprime 2 r).mpr hcop
  have hinj : Function.Injective (fun z : ZMod r ↦ 2 * z) :=
    hunit.mul_right_injective
  have hbij : Function.Bijective (fun z : ZMod r ↦ 2 * z) :=
    Finite.injective_iff_bijective.mp hinj
  have hodd (z : ZMod r) :
      Odd (cyclicSelfConvolution s (2 * z)) ↔ s z = 1 := by
    rw [← ZMod.natCast_eq_one_iff_odd]
    have hmod := cyclicSelfConvolution_double_mod_two hr s z
    rw [hmod]
    have hsquare (q : ZMod 2) : q ^ 2 = q := by
      fin_cases q <;> decide
    rw [hsquare]
    rw [ZMod.natCast_eq_one_iff_odd]
    constructor
    · intro hs
      have := hbinary z
      obtain ⟨k, hk⟩ := hs
      omega
    · intro hs
      rw [hs]
      exact odd_one
  have himage :
      (cyclicBinarySupport s).image (fun z : ZMod r ↦ 2 * z) =
        cyclicOddConvolutionSupport s := by
    ext y
    simp only [Finset.mem_image, cyclicBinarySupport,
      cyclicOddConvolutionSupport, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact (hodd z).mpr hz
    · intro hy
      obtain ⟨z, rfl⟩ := hbij.surjective y
      exact ⟨z, (hodd z).mp hy, rfl⟩
  rw [← himage, Finset.card_image_of_injective _ hinj]

/-- The terminal arithmetic contradiction in the cyclic parity argument. -/
theorem no_squareFamily_cyclic_cardinality
    {a r : ℕ} (ha : 4 ≤ a)
    (horder : r - 3 = a * (a - 1))
    (hparityCard : a = r - 3) : False := by
  rw [horder] at hparityCard
  have ham1 : 3 ≤ a - 1 := by omega
  have hlarge : 3 * a ≤ (a - 1) * a :=
    Nat.mul_le_mul_right a ham1
  nlinarith [hparityCard, hlarge]

/-- Uniform nonexistence of the cyclic almost-difference set produced by the
square-family descent.  No finite search or cyclotomic factorization is used:
the contradiction is entirely characteristic two. -/
theorem no_even_cyclic_two_hole_difference_set
    {a r : ℕ} [NeZero r]
    (ha : 4 ≤ a) (haeven : Even a) (hr : Odd r)
    (horder : r - 3 = a * (a - 1))
    (s : ZMod r → ℕ) (hbinary : ∀ z, s z ≤ 1)
    (hsupport : (cyclicBinarySupport s).card = a)
    (hconv : ∀ z, cyclicSelfConvolution s z =
      if z = 0 then a else if z = 1 ∨ z = -1 then 0 else 1) : False := by
  have hr3 : 3 ≤ r := by
    have hprod : 0 < a * (a - 1) := Nat.mul_pos (by omega) (by omega)
    omega
  have hminus : (-1 : ZMod r) ≠ 1 := by
    convert zmod_sub_one_ne_add_one_of_three_le hr3 (0 : ZMod r) using 1 <;> simp
  have hone : (1 : ZMod r) ≠ 0 := by
    intro h
    have : r = 1 := ZMod.one_eq_zero_iff.mp h
    omega
  have hzero : (0 : ZMod r) ≠ 1 := Ne.symm hone
  let forbidden : Finset (ZMod r) := {0, 1, -1}
  have hforbidden : forbidden.card = 3 := by
    simp [forbidden, hminus, hminus.symm, hone, hzero]
  have hoddsupport : cyclicOddConvolutionSupport s =
      Finset.univ \ forbidden := by
    ext z
    simp only [cyclicOddConvolutionSupport, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_sdiff, forbidden,
      Finset.mem_insert, Finset.mem_singleton]
    rw [hconv]
    by_cases hz0 : z = 0
    · simp [hz0, Nat.not_odd_iff_even.mpr haeven]
    by_cases hz1 : z = 1
    · subst z
      simp [hone]
    by_cases hzm1 : z = -1
    · subst z
      simp [hminus, hone]
    simp [hz0, hz1, hzm1, odd_one]
  have hoddcard : (cyclicOddConvolutionSupport s).card = r - 3 := by
    rw [hoddsupport, Finset.card_sdiff, Finset.card_univ, ZMod.card]
    rw [Finset.inter_eq_left.mpr (Finset.subset_univ forbidden), hforbidden]
  have hparity := card_cyclicOddConvolutionSupport_eq hr s hbinary
  have hacard : a = r - 3 := by omega
  exact no_squareFamily_cyclic_cardinality ha horder hacard

end Erdos85
