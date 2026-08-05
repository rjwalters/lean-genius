import Proofs.Erdos85GraphAnchorParity

/-!
# Fibers of reduction between cyclic groups

If `p | r`, reduction `ZMod r → ZMod p` has fibers of cardinality `r/p`.
In particular the fibers are odd whenever that quotient is odd.
-/

namespace Erdos85

noncomputable section

theorem sum_card_projectionFiber
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (q : X → Y) :
    ∑ y, (projectionFiber q y).card = Fintype.card X := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset X)) (t := (Finset.univ : Finset Y))
    (f := q) (by intro x _; exact Finset.mem_univ (q x))
  simpa [projectionFiber] using h.symm

theorem card_projectionFiber_zmod_castHom
    {r p : ℕ} [NeZero r] [NeZero p] (hdiv : p ∣ r)
    (y : ZMod p) :
    (projectionFiber (ZMod.castHom hdiv (ZMod p)) y).card = r / p := by
  let q : ZMod r →+* ZMod p := ZMod.castHom hdiv (ZMod p)
  have hsurj : Function.Surjective q := ZMod.castHom_surjective hdiv
  have huniform : ∀ z : ZMod p,
      (projectionFiber q z).card = (projectionFiber q 0).card := by
    intro z
    have hz : z ∈ Set.range q := hsurj z
    have hzero : (0 : ZMod p) ∈ Set.range q := ⟨0, map_zero q⟩
    simpa [projectionFiber] using
      (AddMonoidHom.card_fiber_eq_of_mem_range q hz hzero)
  have htotal := sum_card_projectionFiber q
  have htotal' : ∑ z : ZMod p, (projectionFiber q z).card = r := by
    simpa only [ZMod.card] using htotal
  have hmul : p * (projectionFiber q 0).card = r := by
    calc
      p * (projectionFiber q 0).card =
          ∑ _z : ZMod p, (projectionFiber q 0).card := by
            simp [ZMod.card]
      _ = ∑ z : ZMod p, (projectionFiber q z).card := by
            apply Finset.sum_congr rfl
            intro z _
            exact (huniform z).symm
      _ = r := htotal'
  have hquot : (projectionFiber q 0).card = r / p := by
    have hp : 0 < p := NeZero.pos p
    apply Nat.eq_of_mul_eq_mul_left hp
    rw [hmul, Nat.mul_div_cancel' hdiv]
  rw [huniform y, hquot]

theorem odd_card_projectionFiber_zmod_castHom
    {r p : ℕ} [NeZero r] [NeZero p] (hdiv : p ∣ r)
    (hoddQuotient : Odd (r / p)) (y : ZMod p) :
    Odd (projectionFiber (ZMod.castHom hdiv (ZMod p)) y).card := by
  rw [card_projectionFiber_zmod_castHom hdiv y]
  exact hoddQuotient

theorem two_mul_mem_allowedCycleDifferences_iff
    {r : ℕ} [NeZero r] (hrOdd : Odd r) (hr3 : 3 ≤ r)
    (b h : ZMod r) (hdouble : b + b = 1) :
    2 * h ∈ allowedCycleDifferences r ↔
      h ∉ ({0, b, -b} : Finset (ZMod r)) := by
  have htwo : IsUnit (2 : ZMod r) := by
    simpa using (ZMod.isUnit_iff_coprime 2 r).mpr
      (Nat.coprime_two_left.mpr hrOdd)
  have hzero : 2 * h = 0 ↔ h = 0 := by
    constructor
    · intro hz
      exact htwo.mul_right_injective (by simpa using hz)
    · rintro rfl
      simp
  have hone : 2 * h = 1 ↔ h = b := by
    rw [← hdouble, ← two_mul b]
    exact htwo.mul_right_injective.eq_iff
  have hnegone : 2 * h = -1 ↔ h = -b := by
    have hb : 2 * (-b) = -1 := by
      rw [two_mul, ← neg_add, hdouble]
    rw [← hb]
    exact htwo.mul_right_injective.eq_iff
  simp only [allowedCycleDifferences, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton, not_or,
    hzero, hone, hnegone]

theorem card_castFiber_inter_threePoint
    {r p : ℕ} [NeZero r] [NeZero p]
    (hdiv : p ∣ r) (hp : 7 ≤ p) (hr : 7 ≤ r)
    (b : ZMod r) (hdouble : b + b = 1) :
    let q := ZMod.castHom hdiv (ZMod p)
    let a := q b
    ∀ y : ZMod p,
      ((projectionFiber q y) ∩ ({0, b, -b} : Finset (ZMod r))).card =
        if y ∈ ({0, a, -a} : Finset (ZMod p)) then 1 else 0 := by
  dsimp only
  let q := ZMod.castHom hdiv (ZMod p)
  let a := q b
  have haDouble : a + a = 1 := by
    dsimp only [a]
    rw [← map_add, hdouble, map_one]
  let bad : Finset (ZMod r) := {0, b, -b}
  let exceptional : Finset (ZMod p) := {0, a, -a}
  have himage : bad.image q = exceptional := by
    ext y
    simp [bad, exceptional, a, q, map_neg]
  have hbadCard : bad.card = 3 :=
    (threePoint_card_and_anchor_of_large_modulus hr b hdouble).1
  have hexceptionalCard : exceptional.card = 3 :=
    (threePoint_card_and_anchor_of_large_modulus hp a haDouble).1
  have hinj : Set.InjOn q bad := by
    rw [← Finset.card_image_iff]
    rw [himage, hbadCard, hexceptionalCard]
  intro y
  exact card_projectionFiber_inter_eq_indicator_of_image_injective
    (q := q) (bad := bad) (exceptional := exceptional) himage hinj y

theorem odd_projectedMultiplicity_zmod_castHom_iff
    {r p : ℕ} [NeZero r] [NeZero p]
    (hdiv : p ∣ r) (hp : 7 ≤ p) (hr : 7 ≤ r)
    (hrOdd : Odd r) (hoddQuotient : Odd (r / p))
    (b : ZMod r) (hdouble : b + b = 1)
    (m : ZMod r → ℕ)
    (hbase : ∀ h, Odd (m h) ↔
      2 * h ∈ allowedCycleDifferences r)
    (y : ZMod p) :
    let q := ZMod.castHom hdiv (ZMod p)
    let a := q b
    Odd (projectedMultiplicity q m y) ↔
      y ∉ ({0, a, -a} : Finset (ZMod p)) := by
  dsimp only
  let q := ZMod.castHom hdiv (ZMod p)
  let a := q b
  let bad : Finset (ZMod r) := {0, b, -b}
  let exceptional : Finset (ZMod p) := {0, a, -a}
  apply odd_projectedMultiplicity_iff_of_exception_bijection
    q m bad exceptional
  · intro z
    exact odd_card_projectionFiber_zmod_castHom hdiv hoddQuotient z
  · intro h
    rw [hbase h, two_mul_mem_allowedCycleDifferences_iff
      hrOdd (by omega) b h hdouble]
  · intro z
    exact card_castFiber_inter_threePoint hdiv hp hr b hdouble z

/-- Corrected end-to-end parity interface for the square Fourier branch. -/
theorem false_of_zmod_projection_and_convolution_constancy
    {r p : ℕ} [NeZero r] [NeZero p]
    (hdiv : p ∣ r) (hp : 7 ≤ p) (hr : 7 ≤ r)
    (hrOdd : Odd r) (hoddQuotient : Odd (r / p))
    (b : ZMod r) (hdouble : b + b = 1)
    (m : ZMod r → ℕ)
    (hbase : ∀ h, Odd (m h) ↔
      2 * h ∈ allowedCycleDifferences r)
    (hconstant :
      let q := ZMod.castHom hdiv (ZMod p)
      let a := q b
      ∀ g, g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) →
        cyclicConvolution
            (fun y ↦ (projectedMultiplicity q m y : ℤ))
            (fun y ↦ (projectedMultiplicity q m y : ℤ)) a =
          cyclicConvolution
            (fun y ↦ (projectedMultiplicity q m y : ℤ))
            (fun y ↦ (projectedMultiplicity q m y : ℤ)) g) : False := by
  dsimp only at hconstant ⊢
  let q := ZMod.castHom hdiv (ZMod p)
  let a := q b
  have haDouble : a + a = 1 := by
    dsimp only [a, q]
    rw [← map_add, hdouble, map_one]
  have hodd : ∀ y, Odd (projectedMultiplicity q m y) ↔
      y ∉ ({0, a, -a} : Finset (ZMod p)) := by
    intro y
    exact odd_projectedMultiplicity_zmod_castHom_iff
      hdiv hp hr hrOdd hoddQuotient b hdouble m hbase y
  obtain ⟨e, he⟩ := exists_integer_error_of_odd_iff
    (projectedMultiplicity q m) ({0, a, -a} : Finset (ZMod p)) hodd
  exact false_of_large_threePoint_convolution_pattern hp a haDouble
    (fun y ↦ (projectedMultiplicity q m y : ℤ)) e he hconstant

end

end Erdos85
