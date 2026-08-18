import Proofs.Erdos85PrimeConvolutionObstruction
import Mathlib.Algebra.BigOperators.Ring.Nat

/-!
# Parity under projection to a cyclic quotient

This is the abstract parity step in the graph-to-Fourier bridge.  If every
fiber of a quotient map has odd cardinality, then summing multiplicities
whose parity is the pullback of a base pattern preserves that pattern.
-/

namespace Erdos85

open scoped BigOperators

noncomputable section

variable {X Y : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]

def projectionFiber (q : X → Y) (y : Y) : Finset X :=
  Finset.univ.filter fun x ↦ q x = y

def projectedMultiplicity (q : X → Y) (m : X → ℕ) (y : Y) : ℕ :=
  ∑ x ∈ projectionFiber q y, m x

theorem card_projectionFiber_inter_eq_indicator_of_image_injective
    (q : X → Y) (bad : Finset X) (exceptional : Finset Y)
    (himage : bad.image q = exceptional)
    (hinj : Set.InjOn q bad) (y : Y) :
    ((projectionFiber q y) ∩ bad).card =
      if y ∈ exceptional then 1 else 0 := by
  split_ifs with hy
  · rw [← himage] at hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    have heq : projectionFiber q y ∩ bad = {x} := by
      ext z
      simp only [Finset.mem_inter, projectionFiber, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨hzq, hzb⟩
        exact hinj hzb hx (hzq.trans hxy.symm)
      · intro hzx
        subst z
        exact ⟨hxy, hx⟩
    rw [heq]
    simp
  · have heq : projectionFiber q y ∩ bad = ∅ := by
      ext x
      simp only [Finset.mem_inter, projectionFiber, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨hxq, hxb⟩
      apply hy
      rw [← himage]
      exact Finset.mem_image.mpr ⟨x, hxb, hxq⟩
    rw [heq]
    simp

/-- Odd fibers preserve a parity pattern pulled back from the quotient. -/
theorem odd_projectedMultiplicity_iff
    (q : X → Y) (m : X → ℕ) (exceptional : Finset Y)
    (hfiber : ∀ y, Odd (projectionFiber q y).card)
    (hparity : ∀ x, Odd (m x) ↔ q x ∉ exceptional) (y : Y) :
    Odd (projectedMultiplicity q m y) ↔ y ∉ exceptional := by
  unfold projectedMultiplicity
  rw [Finset.odd_sum_iff_odd_card_odd]
  by_cases hy : y ∈ exceptional
  · have hempty :
        (projectionFiber q y).filter (fun x ↦ Odd (m x)) = ∅ := by
      ext x
      simp only [projectionFiber, Finset.mem_filter, Finset.mem_univ,
        true_and, hparity, Finset.notMem_empty, iff_false]
      rintro ⟨hxy, hx⟩
      exact hx (hxy.symm ▸ hy)
    rw [hempty]
    simp [hy]
  · have hfull :
        (projectionFiber q y).filter (fun x ↦ Odd (m x)) =
          projectionFiber q y := by
      ext x
      simp only [projectionFiber, Finset.mem_filter, Finset.mem_univ,
        true_and, hparity]
      constructor
      · exact And.left
      · intro hxy
        exact ⟨hxy, hxy ▸ hy⟩
    rw [hfull]
    simpa [hy] using hfiber y

/-- Correct projection principle for a finite exceptional set.  Odd base
multiplicities occur off `bad`; every quotient fiber is odd; and each
exceptional quotient fiber contains exactly one bad point. -/
theorem odd_projectedMultiplicity_iff_of_exception_bijection
    (q : X → Y) (m : X → ℕ) (bad : Finset X)
    (exceptional : Finset Y)
    (hfiber : ∀ y, Odd (projectionFiber q y).card)
    (hparity : ∀ x, Odd (m x) ↔ x ∉ bad)
    (hbadFiber : ∀ y,
      ((projectionFiber q y) ∩ bad).card = if y ∈ exceptional then 1 else 0)
    (y : Y) :
    Odd (projectedMultiplicity q m y) ↔ y ∉ exceptional := by
  unfold projectedMultiplicity
  rw [Finset.odd_sum_iff_odd_card_odd]
  have hfilter :
      (projectionFiber q y).filter (fun x ↦ Odd (m x)) =
        projectionFiber q y \ bad := by
    ext x
    simp [hparity]
  rw [hfilter, Finset.card_sdiff]
  rw [Finset.inter_comm bad (projectionFiber q y), hbadFiber y]
  by_cases hy : y ∈ exceptional
  · simp only [if_pos hy]
    have hpos : 0 < (projectionFiber q y).card := by
      obtain ⟨k, hk⟩ := hfiber y
      omega
    have heven : Even ((projectionFiber q y).card - 1) := by
      obtain ⟨k, hk⟩ := hfiber y
      refine ⟨k, ?_⟩
      omega
    exact ⟨fun ho _ ↦ (Nat.not_odd_iff_even.mpr heven) ho,
      fun hnot ↦ False.elim (hnot hy)⟩
  · simp only [if_neg hy, Nat.sub_zero]
    exact ⟨fun _ ↦ hy, fun _ ↦ hfiber y⟩

/-- A natural-valued multiplicity with a prescribed parity pattern admits
the integral `indicator + 2e` presentation required by the mod-four
convolution lemma. -/
theorem exists_integer_error_of_odd_iff
    (c : Y → ℕ) (exceptional : Finset Y)
    (hodd : ∀ y, Odd (c y) ↔ y ∉ exceptional) :
    ∃ e : Y → ℤ, ∀ y,
      (c y : ℤ) = (1 - integerIndicator exceptional y) + 2 * e y := by
  have hex : ∀ y, ∃ z : ℤ,
      (c y : ℤ) = (1 - integerIndicator exceptional y) + 2 * z := by
    intro y
    by_cases hy : y ∈ exceptional
    · have heven : Even (c y) :=
        Nat.not_odd_iff_even.mp (fun ho ↦ (hodd y).mp ho hy)
      obtain ⟨k, hk⟩ := heven
      refine ⟨(k : ℤ), ?_⟩
      simp [integerIndicator, hy]
      omega
    · obtain ⟨k, hk⟩ := (hodd y).mpr hy
      refine ⟨(k : ℤ), ?_⟩
      simp [integerIndicator, hy]
      omega
  choose e he using hex
  exact ⟨e, he⟩

/-- End-to-end abstract interface for the graph-facing parity bridge.  Once
the graph supplies an odd-fiber projection, the base parity pattern, and
the square-branch convolution constancy, the uniform `p ≥ 7` contradiction
is automatic. -/
theorem false_of_odd_fiber_projection_and_convolution_constancy
    {p : ℕ} [NeZero p] (hp : 7 ≤ p)
    (a : ZMod p) (hdouble : a + a = 1)
    (q : X → ZMod p) (m : X → ℕ)
    (hfiber : ∀ y, Odd (projectionFiber q y).card)
    (hbaseParity : ∀ x, Odd (m x) ↔
      q x ∉ ({0, a, -a} : Finset (ZMod p)))
    (hconstant : ∀ g,
      g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) →
      cyclicConvolution
          (fun y ↦ (projectedMultiplicity q m y : ℤ))
          (fun y ↦ (projectedMultiplicity q m y : ℤ)) a =
        cyclicConvolution
          (fun y ↦ (projectedMultiplicity q m y : ℤ))
          (fun y ↦ (projectedMultiplicity q m y : ℤ)) g) : False := by
  let exceptional : Finset (ZMod p) := {0, a, -a}
  have hodd : ∀ y, Odd (projectedMultiplicity q m y) ↔
      y ∉ exceptional := by
    intro y
    exact odd_projectedMultiplicity_iff q m exceptional hfiber
      hbaseParity y
  obtain ⟨e, he⟩ := exists_integer_error_of_odd_iff
    (projectedMultiplicity q m) exceptional hodd
  exact false_of_large_threePoint_convolution_pattern hp a hdouble
    (fun y ↦ (projectedMultiplicity q m y : ℤ)) e he hconstant

end

end Erdos85
