import Proofs.Erdos85QuadraticTraceField
import Proofs.Erdos85PrimeFourierSquare
import Proofs.Erdos85ZModProjectionFiber

/-!
# The nonsquare prime-frequency branch

If the frequency-pair scalar is not a square, its restricted operator has
zero trace.  The trace formula therefore makes the projected anchor Fourier
coefficient vanish.  At prime order all projected coefficients are equal,
contradicting the three-exception parity pattern when `p ≥ 7`.
-/

namespace Erdos85

open scoped BigOperators

noncomputable section

/-- A nonsquare quadratic operator and a twice-Fourier trace identity force
the Fourier coefficient to vanish. -/
theorem fourier_eq_zero_of_sq_eq_nonsquare_and_trace_eq_two_mul
    {K E : Type*} [Field K] [CharZero K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    {p : ℕ} [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (T : E →ₗ[K] E) (a : K) (c : ZMod p → ℤ)
    (ha : ¬ IsSquare a) (hTsq : T * T = a • LinearMap.id)
    (htrace : LinearMap.trace K E T =
      2 * ∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x) :
    ∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x = 0 := by
  have hzero := LinearMap.trace_eq_zero_of_sq_eq_nonsquare T a ha hTsq
  rw [hzero] at htrace
  exact (mul_eq_zero.mp htrace.symm).resolve_left two_ne_zero

/-- Prime Fourier vanishing is incompatible with a parity pattern having
exactly three exceptional residues once the prime has size at least seven. -/
theorem false_of_prime_fourier_zero_and_threePoint_parity
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp4 : 4 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (c : ZMod p → ℤ) (a : ZMod p)
    (hzero : ∑ x : ZMod p,
      (c x : K) * primitiveRootCharacter hζ x = 0)
    (hparity : ∀ x, Odd (c x) ↔
      x ∉ ({0, a, -a} : Finset (ZMod p))) : False := by
  let cFin : Fin p → ℤ := fun i ↦ c (ZMod.finEquiv p i)
  have hzeroFin : ∑ i : Fin p, (cFin i : K) * ζ ^ i.val = 0 := by
    calc
      (∑ i : Fin p, (cFin i : K) * ζ ^ i.val) =
          ∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x := by
            refine Fintype.sum_equiv (ZMod.finEquiv p) _ _ ?_
            intro i
            simp [cFin]
      _ = 0 := hzero
  have hall : ∀ i j, cFin i = cFin j :=
    all_eq_of_prime_fourier_eq_zero hp hζ cFin hzeroFin
  let exceptional : Finset (ZMod p) := {0, a, -a}
  have hcardExceptional : exceptional.card ≤ 3 := by
    exact Finset.card_le_three
  obtain ⟨y, hy⟩ : ∃ y : ZMod p, y ∉ exceptional := by
    by_contra h
    push_neg at h
    have hsubset : (Finset.univ : Finset (ZMod p)) ⊆ exceptional := by
      intro x _
      exact h x
    have hle := Finset.card_le_card hsubset
    have hcard : Fintype.card (ZMod p) = p := ZMod.card p
    rw [Finset.card_univ, hcard] at hle
    omega
  let i0 : Fin p := (ZMod.finEquiv p).symm 0
  let iy : Fin p := (ZMod.finEquiv p).symm y
  have heq : c 0 = c y := by
    simpa [cFin, i0, iy] using hall i0 iy
  have hzeroEven : ¬ Odd (c 0) := by
    rw [hparity]
    simp [exceptional]
  have hyOdd : Odd (c y) := by
    rw [hparity]
    exact hy
  exact hzeroEven (heq ▸ hyOdd)

/-- Complete abstract nonsquare branch: the operator identity supplies
Fourier vanishing and the projected parity pattern supplies the contradiction. -/
theorem false_of_nonsquare_frequencyPair_trace_and_threePoint_parity
    {K E : Type*} [Field K] [CharZero K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    {p : ℕ} [NeZero p] (hp : p.Prime) (hp4 : 4 ≤ p)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (T : E →ₗ[K] E) (scalar : K) (c : ZMod p → ℤ)
    (a : ZMod p) (hnonsquare : ¬ IsSquare scalar)
    (hTsq : T * T = scalar • LinearMap.id)
    (htrace : LinearMap.trace K E T =
      2 * ∑ x : ZMod p, (c x : K) * primitiveRootCharacter hζ x)
    (hparity : ∀ x, Odd (c x) ↔
      x ∉ ({0, a, -a} : Finset (ZMod p))) : False := by
  apply false_of_prime_fourier_zero_and_threePoint_parity hp hp4 hζ c a
  · exact fourier_eq_zero_of_sq_eq_nonsquare_and_trace_eq_two_mul
      hζ T scalar c hnonsquare hTsq htrace
  · exact hparity

end

end Erdos85
