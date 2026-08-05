import Proofs.Erdos85GraphProjectedConvolutionTerminal

/-!
# Prime Fourier relation implies convolution constancy

This file isolates the cyclotomic coefficient step in the square branch.
If the Fourier transform of `c*c-s` vanishes at a primitive prime root and
`s` is supported on the special residues, then `c*c` is constant away from
that support.
-/

namespace Erdos85

open scoped BigOperators

noncomputable section

theorem cyclicConvolution_constant_off_support_of_prime_fourier_zero
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (c s : ZMod p → ℤ) (special : Finset (ZMod p))
    (hsupport : ∀ t, t ∉ special → s t = 0)
    (hzero : ∑ i : Fin p,
      (((cyclicConvolution c c (ZMod.finEquiv p i) -
        s (ZMod.finEquiv p i) : ℤ) : K) * ζ ^ i.val) = 0) :
    ∀ x y, x ∉ special → y ∉ special →
      cyclicConvolution c c x = cyclicConvolution c c y := by
  let coeff : Fin p → ℤ := fun i ↦
    cyclicConvolution c c (ZMod.finEquiv p i) - s (ZMod.finEquiv p i)
  have hall := all_eq_of_prime_fourier_eq_zero hp hζ coeff (by
    simpa only [coeff] using hzero)
  intro x y hx hy
  let ix : Fin p := (ZMod.finEquiv p).symm x
  let iy : Fin p := (ZMod.finEquiv p).symm y
  have heq := hall ix iy
  dsimp only [coeff] at heq
  dsimp only [ix, iy] at heq
  have hix : ZMod.finEquiv p ((ZMod.finEquiv p).symm x) = x :=
    (ZMod.finEquiv p).apply_symm_apply x
  have hiy : ZMod.finEquiv p ((ZMod.finEquiv p).symm y) = y :=
    (ZMod.finEquiv p).apply_symm_apply y
  rw [hix, hiy,
    hsupport x hx, hsupport y hy, sub_zero, sub_zero] at heq
  exact heq

/-- The form consumed by the graph terminal, with the five residues covering
both the parity holes and the three Fourier correction coefficients. -/
theorem cyclicConvolution_anchor_constant_of_prime_fourier_zero
    {K : Type*} [Field K] [CharZero K]
    {p : ℕ} [NeZero p] (hp : p.Prime)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (c s : ZMod p → ℤ) (a : ZMod p)
    (hsupport : ∀ t,
      t ∉ ({0, 1, -1} : Finset (ZMod p)) → s t = 0)
    (hzero : ∑ i : Fin p,
      (((cyclicConvolution c c (ZMod.finEquiv p i) -
        s (ZMod.finEquiv p i) : ℤ) : K) * ζ ^ i.val) = 0)
    (ha : a ∉ ({0, 1, -1} : Finset (ZMod p))) :
    ∀ g, g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) →
      cyclicConvolution c c a = cyclicConvolution c c g := by
  have hconst := cyclicConvolution_constant_off_support_of_prime_fourier_zero
    hp hζ c s ({0, 1, -1} : Finset (ZMod p)) hsupport hzero
  intro g hg
  apply hconst a g ha
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hg ⊢
  exact ⟨hg.1, hg.2.2.2.1, hg.2.2.2.2⟩

end

end Erdos85
