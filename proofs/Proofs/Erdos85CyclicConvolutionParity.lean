import Proofs.Erdos85PrimeFourier

/-!
# Mod-four rigidity of cyclic self-convolution

If two integral functions on a finite abelian group agree modulo two, their
self-convolutions agree modulo four.  This is the parity engine in the
square-cyclotomic branch of the equal-cycle argument.
-/

namespace Erdos85

open scoped BigOperators

noncomputable section

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [AddCommGroup Z]

/-- Additive cyclic convolution, written in the orientation used by the
Fourier square `H(X)^2`. -/
def cyclicConvolution (f g : Z → ℤ) (t : Z) : ℤ :=
  ∑ x, f x * g (t - x)

/-- Convolution on a finite abelian group is commutative. -/
theorem cyclicConvolution_comm (f g : Z → ℤ) (t : Z) :
    cyclicConvolution f g t = cyclicConvolution g f t := by
  let e : Z ≃ Z :=
    { toFun := fun x ↦ t - x
      invFun := fun x ↦ t - x
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  unfold cyclicConvolution
  apply Fintype.sum_equiv e
  intro x
  have h : t - (t - x) = x := by abel
  change f x * g (t - x) = g (t - x) * f (t - (t - x))
  rw [h, mul_comm]

/-- Exact expansion when `c=b+2e`. -/
theorem cyclicConvolution_add_twice
    (b e : Z → ℤ) (t : Z) :
    cyclicConvolution (fun x ↦ b x + 2 * e x)
        (fun x ↦ b x + 2 * e x) t =
      cyclicConvolution b b t +
        4 * (cyclicConvolution b e t + cyclicConvolution e e t) := by
  unfold cyclicConvolution
  have hcomm : (∑ x, e x * b (t - x)) = ∑ x, b x * e (t - x) := by
    simpa only [cyclicConvolution] using cyclicConvolution_comm e b t
  have hcross : (∑ x, 2 * (b x * e (t - x) + e x * b (t - x))) =
      4 * ∑ x, b x * e (t - x) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib, hcomm]
    ring
  have hfour : (∑ x, 4 * e x * e (t - x)) =
      4 * ∑ x, e x * e (t - x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  calc
    (∑ x, (b x + 2 * e x) * (b (t - x) + 2 * e (t - x))) =
        ∑ x, (b x * b (t - x) +
          2 * (b x * e (t - x) + e x * b (t - x)) +
          4 * e x * e (t - x)) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = (∑ x, b x * b (t - x)) +
        4 * ((∑ x, b x * e (t - x)) +
          ∑ x, e x * e (t - x)) := by
            simp only [Finset.sum_add_distrib]
            rw [hcross, hfour]
            ring

/-- Pointwise agreement modulo two forces self-convolution agreement modulo
four.  The witness form is convenient for graph multiplicities. -/
theorem cyclicConvolution_mod_four_of_eq_add_twice
    (c b e : Z → ℤ) (h : ∀ x, c x = b x + 2 * e x) (t : Z) :
    cyclicConvolution c c t % 4 = cyclicConvolution b b t % 4 := by
  have hc : c = fun x ↦ b x + 2 * e x := by
    funext x
    exact h x
  rw [hc, cyclicConvolution_add_twice]
  omega

/-- The terminal mod-four obstruction.  If `c*c` is constant at two residues
but the corresponding parity-pattern convolutions differ by two, no integral
lift `c = b + 2e` can exist. -/
theorem false_of_cyclicConvolution_constant_and_parity_gap_two
    (c b e : Z → ℤ) (a g : Z)
    (hparity : ∀ x, c x = b x + 2 * e x)
    (hconstant : cyclicConvolution c c a = cyclicConvolution c c g)
    (P : ℤ)
    (ha : cyclicConvolution b b a = P - 4)
    (hg : cyclicConvolution b b g = P - 6) : False := by
  have hmoda := cyclicConvolution_mod_four_of_eq_add_twice c b e hparity a
  have hmodg := cyclicConvolution_mod_four_of_eq_add_twice c b e hparity g
  rw [hconstant, ha] at hmoda
  rw [hg] at hmodg
  omega

end

end Erdos85
