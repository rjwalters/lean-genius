import Mathlib

/-
  # Entropy of an `n`-fold i.i.d. source: `H(p^{⊗n}) = n · H(p)`

  The parent file `ShannonSourceCodingWIP01` proves **pairwise additivity** of
  Shannon entropy for independent sources,

      H(pX ⊗ pY) = H(pX) + H(pY)      (product distribution `pXY(x,y) = pX x · pY y`).

  This file **iterates** that identity to the `n`-fold i.i.d. product. For a
  distribution `p : α → ℝ` normalised by `∑ₐ p a = 1`, the product distribution

      p^{⊗n}(x) = ∏ᵢ p (xᵢ)          (`x : Fin n → α`)

  has entropy

      H(p^{⊗n}) = n · H(p).

  This is the source-coding statement that a block of `n` i.i.d. symbols carries
  `n · H(p)` bits — the quantitative backbone of the AEP and of the rate `H` in
  Shannon's source coding theorem.

  The proof is a clean induction on `n` along the tuple recursion
  `Fin (n+1) → α ≃ α × (Fin n → α)` (`Fin.consEquiv`): splitting off the first
  coordinate turns `p^{⊗(n+1)}` into the product distribution `p ⊗ p^{⊗n}`, so
  the pairwise additivity `entropy_prod` (reproved locally to keep the file
  self-contained) contributes one `H(p)` at each step. Normalisation of the
  product distribution (`sum_prodDist`, `∑ₓ ∏ᵢ p (xᵢ) = (∑ₐ p a)^n`) supplies the
  hypothesis `∑ p^{⊗n} = 1` that the additivity step consumes.

  ## Results
  * `entropy_prod`  : `H(pX ⊗ pY) = H(pX) + H(pY)` (pairwise, parent's result).
  * `sum_prodDist`  : `∑ₓ ∏ᵢ p (xᵢ) = (∑ₐ p a)^n` (product distribution is
    normalised when `p` is).
  * `entropy_pow`   : **`H(p^{⊗n}) = n · H(p)`** for a normalised `p`.

  `0` axioms.
-/

namespace ShannonSourceCodingWIP01OQ01

open Real Finset

variable {α : Type*} [Fintype α]

/-- Shannon entropy in `negMulLog` form (as in the parent `ShannonSourceCodingWIP01`):
`H(p) = ∑ₓ negMulLog (p x)`, agreeing with the standard `-∑ₓ p x · log (p x)`. -/
noncomputable def entropy (p : α → ℝ) : ℝ := ∑ x, Real.negMulLog (p x)

/-- **Pairwise additivity of entropy for independent sources.** For a product
distribution `pXY(x,y) = pX x · pY y` with `∑ pX = ∑ pY = 1`,

  `H(pX ⊗ pY) = H(pX) + H(pY)`.

This is the parent file's `entropy_prod`, reproved locally so this file is
self-contained; it is the atomic step iterated by `entropy_pow`. -/
theorem entropy_prod {β : Type*} [Fintype β] (pX : α → ℝ) (pY : β → ℝ)
    (hX : ∑ x, pX x = 1) (hY : ∑ y, pY y = 1) :
    entropy (fun xy : α × β => pX xy.1 * pY xy.2) = entropy pX + entropy pY := by
  unfold entropy
  rw [Fintype.sum_prod_type]
  have key : ∀ x, (∑ y, Real.negMulLog (pX x * pY y))
      = Real.negMulLog (pX x) + pX x * ∑ y, Real.negMulLog (pY y) := by
    intro x
    simp_rw [Real.negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hY, one_mul, ← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => key x, Finset.sum_add_distrib,
    ← Finset.sum_mul, hX, one_mul]

/-- The `n`-fold i.i.d. product distribution `p^{⊗n}(x) = ∏ᵢ p (xᵢ)` on
`Fin n → α`. -/
noncomputable def prodDist (p : α → ℝ) (n : ℕ) : (Fin n → α) → ℝ :=
  fun x => ∏ i, p (x i)

/-- **Normalisation of the product distribution.** The total mass of `p^{⊗n}` is
`(∑ₐ p a)^n`; in particular a normalised `p` (with `∑ₐ p a = 1`) gives a
normalised `p^{⊗n}`. Proved by induction along the tuple recursion. -/
theorem sum_prodDist (p : α → ℝ) (n : ℕ) :
    ∑ x, prodDist p n x = (∑ a, p a) ^ n := by
  induction n with
  | zero => simp [prodDist]
  | succ n ih =>
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => α))
        (prodDist p (n + 1))]
      have step : ∀ ar : α × (Fin n → α),
          prodDist p (n + 1) (Fin.consEquiv (fun _ : Fin (n + 1) => α) ar)
            = p ar.1 * prodDist p n ar.2 := by
        rintro ⟨a, s⟩
        simp only [prodDist, Fin.consEquiv_apply, Fin.prod_univ_succ,
          Fin.cons_zero, Fin.cons_succ]
      rw [Finset.sum_congr rfl fun ar _ => step ar, Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, ih]
      ring

/-- **Entropy of an `n`-fold i.i.d. source.** For a distribution `p` with
`∑ₐ p a = 1`, the entropy of the product distribution `p^{⊗n}` on `Fin n → α` is

  `H(p^{⊗n}) = n · H(p)`.

Obtained by iterating the pairwise additivity `entropy_prod` along the tuple
recursion `Fin (n+1) → α ≃ α × (Fin n → α)`: each step splits off one coordinate,
contributing one factor `H(p)`. -/
theorem entropy_pow (p : α → ℝ) (hp : ∑ a, p a = 1) (n : ℕ) :
    entropy (prodDist p n) = n * entropy p := by
  induction n with
  | zero => simp [entropy, prodDist]
  | succ n ih =>
      have hrw : entropy (prodDist p (n + 1))
          = entropy (fun ar : α × (Fin n → α) => p ar.1 * prodDist p n ar.2) := by
        unfold entropy
        rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => α))
          (fun x => Real.negMulLog (prodDist p (n + 1) x))]
        apply Finset.sum_congr rfl
        rintro ⟨a, s⟩ _
        simp only [prodDist, Fin.consEquiv_apply, Fin.prod_univ_succ,
          Fin.cons_zero, Fin.cons_succ]
      rw [hrw, entropy_prod p (prodDist p n) hp
        (by rw [sum_prodDist, hp, one_pow]), ih]
      push_cast
      ring

end ShannonSourceCodingWIP01OQ01
