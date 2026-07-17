/-
# Erdős #490 — the Cauchy–Schwarz energy–product bound

`Erdos490Problem` develops the multiplicative-energy `E(A, B)` of two finite sets of
naturals: it proves the *lower* bound `|A|·|B| ≤ E(A, B)` (minimized exactly at distinct
products, `distinct_minimal_energy`) and several *upper* bounds
(`multiplicativeEnergy_le_sq`, `multiplicativeEnergy_le_sq_mul`,
`multiplicativeEnergy_le_mul_sq`).  What it lacks is the single inequality that makes the
"energy method" a method: the **Cauchy–Schwarz bound** relating the energy to the size of
the *product set* `A·B`,

  |A|²·|B|² ≤ |A·B| · E(A, B).

Equivalently `|A·B| ≥ |A|²|B|² / E(A, B)`: **small energy forces a large product set**.
This is the estimate through which extra multiplicative structure (a small `A·B`) is
converted into a large collision count `E`, and vice versa — precisely the mechanism
behind the Szemerédi/Erdős analysis of distinct products.

The heavy lifting is Mathlib's `Finset.le_card_mul_mul_mulEnergy`; the content here is to
*bridge* the file's bespoke `multiplicativeEnergy` / `productSet` to Mathlib's
`Finset.mulEnergy` / pointwise `A * B`, then read off the bound and its corollaries.  A
closing sharpness result shows the Cauchy–Schwarz inequality becomes an **equality exactly
at the distinct-products (extremal) configuration** — tying the general estimate back to
the Erdős #490 optimum.

All results are `0`-axiom (`#print axioms` = `[propext, Classical.choice, Quot.sound]`).
-/

import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Proofs.Erdos490Problem

open Finset
open scoped Pointwise

namespace Erdos490

/-!
## Bridges to Mathlib's pointwise / energy API
-/

/-- **Energy bridge.** The file's `multiplicativeEnergy` is Mathlib's `Finset.mulEnergy`:
both count the quadruples `((a₁, a₂), (b₁, b₂)) ∈ (A ×ˢ A) ×ˢ (B ×ˢ B)` with
`a₁·b₁ = a₂·b₂`; the two definitions differ only in how the defining predicate is spelled
(a pattern-matching lambda vs. projections). -/
theorem multiplicativeEnergy_eq_mulEnergy (A B : Finset ℕ) :
    multiplicativeEnergy A B = Finset.mulEnergy A B := by
  unfold multiplicativeEnergy Finset.mulEnergy
  congr 1

/-- **Product-set bridge.** The file's `productSet A B = {a·b : a ∈ A, b ∈ B}` is the
pointwise product finset `A * B`. -/
theorem productSet_eq_mul (A B : Finset ℕ) :
    productSet A B = A * B := by
  ext n
  simp only [productSet_eq_image, Finset.mem_image, Finset.mem_product, Finset.mem_mul]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-!
## The Cauchy–Schwarz energy–product bound
-/

/-- **Cauchy–Schwarz energy–product bound**: `(|A|·|B|)² ≤ |A·B| · E(A, B)`.

Writing `r(x) = #{(a, b) ∈ A × B : a·b = x}` for the number of representations of `x` as a
product, one has `|A||B| = ∑_{x ∈ A·B} r(x)` and `E(A, B) = ∑_{x ∈ A·B} r(x)²`; Cauchy–
Schwarz `(∑ r)² ≤ |A·B|·∑ r²` is exactly this inequality.  (Delegated to Mathlib's
`Finset.le_card_mul_mul_mulEnergy` through the two bridges above.) -/
theorem card_sq_le_card_productSet_mul_energy (A B : Finset ℕ) :
    (A.card * B.card) ^ 2 ≤ (productSet A B).card * multiplicativeEnergy A B := by
  rw [productSet_eq_mul, multiplicativeEnergy_eq_mulEnergy, mul_pow]
  exact Finset.le_card_mul_mul_mulEnergy A B

/-- **Product set is controlled below by the energy** (real form):
`|A·B| ≥ |A|²·|B|² / E(A, B)`.  This is the applied shape of the Cauchy–Schwarz bound:
the smaller the multiplicative energy, the larger the product set must be. -/
theorem card_productSet_ge_div (A B : Finset ℕ) (hE : 0 < multiplicativeEnergy A B) :
    ((A.card : ℝ) * B.card) ^ 2 / multiplicativeEnergy A B ≤ (productSet A B).card := by
  rw [div_le_iff₀ (show (0 : ℝ) < multiplicativeEnergy A B by exact_mod_cast hE)]
  calc ((A.card : ℝ) * B.card) ^ 2
      = ((A.card * B.card) ^ 2 : ℕ) := by push_cast; ring
    _ ≤ ((productSet A B).card * multiplicativeEnergy A B : ℕ) := by
        exact_mod_cast card_sq_le_card_productSet_mul_energy A B
    _ = (productSet A B).card * (multiplicativeEnergy A B : ℝ) := by push_cast; ring

/-- **The energy also dominates via the product set** (real form):
`E(A, B) ≥ |A|²·|B|² / |A·B|`.  The dual reading of Cauchy–Schwarz: a small product set
forces a large collision count.  Together with `multiplicativeEnergy_ge`
(`|A||B| ≤ E`) this pins the energy between `|A||B|` and, at the distinct-products
extreme, its Cauchy–Schwarz floor `(|A||B|)²/|A·B| = |A||B|`. -/
theorem energy_ge_div (A B : Finset ℕ) (hP : (productSet A B).Nonempty) :
    ((A.card : ℝ) * B.card) ^ 2 / (productSet A B).card ≤ multiplicativeEnergy A B := by
  have hPpos : (0 : ℝ) < (productSet A B).card := by exact_mod_cast hP.card_pos
  rw [div_le_iff₀ hPpos]
  calc ((A.card : ℝ) * B.card) ^ 2
      = ((A.card * B.card) ^ 2 : ℕ) := by push_cast; ring
    _ ≤ ((productSet A B).card * multiplicativeEnergy A B : ℕ) := by
        exact_mod_cast card_sq_le_card_productSet_mul_energy A B
    _ = (multiplicativeEnergy A B : ℝ) * (productSet A B).card := by push_cast; ring

/-!
## Sharpness and a worked application
-/

/-- **The Cauchy–Schwarz bound is sharp exactly at the distinct-products optimum.**
When all products are distinct, `|A·B| = |A||B|` (definition of `HasDistinctProducts`)
and `E(A, B) = |A||B|` (`distinct_minimal_energy`), so both sides of the bound equal
`(|A||B|)²`.  Thus the extremal configuration of Erdős #490 is precisely the equality case
of the energy–product inequality. -/
theorem card_sq_eq_card_productSet_mul_energy_of_distinct
    {A B : Finset ℕ} (h : HasDistinctProducts A B) :
    (A.card * B.card) ^ 2 = (productSet A B).card * multiplicativeEnergy A B := by
  have hP : (productSet A B).card = A.card * B.card := h
  have hE : multiplicativeEnergy A B = A.card * B.card :=
    (distinct_minimal_energy A B).mp h
  rw [hP, hE, sq]

/-- **Worked application of the energy method**: if `0 ∉ B` then `|A| ≤ |A·B|`.
Chain the Cauchy–Schwarz lower bound `(|A||B|)² ≤ |A·B|·E` with the sharp energy upper
bound `E ≤ |A|·|B|²` (`multiplicativeEnergy_le_mul_sq`, valid for `0 ∉ B`) and cancel the
common positive factor `|A|·|B|²`.  (Symmetrically `|B| ≤ |A·B|` when `0 ∉ A`.)  A small
illustration that the abstract inequality has concrete extremal-combinatorics teeth. -/
theorem card_le_card_productSet_of_zero_not_mem
    {A B : Finset ℕ} (hB : (0 : ℕ) ∉ B) (hA : A.Nonempty) (hBne : B.Nonempty) :
    A.card ≤ (productSet A B).card := by
  have hCS := card_sq_le_card_productSet_mul_energy A B
  have hUB := multiplicativeEnergy_le_mul_sq (A := A) (B := B) hB
  have hchain : A.card * (A.card * B.card ^ 2)
      ≤ (productSet A B).card * (A.card * B.card ^ 2) :=
    calc A.card * (A.card * B.card ^ 2)
        = (A.card * B.card) ^ 2 := by ring
      _ ≤ (productSet A B).card * multiplicativeEnergy A B := hCS
      _ ≤ (productSet A B).card * (A.card * B.card ^ 2) :=
          Nat.mul_le_mul (le_refl _) hUB
  have hpos : 0 < A.card * B.card ^ 2 :=
    Nat.mul_pos hA.card_pos (pow_pos hBne.card_pos 2)
  exact Nat.le_of_mul_le_mul_right hchain hpos

end Erdos490
