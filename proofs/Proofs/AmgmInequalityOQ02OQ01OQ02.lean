/-
  Off-Diagonal Symmetry: Σ_{i≠j} xᵢxⱼ = 2 · Σ_{i<j} xᵢxⱼ

  Open Question (amgm-inequality-oq-02-oq-01-oq-02):
  Show that the off-diagonal sum Σ_{i≠j} xᵢxⱼ equals 2 · e₂,
  where e₂ = Σ_{i<j} xᵢxⱼ is the second elementary symmetric polynomial.

  This completes the Newton-Girard decomposition:
    (Σ xᵢ)² = Σ xᵢ² + Σ_{i≠j} xᵢxⱼ = Σ xᵢ² + 2·Σ_{i<j} xᵢxⱼ

  Proof strategy: pair each (i,j) with i≠j with its transpose (j,i).
  Since xᵢxⱼ = xⱼxᵢ, the off-diagonal sum double-counts each i<j pair.

  Axioms: 0, Sorries: 0
  Tags: algebra, symmetric-functions, combinatorics, Newton-Girard
-/

import Mathlib
import Proofs.AmgmInequalityOQ02OQ01

namespace AMGMInequalityOQ02OQ01OQ02

open Finset BigOperators

variable {R : Type*} [CommRing R]

-- ============================================================
-- Part I: Decomposing offDiag into Upper and Lower Triangular Parts
-- ============================================================

/-- The off-diagonal pairs split into {(i,j) | i < j} �� {(i,j) | j < i}. -/
theorem offDiag_eq_upper_union_lower {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (s : Finset ι) :
    s.offDiag = s.offDiag.filter (fun p => p.1 < p.2) ∪
                s.offDiag.filter (fun p => p.2 < p.1) := by
  ext ⟨a, b⟩
  simp only [mem_union, mem_filter, Finset.mem_offDiag]
  constructor
  · intro ⟨ha, hb, hab⟩
    rcases lt_or_gt_of_ne hab with h | h
    · exact Or.inl ⟨⟨ha, hb, hab⟩, h⟩
    · exact Or.inr ⟨⟨ha, hb, hab⟩, h⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

/-- The upper and lower triangular parts are disjoint. -/
theorem upper_lower_disjoint {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (s : Finset ι) :
    Disjoint (s.offDiag.filter (fun p => p.1 < p.2))
             (s.offDiag.filter (fun p => p.2 < p.1)) := by
  rw [Finset.disjoint_filter]
  exact fun _ _ h1 h2 => absurd (lt_trans h1 h2) (lt_irrefl _)

-- ============================================================
-- Part II: Swap Image Lemma
-- ============================================================

/-- Swapping coordinates maps the lower-triangular part to the upper-triangular part. -/
theorem image_swap_lower_eq_upper {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (s : Finset ι) :
    (s.offDiag.filter (fun p => p.2 < p.1)).image Prod.swap =
     s.offDiag.filter (fun p => p.1 < p.2) := by
  ext ⟨a, b⟩
  simp only [mem_image, mem_filter, Finset.mem_offDiag, Prod.swap, Prod.exists]
  constructor
  · rintro ⟨c, d, ⟨⟨hc, hd, hne⟩, hlt⟩, hcd⟩
    cases hcd
    exact ⟨⟨hd, hc, Ne.symm hne⟩, hlt⟩
  · intro ⟨⟨ha, hb, hab⟩, hlt⟩
    exact ⟨b, a, ⟨⟨hb, ha, Ne.symm hab⟩, hlt⟩, rfl⟩

-- ============================================================
-- Part III: Core Symmetry Theorem
-- ============================================================

/-- For a symmetric function f(i,j) = f(j,i), the sum over the lower-triangular part
    equals the sum over the upper-triangular part.

    Proof: rewrite f(a,b) = f(b,a) = f(swap(a,b)) on the lower-triangular sum,
    then apply sum_image (since swap is injective), then use swap image identity. -/
theorem sum_lower_eq_sum_upper {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (s : Finset ι) (f : ι × ι → R)
    (hf : ∀ i j, f (i, j) = f (j, i)) :
    ∑ p ∈ s.offDiag.filter (fun p => p.2 < p.1), f p =
    ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2), f p := by
  let lower := s.offDiag.filter (fun p => p.2 < p.1)
  -- Step 1: f(a,b) = f(swap(a,b)) by symmetry, so ∑ lower f = ∑ lower (f ∘ swap)
  -- Step 2: By sum_image, ∑ lower (f ∘ swap) = ∑ (lower.image swap) f
  -- Step 3: lower.image swap = upper
  calc ∑ p ∈ lower, f p
      = ∑ p ∈ lower, f (Prod.swap p) :=
        Finset.sum_congr rfl (fun ⟨a, b⟩ _ => hf a b)
    _ = ∑ p ∈ lower.image Prod.swap, f p :=
        (Finset.sum_image (fun ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h => by
          simp only [Prod.swap, Prod.mk.injEq] at h
          exact Prod.ext h.2 h.1)).symm
    _ = ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2), f p := by
        rw [image_swap_lower_eq_upper]

-- ============================================================
-- Part IV: Main Theorem — Off-Diagonal Symmetry
-- ============================================================

/-- **Main Theorem: Off-Diagonal Symmetry**
    For a symmetric function f(i,j) = f(j,i):
    Σ_{i≠j} f(i,j) = 2 · Σ_{i<j} f(i,j)

    This is the key identity connecting the off-diagonal sum to the
    elementary symmetric polynomial e₂ = Σ_{i<j} xᵢxⱼ. -/
theorem sum_offDiag_eq_two_mul_sum_upper {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (s : Finset ι) (f : ι × ι → R)
    (hf : ∀ i j, f (i, j) = f (j, i)) :
    ∑ p ∈ s.offDiag, f p = 2 * ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2), f p := by
  rw [offDiag_eq_upper_union_lower, sum_union (upper_lower_disjoint s),
      sum_lower_eq_sum_upper s f hf, two_mul]

-- ============================================================
-- Part V: Application to Products xᵢ · xⱼ
-- ============================================================

/-- Specialization: Σ_{(i,j) ∈ offDiag} xᵢxⱼ = 2 · Σ_{i<j} xᵢxⱼ. -/
theorem offDiag_prod_eq_two_mul_e2 {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (s : Finset ι) (x : ι → R) :
    ∑ p ∈ s.offDiag, x p.1 * x p.2 =
    2 * ∑ p ∈ s.offDiag.filter (fun p => p.1 < p.2), x p.1 * x p.2 :=
  sum_offDiag_eq_two_mul_sum_upper s (fun p => x p.1 * x p.2) (fun i j => by ring)

-- ============================================================
-- Part VI: Concrete Examples
-- ============================================================

/-- Example: for three elements, off-diagonal products sum to 2× ordered pairs. -/
example (a b c : R) :
    a * b + a * c + b * a + b * c + c * a + c * b = 2 * (a * b + a * c + b * c) := by ring

/-- Example: (a + b)² = a² + b² + 2ab. -/
example (a b : R) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * (a * b) := by ring

end AMGMInequalityOQ02OQ01OQ02
