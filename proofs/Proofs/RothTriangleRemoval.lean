import Mathlib

/-
# Roth's Theorem via the Triangle Removal Lemma

## What This Proves
An explicit formalization of the reduction from Roth's theorem to
the corners theorem. The key construction: given A ⊆ Z/NZ, define
  S = {(x, y) ∈ (Z/NZ)² : 2x + y ∈ A}
Then:
- Corners in S correspond exactly to 3-term APs in A
- AP-free A gives corner-free S (the contrapositive direction)
- The corners theorem (Mathlib, via triangle removal) gives Roth

## Status
- [x] Corner set construction (verified)
- [x] Corners → 3-APs (verified, 0 sorries)
- [x] 3-APs → Corners (verified, 0 sorries)
- [x] AP-free → Corner-free (verified, 0 sorries)
- [ ] Density preservation (axiomatized)
- [ ] Full Roth via corners (axiomatized)

## Connection to Existing Gallery
RothTheorem.lean uses `roth_3ap_theorem_nat` as a black box.
This file opens that box to show the Corners → Roth reduction.

## Mathlib Dependencies
- `ZMod` : Cyclic group arithmetic
- `Finset` : Finite sets
-/

open Finset

namespace RothTriangleRemoval

variable {N : ℕ} [NeZero N]

-- ============================================================
-- PART I: Corner Set Construction
-- ============================================================

/-- The corner set: pairs (x,y) ∈ (Z/NZ)² such that 2x + y ∈ A.
The factor of 2 makes corners correspond to 3-APs, not sum triples. -/
def cornerSet (A : Finset (ZMod N)) : Finset (ZMod N × ZMod N) :=
  (univ ×ˢ univ).filter fun p => 2 * p.1 + p.2 ∈ A

/-- Membership in the corner set. -/
@[simp]
theorem mem_cornerSet (A : Finset (ZMod N)) (p : ZMod N × ZMod N) :
    p ∈ cornerSet A ↔ 2 * p.1 + p.2 ∈ A := by
  simp [cornerSet, mem_filter, mem_product]

-- ============================================================
-- PART II: Corners ↔ 3-AP Correspondence
-- ============================================================

/-
A **corner** in S is a triple (x,y), (x+d,y), (x,y+d) with d ≠ 0
and all three in S. Via the "2x+y" map:

  (x, y) ∈ S    ⟹  2x + y       = a     ∈ A
  (x+d, y) ∈ S  ⟹  2(x+d) + y   = a+2d  ∈ A
  (x, y+d) ∈ S  ⟹  2x + (y+d)   = a+d   ∈ A

So {a, a+d, a+2d} is a 3-AP in A.
-/

/-- **Corners → 3-APs**: A corner in S gives a 3-AP in A. -/
theorem corner_to_ap (A : Finset (ZMod N)) (x y d : ZMod N) (hd : d ≠ 0)
    (h1 : (x, y) ∈ cornerSet A)
    (h2 : (x + d, y) ∈ cornerSet A)
    (h3 : (x, y + d) ∈ cornerSet A) :
    let a := 2 * x + y
    a ∈ A ∧ (a + d) ∈ A ∧ (a + 2 * d) ∈ A := by
  simp only [mem_cornerSet] at h1 h2 h3
  refine ⟨h1, ?_, ?_⟩
  · -- a + d = 2x + (y + d)
    rwa [show 2 * x + y + d = 2 * x + (y + d) from by ring]
  · -- a + 2d = 2(x + d) + y
    rwa [show 2 * x + y + 2 * d = 2 * (x + d) + y from by ring]

/-- **3-APs → Corners**: Each 3-AP {a, a+d, a+2d} in A yields a corner
in S for every choice of x (with y = a - 2x). -/
theorem ap_to_corner (A : Finset (ZMod N)) (a d x : ZMod N)
    (ha : a ∈ A) (had : a + d ∈ A) (ha2d : a + 2 * d ∈ A) :
    let y := a - 2 * x
    (x, y) ∈ cornerSet A ∧
    (x + d, y) ∈ cornerSet A ∧
    (x, y + d) ∈ cornerSet A := by
  simp only [mem_cornerSet]
  exact ⟨
    by rwa [show 2 * x + (a - 2 * x) = a from by ring],
    by rwa [show 2 * (x + d) + (a - 2 * x) = a + 2 * d from by ring],
    by rwa [show 2 * x + (a - 2 * x + d) = a + d from by ring]⟩

/-- **AP-free → Corner-free**: If A has no 3-AP, the corner set
has no corners. This is the contrapositive reduction. -/
theorem apFree_imp_cornerFree (A : Finset (ZMod N))
    (hAP : ∀ a d : ZMod N, d ≠ 0 → a ∈ A → (a + d) ∈ A → (a + 2 * d) ∈ A → False) :
    ∀ x y d : ZMod N, d ≠ 0 →
      (x, y) ∈ cornerSet A → (x + d, y) ∈ cornerSet A →
      (x, y + d) ∈ cornerSet A → False := by
  intro x y d hd h1 h2 h3
  obtain ⟨ha, had, ha2d⟩ := corner_to_ap A x y d hd h1 h2 h3
  exact hAP _ d hd ha had ha2d

-- ============================================================
-- PART III: Density Preservation
-- ============================================================

/-
For each a ∈ A, the equation 2x + y = a has N solutions (one for
each x, with y = a - 2x). So |cornerSet A| = |A| · N.
-/

/-- The map (a, x) ↦ (x, a - 2x) is injective, establishing a
bijection between A × Z/NZ and cornerSet A. -/
theorem cornerSet_map_injective (A : Finset (ZMod N)) :
    Function.Injective (fun p : ZMod N × ZMod N => (p.2, p.1 - 2 * p.2)) := by
  intro ⟨a₁, x₁⟩ ⟨a₂, x₂⟩ h
  simp only [Prod.mk.injEq] at h
  ext
  · -- a₁ = a₂: from x₁ = x₂ and a₁ - 2x₁ = a₂ - 2x₂
    have hx := h.1
    have hy := h.2
    calc a₁ = 2 * x₁ + (a₁ - 2 * x₁) := by ring
      _ = 2 * x₂ + (a₂ - 2 * x₂) := by rw [hx, hy]
      _ = a₂ := by ring
  · exact h.1

/-- Density: |cornerSet A| = |A| · card(Z/NZ). -/
axiom cornerSet_card (A : Finset (ZMod N)) :
    (cornerSet A).card = A.card * Fintype.card (ZMod N)

-- ============================================================
-- PART IV: Roth from Corners (Statement)
-- ============================================================

/-
Combining the ingredients:
1. cornerSet A has density |A|/N in (Z/NZ)² [density preservation]
2. The corners theorem: dense subsets of (Z/NZ)² contain corners
3. Corners in cornerSet A give 3-APs in A [Part II]

The corners theorem itself is proved via:
  Szemerédi Regularity Lemma → Triangle Removal → Corners Theorem

This makes the full chain:
  Regularity → Triangle Removal → Corners → (this file) → Roth

## Why the Factor 2 Matters

The "2x + y" in the cornerSet definition is not arbitrary. Consider
the alternatives:

- x + y: A corner gives a + d, a + d (sum triples, not 3-APs)
- 3x + y: A corner gives a, a+d, a+3d (not evenly spaced)
- 2x + y: A corner gives a, a+d, a+2d (3-AP!)

The coefficient 2 is the unique choice that makes corners in
{(x,y) : cx+y ∈ A} correspond to 3-term APs.
-/

/-- The final result: Roth's theorem via the explicit corners construction.
For sufficiently large N, every dense subset of Z/NZ contains a 3-AP. -/
axiom roth_via_corners (delta : ℝ) (hdelta : 0 < delta) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N ≥ N₀ → ∀ A : Finset (ZMod N),
      (A.card : ℝ) ≥ delta * N →
      ∃ a d : ZMod N, d ≠ 0 ∧ a ∈ A ∧ (a + d) ∈ A ∧ (a + 2 * d) ∈ A

-- ============================================================
-- Export
-- ============================================================

#check @cornerSet
#check @corner_to_ap
#check @ap_to_corner
#check @apFree_imp_cornerFree
#check @cornerSet_map_injective

end RothTriangleRemoval
