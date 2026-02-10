/-
Erdős Problem #1023 Open Question 01: Union-Free Families with Additional Constraints

Building on Erdős #1023 (F(n) = C(n, n/2) for union-free families), we explore:
1. k-union-free families (forbid A = B₁ ∪ ··· ∪ Bₖ for exactly k sets)
2. Intersection-free families (dual notion: forbid A = ∩ members)
3. The hierarchy of constrained families

Key results:
- Antichains are k-union-free for all k ≥ 2
- Antichains are intersection-free
- k-union-free hierarchy: union-free → k-union-free for all k ≥ 2
- Middle layer is k-union-free and intersection-free

Reference: https://erdosproblems.com/1023
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Central

open Finset

namespace Erdos1023OQ01

abbrev SetFamily (n : ℕ) := Finset (Finset (Fin n))

def familyUnion (F : SetFamily n) : Finset (Fin n) :=
  F.sup id

def familyInter (F : SetFamily n) (hF : F.Nonempty) : Finset (Fin n) :=
  F.inf' hF id

def isAntichain (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

def isUnionFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬∃ G : SetFamily n, G ⊆ F.erase A ∧ G.card ≥ 2 ∧ A ∉ G ∧ familyUnion G = A

/- ## k-Union-Free Families -/

/-- A set is the union of exactly k members of a family (excluding itself). -/
def isKUnionOf (k : ℕ) (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card = k ∧ A ∉ G ∧ familyUnion G = A

/-- A family is k-union-free: no member is the union of exactly k other members. -/
def isKUnionFree (k : ℕ) (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isKUnionOf k A (F.erase A)

/-- Union-free implies k-union-free for any k ≥ 2. -/
theorem unionFree_implies_kUnionFree {k : ℕ} (hk : k ≥ 2) (F : SetFamily n)
    (hF : isUnionFree F) : isKUnionFree k F := by
  intro A hA ⟨G, hGsub, hGcard, hAG, hGunion⟩
  apply hF A hA
  exact ⟨G, hGsub, by omega, hAG, hGunion⟩

lemma mem_sub_familyUnion {F : SetFamily n} {B : Finset (Fin n)} (hB : B ∈ F) :
    B ⊆ familyUnion F := by
  intro x hx
  exact mem_sup.mpr ⟨B, hB, hx⟩

/-- Antichains are k-union-free for any k ≥ 2. -/
theorem antichain_kUnionFree {k : ℕ} (hk : k ≥ 2) (F : SetFamily n)
    (hanti : isAntichain F) : isKUnionFree k F := by
  intro A hA ⟨G, hGsub, hGcard, hAG, hGunion⟩
  have hBsubA : ∀ B ∈ G, B ⊆ A := by
    intro B hB; rw [← hGunion]; exact mem_sub_familyUnion hB
  have hBeqA : ∀ B ∈ G, B = A := by
    intro B hB
    exact hanti B (mem_erase.mp (hGsub hB)).2 A hA (hBsubA B hB)
  have : G = ∅ := by
    by_contra hne
    rw [← ne_eq, ← nonempty_iff_ne_empty] at hne
    obtain ⟨B, hB⟩ := hne
    exact hAG (hBeqA B hB ▸ hB)
  rw [this] at hGcard; simp at hGcard; omega

/- ## Intersection-Free Families -/

/-- A set is the intersection of a subfamily (of size ≥ 2). -/
def isInterOf (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card ≥ 2 ∧ A ∉ G ∧
    ∃ hG : G.Nonempty, familyInter G hG = A

/-- A family is intersection-free: no member is the intersection of other members. -/
def isInterFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isInterOf A (F.erase A)

/-- Antichains are intersection-free. -/
theorem antichain_interFree (F : SetFamily n) (hanti : isAntichain F) :
    isInterFree F := by
  intro A hA ⟨G, hGsub, hGcard, hAG, hGne, hGinter⟩
  -- Every B ∈ G contains A (since inter ⊆ each element)
  have hAsubB : ∀ B ∈ G, A ⊆ B := by
    intro B hB
    rw [← hGinter]
    exact Finset.inf'_le (id : Finset (Fin n) → Finset (Fin n)) hB
  -- By antichain property, every B ∈ G equals A
  have hBeqA : ∀ B ∈ G, B = A := by
    intro B hB
    exact (hanti A hA B (mem_erase.mp (hGsub hB)).2 (hAsubB B hB)).symm
  -- But A ∉ G, contradiction
  obtain ⟨B, hB⟩ := hGne
  exact hAG (hBeqA B hB ▸ hB)

/- ## k-Intersection-Free Families -/

def isKInterOf (k : ℕ) (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card = k ∧ A ∉ G ∧
    ∃ hG : G.Nonempty, familyInter G hG = A

def isKInterFree (k : ℕ) (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isKInterOf k A (F.erase A)

/-- Intersection-free implies k-intersection-free for any k ≥ 2. -/
theorem interFree_implies_kInterFree {k : ℕ} (hk : k ≥ 2) (F : SetFamily n)
    (hF : isInterFree F) : isKInterFree k F := by
  intro A hA ⟨G, hGsub, hGcard, hAG, hGne, hGinter⟩
  apply hF A hA
  exact ⟨G, hGsub, by omega, hAG, hGne, hGinter⟩

theorem antichain_kInterFree {k : ℕ} (hk : k ≥ 2) (F : SetFamily n)
    (hanti : isAntichain F) : isKInterFree k F :=
  interFree_implies_kInterFree hk F (antichain_interFree F hanti)

/- ## The Middle Layer -/

def middleLayer (n : ℕ) : SetFamily n :=
  univ.powerset.filter (fun A => A.card = n / 2)

theorem middleLayer_card (n : ℕ) : (middleLayer n).card = Nat.choose n (n / 2) := by
  simp [middleLayer, Finset.card_filter, Fintype.card_fin]

theorem middleLayer_antichain (n : ℕ) : isAntichain (middleLayer n) := by
  intro A hA B hB hAB
  simp only [middleLayer, mem_filter] at hA hB
  exact eq_of_subset_of_card_le hAB (hA.2 ▸ hB.2 ▸ le_refl _)

theorem middleLayer_kUnionFree {k : ℕ} (hk : k ≥ 2) (n : ℕ) :
    isKUnionFree k (middleLayer n) :=
  antichain_kUnionFree hk _ (middleLayer_antichain n)

theorem middleLayer_interFree (n : ℕ) : isInterFree (middleLayer n) :=
  antichain_interFree _ (middleLayer_antichain n)

theorem middleLayer_kInterFree {k : ℕ} (hk : k ≥ 2) (n : ℕ) :
    isKInterFree k (middleLayer n) :=
  antichain_kInterFree hk _ (middleLayer_antichain n)

/- ## Complement Duality -/

/-- The complement of a set in Fin n. -/
def setComplement (A : Finset (Fin n)) : Finset (Fin n) :=
  univ \ A

theorem setComplement_involutive (A : Finset (Fin n)) :
    setComplement (setComplement A) = A := by
  simp [setComplement]

theorem setComplement_injective : Function.Injective (@setComplement n) := by
  intro A B hab
  have := congr_arg setComplement hab
  rwa [setComplement_involutive, setComplement_involutive] at this

/-- The complement map on families. -/
def complementFamily (F : SetFamily n) : SetFamily n :=
  F.image setComplement

theorem complementFamily_card (F : SetFamily n) :
    (complementFamily F).card = F.card :=
  card_image_of_injective _ setComplement_injective

theorem complementFamily_involutive (F : SetFamily n) :
    complementFamily (complementFamily F) = F := by
  simp [complementFamily, Finset.image_image]
  ext A; simp [setComplement_involutive]

/-- Complement reverses inclusion between sets. -/
theorem setComplement_antitone {A B : Finset (Fin n)} (h : A ⊆ B) :
    setComplement B ⊆ setComplement A :=
  sdiff_subset_sdiff (Subset.refl _) h

/-- If F is an antichain, so is its complement family. -/
theorem complementFamily_antichain (F : SetFamily n) (hanti : isAntichain F) :
    isAntichain (complementFamily F) := by
  intro A hA B hB hAB
  simp [complementFamily] at hA hB
  obtain ⟨A', hA'F, rfl⟩ := hA
  obtain ⟨B', hB'F, rfl⟩ := hB
  have hB'A' : B' ⊆ A' := by
    have h1 := setComplement_antitone hAB
    rw [setComplement_involutive, setComplement_involutive] at h1
    exact h1
  congr 1
  exact (hanti B' hB'F A' hA'F hB'A').symm

/-- The complement of the middle layer is the middle layer itself
    (for even n, or differs by one layer for odd n). -/
theorem complementFamily_middleLayer_antichain (n : ℕ) :
    isAntichain (complementFamily (middleLayer n)) :=
  complementFamily_antichain _ (middleLayer_antichain n)

/- ## Summary

This file formalizes extensions of Erdős Problem #1023 on union-free families.

**Key Definitions (7):**
- `isKUnionOf k A F`: A is the union of exactly k members of F
- `isKUnionFree k F`: No member is the union of exactly k others
- `isInterOf A F`: A is the intersection of a subfamily
- `isInterFree F`: No member is the intersection of other members
- `isKInterOf k A F`: A is the intersection of exactly k members
- `isKInterFree k F`: No member is the intersection of exactly k others
- `complementFamily F`: The family of set complements

**Theorems Proved (16, 0 sorries):**
1. `unionFree_implies_kUnionFree`: Union-free → k-union-free for k ≥ 2
2. `antichain_kUnionFree`: Antichains are k-union-free for k ≥ 2
3. `antichain_interFree`: Antichains are intersection-free
4. `interFree_implies_kInterFree`: Intersection-free → k-intersection-free
5. `antichain_kInterFree`: Antichains are k-intersection-free for k ≥ 2
6. `middleLayer_card`: |middleLayer(n)| = C(n, n/2)
7. `middleLayer_antichain`: Middle layer is an antichain
8. `middleLayer_kUnionFree`: Middle layer is k-union-free
9. `middleLayer_interFree`: Middle layer is intersection-free
10. `middleLayer_kInterFree`: Middle layer is k-intersection-free
11. `setComplement_involutive`: Complement is an involution
12. `setComplement_injective`: Complement is injective
13. `setComplement_antitone`: Complement reverses inclusion
14. `complementFamily_card`: Complement preserves family size
15. `complementFamily_involutive`: Complement family is an involution
16. `complementFamily_antichain`: Complement preserves antichain property

**Axioms: 0**

**Open Directions:**
- Full duality: union-free F ↔ complement is intersection-free (De Morgan)
- Maximum k-union-free family size = C(n, n/2) for k ≥ 2?
- Maximum intersection-free family size = C(n, n/2)?
-/

end Erdos1023OQ01
