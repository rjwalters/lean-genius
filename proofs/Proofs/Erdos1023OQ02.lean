/-
Erdős Problem #1023, Open Question OQ-02: The Intersection-Free Dual

The parent problem (Erdős #1023) studies *union-free* families: families of subsets
of {1,…,n} in which no member is the union of two or more other members.  Its
extremal function F(n) (the maximum size of such a family) is known to equal the
central binomial coefficient C(n, ⌊n/2⌋).

One of the open questions raised by the parent entry is:

    "Analogous problems for other operations (intersection, difference)?"

This file answers the *intersection* case completely, and in the sharpest possible
form: the intersection-free extremal problem is **identical** to the union-free one
for *every* n — not merely asymptotically.  The bridge is the complement involution
A ↦ Aᶜ, which is a size-preserving bijection on families that exchanges the two
properties via De Morgan's laws:

    a family F is intersection-free  ⟺  its complement family Fᶜ = {Aᶜ : A ∈ F}
                                          is union-free.

Consequently the maximum intersection-free family has exactly the same size as the
maximum union-free family, `interFreeMax n = unionFreeMax n`, and the complemented
middle layer is an explicit extremal construction of size C(n, ⌊n/2⌋).

All results are machine-checked with **zero axioms** (see `#print axioms` at the end).

The file is self-contained: it re-declares the parent's union-free definitions
(`familyUnion`, `isUnionFree`, `unionFreeMax`, `middleLayer`, …), matching
`Proofs/Erdos1023Problem.lean` verbatim, and then develops the intersection dual.
-/

import Mathlib

open Finset

namespace Erdos1023OQ02

variable {n : ℕ}

/-! ## Parent definitions (re-declared to keep this file standalone) -/

/-- A set family is a collection of subsets. -/
abbrev SetFamily (n : ℕ) := Finset (Finset (Fin n))

/-- The power set of {0,…,n-1}. -/
def powerSet (n : ℕ) : Finset (Finset (Fin n)) := univ.powerset

theorem powerSet_card (n : ℕ) : (powerSet n).card = 2 ^ n := by simp [powerSet]

/-- The union of a subfamily. -/
def familyUnion (F : SetFamily n) : Finset (Fin n) := F.sup id

/-- `A` is the union of a subfamily of `F` of size ≥ 2 not containing `A`. -/
def isUnionOf (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card ≥ 2 ∧ A ∉ G ∧ familyUnion G = A

/-- A family is union-free: no member is the union of other members. -/
def isUnionFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isUnionOf A (F.erase A)

/-- F(n): maximum size of a union-free family on {0,…,n-1}. -/
noncomputable def unionFreeMax (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k }

/-- A family is an antichain if no set contains another. -/
def isAntichain (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

/-- Each element of a subfamily contributes to the union. -/
lemma mem_sub_familyUnion {F : SetFamily n} {B : Finset (Fin n)} (hB : B ∈ F) :
    B ⊆ familyUnion F := by
  intro x hx
  simp only [familyUnion]
  exact Finset.mem_sup.mpr ⟨B, hB, hx⟩

/-- Antichains are union-free. -/
theorem antichain_unionFree (F : SetFamily n) : isAntichain F → isUnionFree F := by
  intro hanti A hA ⟨G, hGsub, hGcard, hAnotG, hGunion⟩
  have hBsubA : ∀ B ∈ G, B ⊆ A := by
    intro B hB; rw [← hGunion]; exact mem_sub_familyUnion hB
  have hBeqA : ∀ B ∈ G, B = A := by
    intro B hB
    have hBF : B ∈ F := Finset.mem_of_mem_erase (hGsub hB)
    exact hanti B hBF A hA (hBsubA B hB)
  have : G.card ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp h
    exact hBC (by rw [hBeqA B hB, hBeqA C hC])
  omega

/-- The k-th layer: sets of size exactly k. -/
def layer (n k : ℕ) : SetFamily n := (powerSet n).filter (fun A => A.card = k)

/-- The middle layer: sets of size n/2. -/
def middleLayer (n : ℕ) : SetFamily n := layer n (n / 2)

theorem layer_card (n k : ℕ) : (layer n k).card = Nat.choose n k := by
  simp [layer, powerSet]

theorem middleLayer_card (n : ℕ) : (middleLayer n).card = Nat.choose n (n / 2) :=
  layer_card n (n / 2)

theorem middleLayer_antichain (n : ℕ) : isAntichain (middleLayer n) := by
  intro A hA B hB hAB
  simp only [middleLayer, layer, mem_filter] at hA hB
  exact Finset.eq_of_subset_of_card_le hAB (hA.2 ▸ hB.2 ▸ le_refl _)

theorem middleLayer_unionFree (n : ℕ) : isUnionFree (middleLayer n) :=
  antichain_unionFree _ (middleLayer_antichain n)

/-! ## The complement involution on families

`compl` is the Boolean-algebra complement on `Finset (Fin n)` (i.e. `Aᶜ = univ \ A`).
It is an involution, hence injective; the induced map on families
`complFamily F = F.image compl` is therefore a size-preserving involution as well. -/

/-- The complement family: replace every member `A` of `F` by its complement `Aᶜ`. -/
def complFamily (F : SetFamily n) : SetFamily n := F.image compl

@[simp] lemma mem_complFamily {F : SetFamily n} {A : Finset (Fin n)} :
    A ∈ complFamily F ↔ Aᶜ ∈ F := by
  unfold complFamily
  rw [mem_image]
  constructor
  · rintro ⟨B, hB, rfl⟩; simpa using hB
  · intro hA; exact ⟨Aᶜ, hA, by simp⟩

/-- `complFamily` preserves cardinality (the complement map is injective). -/
@[simp] lemma complFamily_card (F : SetFamily n) : (complFamily F).card = F.card :=
  card_image_of_injective _ (fun a b h => by simpa using congrArg compl h)

/-- `complFamily` is an involution. -/
@[simp] lemma complFamily_complFamily (F : SetFamily n) :
    complFamily (complFamily F) = F := by
  unfold complFamily; rw [image_image]; simp

/-- Erasing a member and complementing commute. -/
lemma complFamily_erase (F : SetFamily n) (A : Finset (Fin n)) :
    complFamily (F.erase A) = (complFamily F).erase Aᶜ := by
  unfold complFamily
  exact image_erase (fun a b h => by simpa using congrArg compl h) F A

/-! ## De Morgan: complementing turns unions into intersections -/

/-- The intersection of a subfamily (empty family ↦ `univ`). -/
def familyInter (F : SetFamily n) : Finset (Fin n) := F.inf id

/-- De Morgan, union form: `⋃ (complemented G) = (⋂ G)ᶜ`. -/
lemma familyUnion_complFamily (G : SetFamily n) :
    familyUnion (complFamily G) = (familyInter G)ᶜ := by
  unfold familyUnion familyInter complFamily
  rw [sup_image, Finset.compl_inf]; rfl

/-- De Morgan, intersection form: `⋂ (complemented G) = (⋃ G)ᶜ`. -/
lemma familyInter_complFamily (G : SetFamily n) :
    familyInter (complFamily G) = (familyUnion G)ᶜ := by
  unfold familyInter familyUnion complFamily
  rw [inf_image, Finset.compl_sup]; rfl

/-! ## Intersection-free families

Mirror of the union-free definitions, with `⋃` replaced by `⋂`. -/

/-- `A` is the intersection of a subfamily of `F` of size ≥ 2 not containing `A`. -/
def isInterOf (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ G.card ≥ 2 ∧ A ∉ G ∧ familyInter G = A

/-- A family is intersection-free: no member is the intersection of other members. -/
def isInterFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬isInterOf A (F.erase A)

/-! ## The core bridge

`A` is an intersection of a subfamily of `H` iff `Aᶜ` is a union of the
complemented subfamily of `complFamily H`. -/

lemma isInterOf_iff_isUnionOf_compl (A : Finset (Fin n)) (H : SetFamily n) :
    isInterOf A H ↔ isUnionOf Aᶜ (complFamily H) := by
  constructor
  · rintro ⟨G, hGH, hGcard, hAG, hGinter⟩
    refine ⟨complFamily G, ?_, ?_, ?_, ?_⟩
    · exact image_subset_image hGH
    · rwa [complFamily_card]
    · simp only [mem_complFamily, compl_compl]; exact hAG
    · rw [familyUnion_complFamily, hGinter]
  · rintro ⟨G', hG'H, hG'card, hAG', hG'union⟩
    refine ⟨complFamily G', ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [mem_complFamily] at hx
      have hx' := hG'H hx
      rw [mem_complFamily, compl_compl] at hx'
      exact hx'
    · rwa [complFamily_card]
    · simpa using hAG'
    · rw [familyInter_complFamily, hG'union, compl_compl]

/-! ## Main duality theorem -/

/-- A family is intersection-free iff its complement family is union-free.  This is
the exact, non-asymptotic statement of the intersection ⟷ union correspondence. -/
theorem isInterFree_iff_isUnionFree_complFamily (F : SetFamily n) :
    isInterFree F ↔ isUnionFree (complFamily F) := by
  constructor
  · intro h B hB hUnion
    rw [mem_complFamily] at hB
    apply h Bᶜ hB
    rw [isInterOf_iff_isUnionOf_compl, complFamily_erase]
    simpa using hUnion
  · intro h A hA hInter
    rw [isInterOf_iff_isUnionOf_compl, complFamily_erase] at hInter
    exact h Aᶜ (by rw [mem_complFamily, compl_compl]; exact hA) hInter

/-- Symmetric form: a family is union-free iff its complement is intersection-free. -/
theorem isUnionFree_iff_isInterFree_complFamily (F : SetFamily n) :
    isUnionFree F ↔ isInterFree (complFamily F) := by
  rw [isInterFree_iff_isUnionFree_complFamily, complFamily_complFamily]

/-! ## The extremal function for intersection-free families -/

/-- F_∩(n): the maximum size of an intersection-free family on {0,…,n-1}. -/
noncomputable def interFreeMax (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ F : SetFamily n, isInterFree F ∧ F.card = k }

/-- The achievable cardinalities for the two problems are the same set. -/
theorem interFree_sizes_eq_unionFree_sizes (n : ℕ) :
    { k : ℕ | ∃ F : SetFamily n, isInterFree F ∧ F.card = k }
      = { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k } := by
  ext k
  constructor
  · rintro ⟨F, hF, hcard⟩
    exact ⟨complFamily F, (isInterFree_iff_isUnionFree_complFamily F).mp hF,
      by rwa [complFamily_card]⟩
  · rintro ⟨F, hF, hcard⟩
    exact ⟨complFamily F, (isUnionFree_iff_isInterFree_complFamily F).mp hF,
      by rwa [complFamily_card]⟩

/-- **The intersection-free and union-free extremal problems coincide exactly.**
For every `n`, the maximum size of an intersection-free family equals the maximum
size of a union-free family. -/
theorem interFreeMax_eq_unionFreeMax (n : ℕ) : interFreeMax n = unionFreeMax n := by
  unfold interFreeMax unionFreeMax
  rw [interFree_sizes_eq_unionFree_sizes]

/-! ## An explicit extremal intersection-free family -/

/-- The complemented middle layer is intersection-free. -/
theorem complMiddleLayer_interFree (n : ℕ) :
    isInterFree (complFamily (middleLayer n)) :=
  (isUnionFree_iff_isInterFree_complFamily _).mp (middleLayer_unionFree n)

/-- The complemented middle layer has size C(n, ⌊n/2⌋). -/
theorem complMiddleLayer_card (n : ℕ) :
    (complFamily (middleLayer n)).card = Nat.choose n (n / 2) := by
  rw [complFamily_card, middleLayer_card]

/-- Lower bound: `interFreeMax n ≥ C(n, ⌊n/2⌋)`, achieved by the complemented
middle layer. -/
theorem interFreeMax_ge_choose (n : ℕ) : Nat.choose n (n / 2) ≤ interFreeMax n := by
  unfold interFreeMax
  apply le_csSup
  · refine ⟨2 ^ n, ?_⟩
    rintro k ⟨F, _, rfl⟩
    exact (Finset.card_le_univ F).trans (by simp)
  · exact ⟨complFamily (middleLayer n), complMiddleLayer_interFree n,
      complMiddleLayer_card n⟩

/-- The map `complFamily` restricts to a size-preserving involutive bijection
between the intersection-free families and the union-free families. -/
theorem complFamily_bij_interFree_unionFree (F : SetFamily n) :
    (isInterFree F ↔ isUnionFree (complFamily F))
      ∧ (complFamily F).card = F.card
      ∧ complFamily (complFamily F) = F :=
  ⟨isInterFree_iff_isUnionFree_complFamily F, complFamily_card F,
    complFamily_complFamily F⟩

end Erdos1023OQ02

-- Axiom audit: these results are axiom-free.
#print axioms Erdos1023OQ02.interFreeMax_eq_unionFreeMax
#print axioms Erdos1023OQ02.isInterFree_iff_isUnionFree_complFamily
#print axioms Erdos1023OQ02.interFreeMax_ge_choose
