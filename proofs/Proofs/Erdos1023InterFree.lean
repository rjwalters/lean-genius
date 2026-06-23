/-
Erdős Problem #1023 — Intersection-Free and Difference-Free Set Families
(child open question: "Sunflower-type problems for intersection and difference operations")

The parent problem #1023 concerns *union-free* families: families F of subsets of
{1,…,n} in which no member is the union of ≥ 2 other members. The answer is
F(n) = C(n, ⌊n/2⌋), realized by the middle layer.

This file develops the natural analogues for the two other Boolean operations —
**intersection** and **(symmetric) difference** — and pins down exactly how each
relates to the union-free theory via complementation.

Main results (all 0-axiom, machine-checked):

* **De Morgan duality.**  The complementation bijection  A ↦ Aᶜ  on subsets of
  {1,…,n} carries union-free families bijectively onto **intersection-free**
  families, preserving cardinality (`unionFree_compl`, `interFree_compl`).
  Consequently the intersection-analogue extremal function is *identical* to the
  union one:  `interFreeMax n = unionFreeMax n`  (`interFreeMax_eq_unionFreeMax`).
  This transports the whole solved problem #1023 to its intersection form for free:
  the intersection-free maximum is also C(n, ⌊n/2⌋).

* **Antichains.**  Antichains are intersection-free (`antichain_interFree`), giving
  the constructive lower bound  `interFreeMax n ≥ C(n, ⌊n/2⌋)`  via the middle layer
  (`interFreeMax_ge_middle`) — independent of the duality and of any axiom.

* **Difference operations.**  Symmetric difference is *complement-stable* as an
  operation:  Aᶜ ∆ Bᶜ = A ∆ B  (`symmDiff_compl_compl`), while set difference is
  *complement-reversing*:  Aᶜ \ Bᶜ = B \ A  (`compl_sdiff_compl`).  These identities
  explain why the clean De Morgan transport that works for ∩ does **not** carry the
  union-free extremal result over to symmetric difference: the operation is not
  De Morgan-dual to union but invariant under complementation.

Self-contained: re-declares the needed definitions in its own namespace so the file
depends on no axioms from the (axiomatized) parent entry.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.SymmDiff
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Finset
open scoped symmDiff

namespace Erdos1023InterFree

variable {n : ℕ}

/-! ## Setup: families and the three operations -/

/-- A set family on {0,…,n-1}. -/
abbrev SetFamily (n : ℕ) := Finset (Finset (Fin n))

/-- The union of a subfamily (⊥ = ∅ on the empty family). -/
def familyUnion (F : SetFamily n) : Finset (Fin n) := F.sup id

/-- The intersection of a subfamily (⊤ = univ on the empty family). -/
def familyInter (F : SetFamily n) : Finset (Fin n) := F.inf id

/-- `A` is the union of a subfamily of size ≥ 2 not containing `A`. -/
def isUnionOf (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ 2 ≤ G.card ∧ A ∉ G ∧ familyUnion G = A

/-- `A` is the intersection of a subfamily of size ≥ 2 not containing `A`. -/
def isInterOf (A : Finset (Fin n)) (F : SetFamily n) : Prop :=
  ∃ G : SetFamily n, G ⊆ F ∧ 2 ≤ G.card ∧ A ∉ G ∧ familyInter G = A

/-- A family is union-free: no member is the union of other members. -/
def isUnionFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬ isUnionOf A (F.erase A)

/-- A family is intersection-free: no member is the intersection of other members. -/
def isInterFree (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ¬ isInterOf A (F.erase A)

/-! ## The complementation bijection -/

/-- Complementation `A ↦ Aᶜ` is injective on subsets of `Fin n`. -/
theorem compl_inj : Function.Injective (compl : Finset (Fin n) → Finset (Fin n)) := by
  intro a b h
  have := congrArg compl h
  simpa using this

/-- Complementing every member preserves cardinality. -/
theorem card_image_compl (F : SetFamily n) :
    (F.image (·ᶜ)).card = F.card :=
  Finset.card_image_of_injective _ compl_inj

/-- Complementing twice recovers the family. -/
theorem image_compl_compl (F : SetFamily n) :
    (F.image (·ᶜ)).image (·ᶜ) = F := by
  rw [Finset.image_image]
  simp

/-- Erasing commutes with member-wise complementation. -/
theorem erase_image_compl (F : SetFamily n) (A : Finset (Fin n)) :
    (F.image (·ᶜ)).erase Aᶜ = (F.erase A).image (·ᶜ) := by
  ext B
  simp only [Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hBne, C, hC, rfl⟩
    exact ⟨C, ⟨fun h => hBne (by rw [h]), hC⟩, rfl⟩
  · rintro ⟨C, ⟨hCne, hC⟩, rfl⟩
    exact ⟨fun h => hCne (compl_inj h), C, hC, rfl⟩

/-! ## De Morgan's laws at the level of subfamilies -/

/-- The complement of a union of a subfamily is the intersection of the complements. -/
theorem compl_familyUnion (G : SetFamily n) :
    (familyUnion G)ᶜ = familyInter (G.image (·ᶜ)) := by
  classical
  simp only [familyUnion, familyInter]
  induction G using Finset.induction with
  | empty => simp
  | insert A G hA ih =>
    rw [Finset.sup_insert, compl_sup, Finset.image_insert, Finset.inf_insert, ih]
    simp

/-- The complement of an intersection of a subfamily is the union of the complements. -/
theorem compl_familyInter (G : SetFamily n) :
    (familyInter G)ᶜ = familyUnion (G.image (·ᶜ)) := by
  classical
  simp only [familyUnion, familyInter]
  induction G using Finset.induction with
  | empty => simp
  | insert A G hA ih =>
    rw [Finset.inf_insert, compl_inf, Finset.image_insert, Finset.sup_insert, ih]
    simp

/-! ## Operation transport under complementation -/

/-- A union witness becomes an intersection witness for the complemented family. -/
theorem isUnionOf_to_isInterOf {A : Finset (Fin n)} {F : SetFamily n}
    (h : isUnionOf A F) : isInterOf Aᶜ (F.image (·ᶜ)) := by
  obtain ⟨G, hGF, hcard, hAG, hU⟩ := h
  refine ⟨G.image (·ᶜ), Finset.image_subset_image hGF, ?_, ?_, ?_⟩
  · rwa [card_image_compl]
  · intro h
    obtain ⟨B, hB, hBeq⟩ := Finset.mem_image.mp h
    exact hAG (by rwa [compl_inj hBeq] at hB)
  · rw [← hU, compl_familyUnion]

/-- An intersection witness becomes a union witness for the complemented family. -/
theorem isInterOf_to_isUnionOf {A : Finset (Fin n)} {F : SetFamily n}
    (h : isInterOf A F) : isUnionOf Aᶜ (F.image (·ᶜ)) := by
  obtain ⟨G, hGF, hcard, hAG, hI⟩ := h
  refine ⟨G.image (·ᶜ), Finset.image_subset_image hGF, ?_, ?_, ?_⟩
  · rwa [card_image_compl]
  · intro h
    obtain ⟨B, hB, hBeq⟩ := Finset.mem_image.mp h
    exact hAG (by rwa [compl_inj hBeq] at hB)
  · rw [← hI, compl_familyInter]

/-- Complementation sends union-free families to intersection-free families. -/
theorem unionFree_compl {F : SetFamily n} (hF : isUnionFree F) :
    isInterFree (F.image (·ᶜ)) := by
  intro B hB hInter
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
  rw [erase_image_compl] at hInter
  have hU : isUnionOf Aᶜᶜ ((F.erase A).image (·ᶜ) |>.image (·ᶜ)) :=
    isInterOf_to_isUnionOf hInter
  rw [compl_compl, image_compl_compl] at hU
  exact hF A hA hU

/-- Complementation sends intersection-free families to union-free families. -/
theorem interFree_compl {F : SetFamily n} (hF : isInterFree F) :
    isUnionFree (F.image (·ᶜ)) := by
  intro B hB hUnion
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hB
  rw [erase_image_compl] at hUnion
  have hI : isInterOf Aᶜᶜ ((F.erase A).image (·ᶜ) |>.image (·ᶜ)) :=
    isUnionOf_to_isInterOf hUnion
  rw [compl_compl, image_compl_compl] at hI
  exact hF A hA hI

/-! ## Antichains are intersection-free -/

/-- A family is an antichain if no set contains another. -/
def isAntichain (F : SetFamily n) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, A ⊆ B → A = B

/-- Each member of a subfamily contains its intersection. -/
theorem familyInter_subset {G : SetFamily n} {B : Finset (Fin n)} (hB : B ∈ G) :
    familyInter G ⊆ B := by
  have : G.inf id ≤ id B := Finset.inf_le hB
  simpa [familyInter] using this

/-- Antichains are intersection-free (dual to `antichain_unionFree`). -/
theorem antichain_interFree (F : SetFamily n) : isAntichain F → isInterFree F := by
  intro hanti A hA ⟨G, hGsub, hGcard, hAnotG, hGinter⟩
  -- every member of `G` contains `A = ⋂ G`, and lies in `F` distinct from `A`
  have hAsubB : ∀ B ∈ G, A ⊆ B := by
    intro B hB
    rw [← hGinter]
    exact familyInter_subset hB
  have hAeqB : ∀ B ∈ G, A = B := by
    intro B hB
    have hBF : B ∈ F := Finset.mem_of_mem_erase (hGsub hB)
    exact hanti A hA B hBF (hAsubB B hB)
  -- but then every member of `G` equals `A`, forcing `card G ≤ 1`
  have : G.card ≤ 1 := by
    by_contra h
    push_neg at h
    obtain ⟨B, hB, C, hC, hBC⟩ := Finset.one_lt_card.mp h
    exact hBC (by rw [← hAeqB B hB, ← hAeqB C hC])
  omega

/-! ## The extremal functions and their equality -/

/-- The achievable sizes of union-free families are bounded by 2ⁿ. -/
theorem unionFree_sizes_bddAbove (n : ℕ) :
    BddAbove { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k } :=
  ⟨2 ^ n, fun k ⟨F, _, hk⟩ => hk ▸ (Finset.card_le_univ F).trans (by simp)⟩

/-- The achievable sizes of intersection-free families are bounded by 2ⁿ. -/
theorem interFree_sizes_bddAbove (n : ℕ) :
    BddAbove { k : ℕ | ∃ F : SetFamily n, isInterFree F ∧ F.card = k } :=
  ⟨2 ^ n, fun k ⟨F, _, hk⟩ => hk ▸ (Finset.card_le_univ F).trans (by simp)⟩

/-- F(n): maximum size of a union-free family. -/
noncomputable def unionFreeMax (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k }

/-- F∩(n): maximum size of an intersection-free family. -/
noncomputable def interFreeMax (n : ℕ) : ℕ :=
  sSup { k : ℕ | ∃ F : SetFamily n, isInterFree F ∧ F.card = k }

/-- The achievable-size sets coincide: intersection-free and union-free families
    realize exactly the same cardinalities (via the complement bijection). -/
theorem interFree_sizes_eq_unionFree_sizes (n : ℕ) :
    { k : ℕ | ∃ F : SetFamily n, isInterFree F ∧ F.card = k }
      = { k : ℕ | ∃ F : SetFamily n, isUnionFree F ∧ F.card = k } := by
  ext k
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F.image (·ᶜ), interFree_compl hF, card_image_compl F⟩
  · rintro ⟨F, hF, rfl⟩
    exact ⟨F.image (·ᶜ), unionFree_compl hF, card_image_compl F⟩

/-- **De Morgan duality of the extremal functions.**
    The intersection-free maximum equals the union-free maximum. Combined with the
    solved parent problem (F(n) = C(n, ⌊n/2⌋)) this gives the intersection analogue
    for free. -/
theorem interFreeMax_eq_unionFreeMax (n : ℕ) : interFreeMax n = unionFreeMax n := by
  unfold interFreeMax unionFreeMax
  rw [interFree_sizes_eq_unionFree_sizes]

/-! ## Lower bound via the middle layer -/

/-- The k-th layer: subsets of size exactly k. -/
def layer (n k : ℕ) : SetFamily n :=
  (univ.powerset).filter (fun A => A.card = k)

/-- The middle layer: subsets of size ⌊n/2⌋. -/
def middleLayer (n : ℕ) : SetFamily n :=
  layer n (n / 2)

/-- Size of a layer equals the binomial coefficient. -/
theorem layer_card (n k : ℕ) : (layer n k).card = Nat.choose n k := by
  rw [layer, ← powersetCard_eq_filter, card_powersetCard, card_univ, Fintype.card_fin]

/-- Size of the middle layer is C(n, ⌊n/2⌋). -/
theorem middleLayer_card (n : ℕ) : (middleLayer n).card = Nat.choose n (n / 2) :=
  layer_card n (n / 2)

/-- The middle layer is an antichain. -/
theorem middleLayer_antichain (n : ℕ) : isAntichain (middleLayer n) := by
  intro A hA B hB hAB
  simp only [middleLayer, layer, mem_filter] at hA hB
  exact Finset.eq_of_subset_of_card_le hAB (hA.2 ▸ hB.2 ▸ le_refl _)

/-- The middle layer is intersection-free. -/
theorem middleLayer_interFree (n : ℕ) : isInterFree (middleLayer n) :=
  antichain_interFree _ (middleLayer_antichain n)

/-- **Lower bound.** F∩(n) ≥ C(n, ⌊n/2⌋), realized constructively by the middle
    layer — independent of the duality and axiom-free. -/
theorem interFreeMax_ge_middle (n : ℕ) :
    Nat.choose n (n / 2) ≤ interFreeMax n := by
  rw [interFreeMax]
  apply le_csSup (interFree_sizes_bddAbove n)
  exact ⟨middleLayer n, middleLayer_interFree n, middleLayer_card n⟩

/-! ## Difference operations: why the duality stops at intersection

Union and intersection are De Morgan-dual: complementation swaps them, which is
exactly what transports the extremal result. The two difference operations behave
differently under complementation, so no analogous transport is available. -/

/-- Symmetric difference is **complement-stable**: complementing both arguments
    leaves it unchanged. -/
theorem symmDiff_compl_compl (A B : Finset (Fin n)) : Aᶜ ∆ Bᶜ = A ∆ B := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_compl]
  tauto

/-- Complementing one argument of a symmetric difference complements the result. -/
theorem symmDiff_compl_left (A B : Finset (Fin n)) : Aᶜ ∆ B = (A ∆ B)ᶜ := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_compl]
  tauto

/-- A set and its complement are symmetric-difference complementary. -/
theorem symmDiff_self_compl (A : Finset (Fin n)) : A ∆ Aᶜ = univ := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_compl, Finset.mem_univ, iff_true]
  tauto

/-- Set difference is **complement-reversing**: complementing both arguments
    transposes the operands. -/
theorem compl_sdiff_compl (A B : Finset (Fin n)) : Aᶜ \ Bᶜ = B \ A := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_compl]
  tauto

end Erdos1023InterFree
