import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic

/-!
# Product of All Group Elements in the Non-Abelian Case

## Overview

The parent result (`WilsonsTheoremOQ04OQ02`) computes the product of all
elements of a finite **commutative** group: in that setting `∏ x : G, x` is a
single well-defined element (`Finset.prod` needs commutativity), equal to the
unique nontrivial involution when one exists.

For a general (possibly **non-abelian**) finite group there is no canonical
"product of all elements": the value of an ordered product depends on the
chosen ordering, so `Finset.prod` is not even defined. This file identifies the
precise sense in which the product survives:

> **Main theorem** (`abelianization_prod_enum`): for *any* enumeration `l` of a
> finite group `G` (a `Nodup` list containing every element), the image of the
> ordered product `l.prod` in the abelianization `Gᵃᵇ` is independent of the
> ordering and equals the order-free `Finset` product `∏ x : G, of x`.

So while `l.prod` is order-dependent in `G`, its class modulo the commutator
subgroup is a genuine invariant of the group. The proof is forced to pass to
the abelianization *before* using permutation-invariance, because
`List.Perm.prod_eq` requires a commutative target — `l.prod` itself lives in the
noncommutative `G`.

## Main results

- `enum_perm` / `enum_perm_toList` — any two enumerations of a `Fintype` are
  permutations of each other (and of `univ.toList`).
- `abelianization_prod_enum` — the abelianized ordered product equals
  `∏ x : G, of x`, independent of ordering.
- `abelianization_prod_order_independent` — two enumerations have equal image
  in `Gᵃᵇ`.
- `prod_enum_eq_of_commGroup` — the abelian contrast: when `G` is commutative
  every enumeration's product already equals `∏ x : G, x` in `G` itself.
- `two_elt_prod_ne` / `two_elt_abelianization_eq` — the smallest witness:
  noncommuting `a, b` give `[a,b].prod ≠ [b,a].prod` in `G`, yet equal images
  in `Gᵃᵇ`.
-/

namespace WilsonsTheoremOQ04OQ02OQ01

open Finset List

variable {G : Type*} [Group G]

-- ============================================================================
-- Part 1: Enumerations of a finite group are mutually permutations
-- ============================================================================

omit [Group G] in
/-- An *enumeration* of a finite group is a `Nodup` list containing every
    element. Any two enumerations are permutations of each other: they are
    duplicate-free and have exactly the same members. -/
theorem enum_perm [Fintype G] {l₁ l₂ : List G}
    (h₁n : l₁.Nodup) (h₁ : ∀ x, x ∈ l₁)
    (h₂n : l₂.Nodup) (h₂ : ∀ x, x ∈ l₂) : l₁ ~ l₂ :=
  (perm_ext_iff_of_nodup h₁n h₂n).mpr (fun a => ⟨fun _ => h₂ a, fun _ => h₁ a⟩)

omit [Group G] in
/-- Every enumeration of a finite group is a permutation of the canonical
    enumeration `univ.toList`. -/
theorem enum_perm_toList [Fintype G] {l : List G}
    (hn : l.Nodup) (hmem : ∀ x, x ∈ l) : l ~ (univ : Finset G).toList :=
  enum_perm hn hmem (Finset.nodup_toList _)
    (fun x => Finset.mem_toList.mpr (mem_univ x))

-- ============================================================================
-- Part 2: The ordered product is well-defined modulo commutators
-- ============================================================================

/-- **Main theorem.** For any enumeration `l` of a finite group `G`, the image
    of the ordered product `l.prod` in the abelianization is independent of the
    ordering and equals the order-free `Finset` product `∏ x : G, of x`.

    The proof passes to the abelianization *first* (`map_list_prod`): `l.prod`
    lives in the noncommutative `G`, so `List.Perm.prod_eq` — which needs a
    commutative target — only becomes available after applying the homomorphism
    `Abelianization.of`. -/
theorem abelianization_prod_enum [Fintype G] {l : List G}
    (hn : l.Nodup) (hmem : ∀ x, x ∈ l) :
    Abelianization.of l.prod = ∏ x : G, Abelianization.of x := by
  have hperm : l ~ (univ : Finset G).toList := enum_perm_toList hn hmem
  rw [map_list_prod Abelianization.of l,
      (hperm.map (⇑Abelianization.of)).prod_eq,
      Finset.prod_map_toList univ Abelianization.of]

/-- **Order-independence.** Any two enumerations of `G` have the same image
    under abelianization, even though their ordered products in `G` may
    differ. -/
theorem abelianization_prod_order_independent [Fintype G]
    {l₁ l₂ : List G} (h₁n : l₁.Nodup) (h₁ : ∀ x, x ∈ l₁)
    (h₂n : l₂.Nodup) (h₂ : ∀ x, x ∈ l₂) :
    Abelianization.of l₁.prod = Abelianization.of l₂.prod := by
  rw [abelianization_prod_enum h₁n h₁, abelianization_prod_enum h₂n h₂]

-- ============================================================================
-- Part 3: The abelian contrast — order-independence already holds in G
-- ============================================================================

/-- In an abelian group the ordered product is *already* order-independent in
    `G` itself: every enumeration's product equals `∏ x : G, x`. Contrast with
    the general case, where only the abelianization image is well-defined. -/
theorem prod_enum_eq_of_commGroup {G : Type*} [CommGroup G] [Fintype G]
    {l : List G} (hn : l.Nodup) (hmem : ∀ x, x ∈ l) :
    l.prod = ∏ x : G, x := by
  rw [(enum_perm_toList hn hmem).prod_eq, Finset.prod_toList]

-- ============================================================================
-- Part 4: The smallest witness — noncommuting pair
-- ============================================================================

/-- The ordered product genuinely depends on order in a non-abelian group: if
    `a` and `b` do not commute, the two orderings `[a, b]` and `[b, a]` of the
    same pair have different products. This is why `Finset.prod` cannot define
    "the product of all elements" without commutativity. -/
theorem two_elt_prod_ne {a b : G} (h : a * b ≠ b * a) :
    ([a, b] : List G).prod ≠ ([b, a] : List G).prod := by
  simpa using h

/-- ...yet the images of both orderings in the abelianization agree,
    illustrating `abelianization_prod_enum` on the smallest ordered pair. -/
theorem two_elt_abelianization_eq (a b : G) :
    Abelianization.of ([a, b] : List G).prod
      = Abelianization.of ([b, a] : List G).prod := by
  simp only [List.prod_cons, List.prod_nil, mul_one, map_mul]
  exact mul_comm _ _

end WilsonsTheoremOQ04OQ02OQ01
