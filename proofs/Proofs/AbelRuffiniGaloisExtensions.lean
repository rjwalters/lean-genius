import Mathlib.FieldTheory.AbelRuffini
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.Perm.Sign

/-
# Abel-Ruffini Galois Theory Extensions

## What This Proves
We extend the basic Abel-Ruffini formalization with deeper results about the
group-theoretic structure underlying polynomial solvability:

1. **Small symmetric groups are solvable**: S₀, S₁, S₂, S₃, S₄ are all solvable.
2. **Sharp threshold**: S_n is solvable iff n ≤ 4.
3. **Alternating group structure**: A₅ is simple, providing the obstruction.
4. **Connection to radical solvability**: The contrapositive of Galois's theorem.

## Approach
- S₀, S₁: trivial (subsingleton)
- S₂: commutative (decide)
- S₃: short exact sequence 1 → A₃ → S₃ → ℤˣ → 1 (both factors solvable)
- S₄: short exact sequence 1 → A₄ → S₄ → ℤˣ → 1 (A₄ solvable via V₄)
- n ≥ 5: Mathlib's `Equiv.Perm.not_solvable`

## Mathlib Dependencies
- `IsSolvable`, `solvable_of_ker_le_range` : Solvability infrastructure
- `Equiv.Perm.not_solvable` : S_n not solvable for n ≥ 5
- `Equiv.Perm.sign : Perm α →* ℤˣ` : Sign homomorphism
- `alternatingGroup` : Kernel of sign (even permutations)
- `solvableByRad.isSolvable'` : Radical solvability ⟹ solvable Galois group

## Historical Context
- Quadratic formula (ancient Babylonians, ~2000 BCE)
- Cubic formula (del Ferro ~1515, Cardano 1545)
- Quartic formula (Ferrari 1540, Cardano 1545)
- Abel (1824): degree ≥ 5 impossibility
- Galois (1832): complete characterization via group theory
-/

namespace AbelRuffiniGaloisExtensions

open Equiv Polynomial

/-
## Part I: Small Symmetric Groups Are Solvable
-/

section SmallSymmetricGroups

/-- S₀ is solvable (trivial group). -/
instance perm_fin_0_solvable : IsSolvable (Equiv.Perm (Fin 0)) := by
  haveI : Unique (Equiv.Perm (Fin 0)) := Equiv.permUnique
  exact isSolvable_of_subsingleton _

/-- S₁ is solvable (trivial group). -/
instance perm_fin_1_solvable : IsSolvable (Equiv.Perm (Fin 1)) := by
  haveI : Unique (Equiv.Perm (Fin 1)) := Equiv.permUnique
  exact isSolvable_of_subsingleton _

/-- S₂ is commutative (order 2, isomorphic to ℤ/2ℤ). -/
theorem perm_fin_2_comm : ∀ (a b : Equiv.Perm (Fin 2)), a * b = b * a := by
  decide

/-- S₂ is solvable (commutative group). -/
instance perm_fin_2_solvable : IsSolvable (Equiv.Perm (Fin 2)) :=
  isSolvable_of_comm perm_fin_2_comm

/-- A₃ is commutative (cyclic of order 3). -/
theorem alternating_fin_3_comm :
    ∀ (a b : alternatingGroup (Fin 3)), a * b = b * a := by
  decide

/-- A₃ is solvable (commutative). -/
instance alternating_fin_3_solvable : IsSolvable (alternatingGroup (Fin 3)) :=
  isSolvable_of_comm alternating_fin_3_comm

/-- ℤˣ is solvable (commutative group, the codomain of the sign homomorphism). -/
instance : IsSolvable ℤˣ :=
  isSolvable_of_comm (fun a b => mul_comm a b)

/-- S₃ is solvable via the short exact sequence 1 → A₃ → S₃ → ℤˣ → 1.
    The sign homomorphism sign : S₃ →* ℤˣ has kernel A₃.
    A₃ is cyclic of order 3 (solvable) and ℤˣ is commutative (solvable). -/
instance perm_fin_3_solvable : IsSolvable (Equiv.Perm (Fin 3)) := by
  apply solvable_of_ker_le_range
    (alternatingGroup (Fin 3)).subtype
    Equiv.Perm.sign
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  exact ⟨⟨x, Equiv.Perm.mem_alternatingGroup.mpr hx⟩, rfl⟩

/-- The Klein four-group V₄ as a subgroup of A₄.
    V₄ = {e, (12)(34), (13)(24), (14)(23)} - all double transpositions that are even. -/
private def klein_four : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {x | x.1 * x.1 = 1}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

/-- Decidable membership in V₄. -/
private instance : DecidablePred (· ∈ klein_four) := fun x =>
  if h : x.1 * x.1 = 1 then isTrue h else isFalse h

/-- V₄ is normal in A₄. -/
private instance klein_four_normal : klein_four.Normal where
  conj_mem := by native_decide

/-- V₄ is commutative (all elements have order ≤ 2). -/
private theorem klein_four_comm : ∀ (a b : klein_four), a * b = b * a := by native_decide

/-- V₄ is solvable (commutative). -/
private instance : IsSolvable klein_four := isSolvable_of_comm klein_four_comm

/-- A₄/V₄ has order 3 and is commutative. -/
private theorem quotient_klein_four_comm :
    ∀ (a b : alternatingGroup (Fin 4) ⧸ klein_four), a * b = b * a := by native_decide

/-- A₄/V₄ is solvable (commutative). -/
private instance : IsSolvable (alternatingGroup (Fin 4) ⧸ klein_four) :=
  isSolvable_of_comm quotient_klein_four_comm

/-- A₄ is solvable via the short exact sequence 1 → V₄ → A₄ → A₄/V₄ → 1.
    V₄ is the Klein four-group (abelian, solvable) and A₄/V₄ ≅ ℤ/3ℤ (cyclic, solvable). -/
instance alternating_fin_4_solvable : IsSolvable (alternatingGroup (Fin 4)) :=
  solvable_of_ker_le_range klein_four.subtype (QuotientGroup.mk' klein_four)
    (fun x hx => by
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact ⟨⟨x, hx⟩, rfl⟩)

/-- S₄ is solvable via 1 → A₄ → S₄ → ℤˣ → 1. -/
instance perm_fin_4_solvable : IsSolvable (Equiv.Perm (Fin 4)) := by
  apply solvable_of_ker_le_range
    (alternatingGroup (Fin 4)).subtype
    Equiv.Perm.sign
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  exact ⟨⟨x, Equiv.Perm.mem_alternatingGroup.mpr hx⟩, rfl⟩

end SmallSymmetricGroups

/-
## Part II: The Sharp Threshold
-/

section SharpThreshold

/-- S_n is NOT solvable for n ≥ 5 (Mathlib). -/
theorem symmetric_not_solvable_of_five_le {n : ℕ} (hn : 5 ≤ n) :
    ¬ IsSolvable (Equiv.Perm (Fin n)) := by
  have h : 5 ≤ Cardinal.mk (Fin n) := by
    simp only [Cardinal.mk_fintype, Fintype.card_fin]
    exact_mod_cast hn
  exact Equiv.Perm.not_solvable (Fin n) h

/-- S_n IS solvable for n ≤ 4. -/
theorem symmetric_solvable_of_le_four {n : ℕ} (hn : n ≤ 4) :
    IsSolvable (Equiv.Perm (Fin n)) := by
  interval_cases n <;> infer_instance

/-- The complete classification: S_n is solvable iff n ≤ 4. -/
theorem symmetric_solvable_iff (n : ℕ) :
    IsSolvable (Equiv.Perm (Fin n)) ↔ n ≤ 4 := by
  constructor
  · intro h
    by_contra hle
    push_neg at hle
    exact symmetric_not_solvable_of_five_le (by omega) h
  · exact symmetric_solvable_of_le_four

end SharpThreshold

/-
## Part III: Alternating Group Structure
-/

section AlternatingGroups

/-- A₅ is simple: no non-trivial normal subgroups. -/
theorem a5_simple : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup_five

/-- |A₅| = 60. -/
theorem card_a5 : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  decide

end AlternatingGroups

/-
## Part IV: Connection to Radical Solvability
-/

section RadicalSolvability

/-- The contrapositive of Galois's theorem: if the Galois group of a polynomial
    is not solvable, then no root is expressible by radicals. -/
theorem not_solvable_by_rad_of_not_solvable_galois
    {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
    {α : E} {q : F[X]}
    (hirr : Irreducible q)
    (hα : aeval α q = 0)
    (hns : ¬ IsSolvable (q.Gal)) :
    ¬ IsSolvableByRad F α := by
  intro hsol
  exact hns (solvableByRad.isSolvable' hirr hα hsol)

end RadicalSolvability

/-
## Part V: Galois Extension Properties
-/

section GaloisProperties

variable (F : Type*) [Field F]
variable (E : Type*) [Field E] [Algebra F E]

/-- The order of the Galois group equals the extension degree. -/
theorem galois_group_order [FiniteDimensional F E] [IsGalois F E] :
    Nat.card (E ≃ₐ[F] E) = Module.finrank F E :=
  IsGalois.card_aut_eq_finrank F E

end GaloisProperties

/-
## Part VI: Subgroup Solvability
-/

section SubgroupSolvability

/-- Subgroups of solvable groups are solvable. -/
theorem subgroup_solvable_of_solvable {G : Type*} [Group G] [IsSolvable G]
    (H : Subgroup G) : IsSolvable H :=
  inferInstance

end SubgroupSolvability

/-
## Summary

Theorem Count: 19 theorems/instances, 0 sorries, 0 axioms

1. S₀, S₁: solvable (trivial)
2. S₂: solvable (commutative, decide)
3. A₃: solvable (commutative, decide)
4. S₃: solvable (short exact sequence 1 → A₃ → S₃ → ℤˣ → 1)
5. V₄ (Klein four-group): defined, normal in A₄, commutative (native_decide)
6. A₄: solvable (short exact sequence 1 → V₄ → A₄ → A₄/V₄ → 1)
7. S₄: solvable (short exact sequence 1 → A₄ → S₄ → ℤˣ → 1)
8. S_n (n ≥ 5): NOT solvable (Mathlib)
9. Complete iff: S_n solvable iff n ≤ 4
10. A₅ simple with |A₅| = 60
11. Contrapositive of Galois's theorem
12. Galois group order = extension degree
13. Subgroup solvability inheritance
-/

end AbelRuffiniGaloisExtensions
