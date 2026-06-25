import Mathlib

/-
# The Galois Correspondence for ℂ / ℝ

## What This Proves

This is the **Galois-theoretic** route to the no-intermediate-fields theorem for
`ℝ ⊆ ℂ` (open question oq-04-oq-03 of `fundamental-theorem-algebra-oq-04`,
"C is the Unique Algebraic Closure of R"). The parent entry proved
`no_intermediate_field` by the *tower law* (`[ℂ:ℝ] = 2` forces `[K:ℝ] ∈ {1,2}`).
Here we give the genuinely different argument the open question asks for:

1. `ℂ / ℝ` is a **Galois extension** (`IsGalois ℝ ℂ`): finite, separable
   (char 0), and normal (ℂ is an algebraic closure of ℝ).
2. The Galois group has **order 2**: `Nat.card (ℂ ≃ₐ[ℝ] ℂ) = [ℂ:ℝ] = 2`.
3. Hence `Gal(ℂ/ℝ)` is **cyclic** — i.e. `≅ ℤ/2ℤ`, the unique group of order 2.
   Its nontrivial element is complex conjugation.
4. The **fundamental theorem of Galois theory** gives an order-reversing bijection
   `IntermediateField ℝ ℂ ≃o (Subgroup Gal(ℂ/ℝ))ᵒᵈ`.
5. A group of prime order 2 has exactly two subgroups (`⊥` and `⊤`, by Lagrange),
   so via the correspondence there are exactly two intermediate fields, and every
   intermediate field equals `⊥ = ℝ` or `⊤ = ℂ`.

The punchline `intermediateField_eq_bot_or_top` is *stronger* than the parent's
`no_intermediate_field`: it pins each intermediate field to `⊥` or `⊤` rather than
just constraining its degree, and it does so through the subgroup lattice rather
than the tower law.

## Approach
- `Algebra.IsSeparable ℝ ℂ` is automatic in characteristic 0.
- `Normal ℝ ℂ` comes from `IsAlgClosure.normal` once `IsAlgClosure ℝ ℂ` is in scope.
- `IsGalois.card_aut_eq_finrank` + `Complex.finrank_real_complex` give order 2.
- `isCyclic_of_prime_card` gives cyclicity.
- `IsGalois.intermediateFieldEquivSubgroup` is the correspondence.
- Lagrange (`Subgroup.card_subgroup_dvd_card`) plus
  `Subgroup.eq_bot_of_card_eq` / `eq_top_of_card_eq` enumerate the subgroups.

This file is self-contained: it re-establishes `IsAlgClosure ℝ ℂ` (3 lines, as in
the parent) so it does not depend on the parent's compiled object file.
-/

open Complex
open scoped IntermediateField

namespace FTAGaloisCorrespondence

/-! ## Setup: ℂ as an algebraic closure of ℝ -/

/-- ℂ is algebraic over ℝ (finite extension ⇒ algebraic). -/
instance : Algebra.IsAlgebraic ℝ ℂ := Algebra.IsAlgebraic.of_finite ℝ ℂ

/-- ℂ is an algebraic closure of ℝ — the instance that supplies `Normal ℝ ℂ`. -/
instance : IsAlgClosure ℝ ℂ where
  isAlgClosed := Complex.isAlgClosed
  isAlgebraic := inferInstance

/-! ## Part 1: ℂ / ℝ is a Galois extension -/

/-- `ℂ / ℝ` is normal: ℂ is an algebraic closure of ℝ. -/
example : Normal ℝ ℂ := inferInstance

/-- `ℂ / ℝ` is separable: characteristic zero. -/
example : Algebra.IsSeparable ℝ ℂ := inferInstance

/-- **`ℂ / ℝ` is a Galois extension.** Finite + separable (char 0) + normal
    (algebraic closure). This is the structural hypothesis the entire Galois
    correspondence rests on. -/
instance galois_complex_real : IsGalois ℝ ℂ := IsGalois.mk

/-! ## Part 2: the Galois group has order 2 -/

/-- **`|Gal(ℂ/ℝ)| = 2`.** For a Galois extension the automorphism group has order
    equal to the degree, and `[ℂ:ℝ] = 2`. -/
theorem card_galoisGroup_eq_two : Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2 := by
  rw [IsGalois.card_aut_eq_finrank ℝ ℂ, Complex.finrank_real_complex]

/-- **`Gal(ℂ/ℝ)` is cyclic**, hence isomorphic to `ℤ/2ℤ` (the unique group of
    order 2). Its single nontrivial element is complex conjugation. -/
theorem galoisGroup_isCyclic : IsCyclic (ℂ ≃ₐ[ℝ] ℂ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isCyclic_of_prime_card (p := 2) card_galoisGroup_eq_two

/-! ## Part 3: the Galois correspondence -/

/-- **The fundamental theorem of Galois theory for `ℂ / ℝ`.** An order-reversing
    bijection between intermediate fields of `ℝ ⊆ ℂ` and subgroups of `Gal(ℂ/ℝ)`
    (the order reversal is encoded by the `ᵒᵈ`). -/
noncomputable def galoisCorrespondence :
    IntermediateField ℝ ℂ ≃o (Subgroup (ℂ ≃ₐ[ℝ] ℂ))ᵒᵈ :=
  IsGalois.intermediateFieldEquivSubgroup

/-- The correspondence is a bijection, so intermediate fields and subgroups are
    equinumerous. -/
theorem card_intermediateField_eq_card_subgroup :
    Nat.card (IntermediateField ℝ ℂ) = Nat.card (Subgroup (ℂ ≃ₐ[ℝ] ℂ)) :=
  Nat.card_congr galoisCorrespondence.toEquiv

/-! ## Part 4: subgroups of an order-2 group -/

/-- **Every subgroup of `Gal(ℂ/ℝ)` is `⊥` or `⊤`.** The group has prime order 2,
    so by Lagrange any subgroup has order `1` or `2`. -/
theorem subgroup_eq_bot_or_top (H : Subgroup (ℂ ≃ₐ[ℝ] ℂ)) : H = ⊥ ∨ H = ⊤ := by
  have hdvd : Nat.card H ∣ Nat.card (ℂ ≃ₐ[ℝ] ℂ) := Subgroup.card_subgroup_dvd_card H
  rw [card_galoisGroup_eq_two] at hdvd
  -- a divisor of the prime 2 is 1 or 2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact Or.inl (Subgroup.eq_bot_of_card_eq H h1)
  · exact Or.inr (Subgroup.eq_top_of_card_eq H (by rw [h2, card_galoisGroup_eq_two]))

/-! ## Part 5: no intermediate fields (Galois route) -/

/-- **No proper intermediate fields (via Galois theory).** Every intermediate field
    of `ℝ ⊆ ℂ` is either `⊥ = ℝ` or `⊤ = ℂ`.

    Proof: send `K` through the Galois correspondence to a subgroup `H`; `H` is `⊥`
    or `⊤` (order-2 group); the correspondence reverses order, sending `⊤` (field)
    to `⊥` (subgroup) and `⊥` (field) to `⊤` (subgroup), and is injective. This is
    the structural alternative to the parent's tower-law degree count. -/
theorem intermediateField_eq_bot_or_top (K : IntermediateField ℝ ℂ) :
    K = ⊥ ∨ K = ⊤ := by
  have e := galoisCorrespondence
  -- view `e K` as an ordinary subgroup
  rcases subgroup_eq_bot_or_top (OrderDual.ofDual (e K)) with h | h
  · -- ofDual (e K) = ⊥  ⇒  e K = (⊤ : dual) = e ⊤  ⇒  K = ⊤
    right
    apply e.injective
    rw [e.map_top]
    exact OrderDual.toDual.injective (by simpa using h)
  · -- ofDual (e K) = ⊤  ⇒  e K = (⊥ : dual) = e ⊥  ⇒  K = ⊥
    left
    apply e.injective
    rw [e.map_bot]
    exact OrderDual.toDual.injective (by simpa using h)

end FTAGaloisCorrespondence
