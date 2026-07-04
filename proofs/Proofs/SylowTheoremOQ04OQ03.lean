/-
  Toward the simplicity of PSL(2, p) for primes p ≥ 5 (Sylow OQ-04 OQ-03)

  Parent open question sylow-theorem-oq-04-oq-03: prove that PSL(2, p) is simple
  for every prime p ≥ 5, generalizing the parent entry's A₅ = PSL(2,5) result to
  the first infinite family of finite simple groups.

  The full theorem is genuinely blocked on a large body of missing Mathlib
  infrastructure (the action of PSL(2,p) on the projective line P¹(𝔽_p), its
  2-transitivity, an Iwasawa structure, and perfectness for p ≥ 5). The standard
  modern route is *not* a raw Sylow count but Iwasawa's criterion applied to that
  action; see the research knowledge file for the full assessment.

  This file builds one clean, fully verified piece of that infrastructure: the
  **unipotent one-parameter subgroup**

      U = { [[1, t], [0, 1]] : t ∈ 𝔽_p } ⊆ SL(2, 𝔽_p).

  U is exactly the abelian normal subgroup of the Borel (stabilizer of ∞) that the
  Iwasawa criterion requires, and it is the order-p Sylow subgroup of SL(2, p).
  We show:

  * `unipotentUpper t` is a genuine element of `SL(2, ZMod p)` (determinant 1);
  * `t ↦ unipotentUpper t` is an injective group homomorphism from the additive
    group `(ZMod p, +)` (written multiplicatively) into `SL(2, ZMod p)`
    (`unipotentHom`), so its image is abelian and isomorphic to `ZMod p`;
  * the image has cardinality exactly `p` (the order-p Sylow / unipotent subgroup).

  Everything here is `sorry`-free and axiom-free; the deep simplicity theorem
  remains open.

  References:
  - Rotman, An Introduction to the Theory of Groups (4th ed.), §9.
  - Dixon & Mortimer, Permutation Groups, §3.3 (Iwasawa's lemma), §2.8.

  Tags: group-theory, sylow, PSL, special-linear-group, unipotent, iwasawa
-/

import Mathlib

open Matrix

namespace SylowOQ04OQ03

variable {p : ℕ} [Fact p.Prime]

/-!
## The unipotent one-parameter subgroup of `SL(2, ZMod p)`

We embed `(ZMod p, +)` into `SL(2, ZMod p)` via the upper-triangular unipotent
matrices `[[1, t], [0, 1]]`.
-/

/-- The upper unipotent matrix `[[1, t], [0, 1]]`, viewed as an element of
`SL(2, ZMod p)`. Its determinant is `1 · 1 − t · 0 = 1`. -/
def unipotentUpper (t : ZMod p) : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem val_unipotentUpper (t : ZMod p) :
    (unipotentUpper t : Matrix (Fin 2) (Fin 2) (ZMod p)) = !![1, t; 0, 1] := rfl

/-- The unipotent embedding is additive: `[[1,s],[0,1]] · [[1,t],[0,1]] = [[1,s+t],[0,1]]`. -/
theorem unipotentUpper_mul (s t : ZMod p) :
    unipotentUpper s * unipotentUpper t = unipotentUpper (s + t) := by
  apply Subtype.ext
  show (!![1, s; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) * !![1, t; 0, 1]
      = !![1, s + t; 0, 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The unipotent embedding sends `0` to the identity matrix. -/
theorem unipotentUpper_zero : unipotentUpper (0 : ZMod p) = 1 := by
  apply Subtype.ext
  show (!![1, (0 : ZMod p); 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) = 1
  rw [Matrix.one_fin_two]

/-- Elements of the unipotent subgroup commute (it is abelian). -/
theorem unipotentUpper_comm (s t : ZMod p) :
    unipotentUpper s * unipotentUpper t = unipotentUpper t * unipotentUpper s := by
  rw [unipotentUpper_mul, unipotentUpper_mul, add_comm]

/-- The unipotent embedding is injective (read off the top-right entry). -/
theorem unipotentUpper_injective :
    Function.Injective (unipotentUpper (p := p)) := by
  intro s t h
  have h' : (unipotentUpper s : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1
      = (unipotentUpper t : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 1 := by rw [h]
  simpa using h'

/-- The unipotent one-parameter subgroup packaged as a group homomorphism from the
additive group `(ZMod p, +)` (written multiplicatively) into `SL(2, ZMod p)`.

This is the abelian normal subgroup of the Borel stabilizer required by Iwasawa's
simplicity criterion for `PSL(2, p)`. -/
def unipotentHom :
    Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod p) where
  toFun t := unipotentUpper (Multiplicative.toAdd t)
  map_one' := by simpa using unipotentUpper_zero
  map_mul' s t := by
    simpa using
      (unipotentUpper_mul (Multiplicative.toAdd s) (Multiplicative.toAdd t)).symm

@[simp] theorem unipotentHom_apply (t : Multiplicative (ZMod p)) :
    unipotentHom t = unipotentUpper (Multiplicative.toAdd t) := rfl

/-- `unipotentHom` is injective, so its range is a subgroup of `SL(2, ZMod p)`
isomorphic to `(ZMod p, +)`. -/
theorem unipotentHom_injective : Function.Injective (unipotentHom (p := p)) := by
  intro s t h
  exact Multiplicative.toAdd.injective (unipotentUpper_injective h)

/-- The unipotent subgroup has cardinality exactly `p`: it is the order-`p`
Sylow-`p` subgroup of `SL(2, p)`. -/
theorem card_unipotent_range :
    Nat.card (Set.range (unipotentUpper (p := p))) = p := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).pos.ne'⟩
  have e : ZMod p ≃ Set.range (unipotentUpper (p := p)) :=
    Equiv.ofInjective _ unipotentUpper_injective
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, ZMod.card]

end SylowOQ04OQ03
