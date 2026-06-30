import Proofs.LebesgueMeasureOQ06

/-
# Lebesgue Measure — OQ-06-OQ-01: Hausdorff's free subgroup of SO(3), as an honest subgroup

## Research Problem: lebesgue-measure-oq-06-oq-01

**Hausdorff free subgroup theorem in SO(3) formalized in Lean.**

The parent entry (`lebesgue-measure-oq-06`, `LebesgueMeasureOQ06.lean`) proves
**Hausdorff's theorem** (1914): the rotation group of `ℝ³` contains a free subgroup
of rank 2. Concretely, two rotations `φ`, `ψ` by `arccos(1/3)` about perpendicular
axes generate a free group, established there as

```
hausdorff_free_subgroup :
  ∃ (φ ψ : ℝ³ ≃ₗᵢ[ℝ] ℝ³),
    Function.Injective (FreeGroup.lift (fun b => if b then φ.toLinearEquiv else ψ.toLinearEquiv))
```

That statement records freeness through the *underlying linear equivalences*
(`≃ₗ`), forgetting that `φ` and `ψ` are isometries. This file upgrades it to a
statement *internal to the isometry group* `ℝ³ ≃ₗᵢ[ℝ] ℝ³` (the orthogonal group
`O(3)`; the two generators are rotations, hence lie in `SO(3)`), and then packages
the result the way group theory usually wants it:

1. `toLinearEquivHom` — the forgetful monoid homomorphism
   `(ℝ³ ≃ₗᵢ[ℝ] ℝ³) →* (ℝ³ ≃ₗ[ℝ] ℝ³)`, which is what lets freeness be transported
   between the two settings.
2. `hausdorff_free_subgroup_isometry` — the free embedding realised **inside** the
   isometry group: `FreeGroup.lift (fun b => bif b then φ else ψ)` is injective as a
   map into `ℝ³ ≃ₗᵢ[ℝ] ℝ³`.
3. `isometryGroup_contains_freeGroup` — an injective group homomorphism
   `FreeGroup Bool →* (ℝ³ ≃ₗᵢ[ℝ] ℝ³)`.
4. `exists_freeGroup_mulEquiv_rotationSubgroup` — there is a subgroup `S` of the
   isometry group with `FreeGroup Bool ≃* S`: i.e. `SO(3)` contains a literal copy
   of the rank-2 free group `F₂`.
5. `exists_noncommuting_rotations` — a clean concrete corollary: there exist two
   rotations that do not commute, witnessing non-abelianness of `SO(3)`.

Everything is derived from the parent's hard orbit/`ℤ[√2]` invariant; no new
geometry is reproved and no axioms or `sorry`s are introduced. (The parent file
does declare one `axiom banach_tarski`, but none of the results below depend on it
— see `#print axioms` checks at the end.)

Tags: measure-theory, banach-tarski, paradox, free-group, SO(3), axiom-of-choice
-/

set_option linter.unusedVariables false

namespace BanachTarski

open Function

/-- The three-dimensional Euclidean rotation/isometry group `O(3)`
    (linear isometric self-equivalences of `ℝ³`). -/
abbrev Rot3 := EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)

/-- The general linear automorphism group of `ℝ³` (linear self-equivalences). -/
abbrev Lin3 := EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3)

/-- The forgetful map "a linear *isometry* is in particular a linear equivalence",
    bundled as a **group homomorphism** `Rot3 →* Lin3`.

    Multiplicativity is exactly `LinearIsometryEquiv.toLinearEquiv_trans`, since both
    groups put composition on the underlying maps (`a * b = b.trans a`). This is the
    bridge that lets us move Hausdorff's freeness statement from the `≃ₗ` world (where
    the parent proves it) into the isometry group. -/
def toLinearEquivHom : Rot3 →* Lin3 :=
  MonoidHom.mk' (fun e => e.toLinearEquiv) <| by
    intro a b
    show (a * b).toLinearEquiv = a.toLinearEquiv * b.toLinearEquiv
    rw [LinearEquiv.mul_eq_trans]
    exact LinearIsometryEquiv.toLinearEquiv_trans b a

@[simp]
theorem toLinearEquivHom_apply (e : Rot3) : toLinearEquivHom e = e.toLinearEquiv := rfl

/-- **Hausdorff's free subgroup theorem, internal to the isometry group.**

    There exist rotations `φ, ψ` of `ℝ³` (by `arccos(1/3)` about perpendicular axes)
    such that the free group on two generators embeds into the isometry group
    `ℝ³ ≃ₗᵢ[ℝ] ℝ³` via `b ↦ if b then φ else ψ`. Equivalently: `⟨φ, ψ⟩` is a free
    subgroup of rank 2 of `O(3)` (indeed of `SO(3)`, as both generators are rotations).

    Upgrades `hausdorff_free_subgroup`, whose injectivity is stated for the underlying
    *linear* equivalences, to injectivity for the *isometric* equivalences themselves. -/
theorem hausdorff_free_subgroup_isometry :
    ∃ (φ ψ : Rot3),
      Function.Injective (FreeGroup.lift (fun b : Bool => bif b then φ else ψ)) := by
  obtain ⟨φ, ψ, hinj⟩ := hausdorff_free_subgroup
  refine ⟨φ, ψ, ?_⟩
  -- The parent's lift (into `Lin3`) factors as `toLinearEquivHom ∘ (our lift into Rot3)`.
  have hbridge :
      (FreeGroup.lift (fun b : Bool => if b then φ.toLinearEquiv else ψ.toLinearEquiv))
        = toLinearEquivHom.comp
            (FreeGroup.lift (fun b : Bool => bif b then φ else ψ)) := by
    apply FreeGroup.ext_hom
    intro b
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of, toLinearEquivHom_apply]
    cases b <;> rfl
  -- Injectivity transfers along the factorisation.
  intro x y hxy
  apply hinj
  rw [hbridge, MonoidHom.comp_apply, MonoidHom.comp_apply, hxy]

/-- **`O(3)` (hence `SO(3)`) contains a free group of rank 2**, packaged as an
    injective group homomorphism `FreeGroup Bool →* (ℝ³ ≃ₗᵢ[ℝ] ℝ³)`. -/
theorem isometryGroup_contains_freeGroup :
    ∃ f : FreeGroup Bool →* Rot3, Function.Injective f := by
  obtain ⟨φ, ψ, hinj⟩ := hausdorff_free_subgroup_isometry
  exact ⟨FreeGroup.lift (fun b : Bool => bif b then φ else ψ), hinj⟩

/-- **`SO(3)` contains a literal copy of the free group `F₂`.**

    There is a subgroup `S` of the three-dimensional isometry group together with a
    group isomorphism `FreeGroup Bool ≃* S`. This is the precise sense in which the
    Banach–Tarski "paradoxical" combinatorics of `F₂` are realised by actual rotations. -/
theorem exists_freeGroup_mulEquiv_rotationSubgroup :
    ∃ S : Subgroup Rot3, Nonempty (FreeGroup Bool ≃* S) := by
  obtain ⟨f, hf⟩ := isometryGroup_contains_freeGroup
  exact ⟨f.range, ⟨MonoidHom.ofInjective hf⟩⟩

/-- In `FreeGroup Bool`, the two generators do not commute: `a·b ≠ b·a`.

    Proof: map into the symmetric group `S₃ = Perm (Fin 3)` sending the generators to
    two transpositions `(0 1)` and `(1 2)` that fail to commute, then `decide`. -/
theorem freeGroup_of_true_false_ne :
    (FreeGroup.of true * FreeGroup.of false : FreeGroup Bool)
      ≠ FreeGroup.of false * FreeGroup.of true := by
  intro h
  have h' :
      (FreeGroup.lift (fun b : Bool => bif b then Equiv.swap (0 : Fin 3) 1 else Equiv.swap 1 2))
          (FreeGroup.of true * FreeGroup.of false)
        = (FreeGroup.lift (fun b : Bool => bif b then Equiv.swap (0 : Fin 3) 1 else Equiv.swap 1 2))
          (FreeGroup.of false * FreeGroup.of true) :=
    congrArg _ h
  simp only [map_mul, FreeGroup.lift_apply_of, Bool.cond_true, Bool.cond_false] at h'
  revert h'
  decide

/-- **There exist two non-commuting rotations of `ℝ³`** — a concrete witness that
    `SO(3)` is non-abelian, extracted directly from the free generators `φ, ψ`. -/
theorem exists_noncommuting_rotations :
    ∃ (φ ψ : Rot3), φ * ψ ≠ ψ * φ := by
  obtain ⟨φ, ψ, hinj⟩ := hausdorff_free_subgroup_isometry
  refine ⟨φ, ψ, fun hcomm => freeGroup_of_true_false_ne (hinj ?_)⟩
  simp only [map_mul, FreeGroup.lift_apply_of, Bool.cond_true, Bool.cond_false]
  exact hcomm

-- Axiom audit: none of these results depend on `banach_tarski` (the parent's lone
-- axiom). They rest only on the standard foundational axioms.
-- #print axioms hausdorff_free_subgroup_isometry
-- #print axioms exists_freeGroup_mulEquiv_rotationSubgroup
-- #print axioms exists_noncommuting_rotations

end BanachTarski
