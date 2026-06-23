import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-
# The Algebraic Obstruction Behind No-Retraction: ℤ is not a retract of any finite or torsion group
# (brouwer-fixed-point-oq-01-oq-02-oq-02)

## The Open Question

The parent entry OQ-01-OQ-02 ("No-Retraction via Singular Homology") proves the
No-Retraction Theorem by reducing it, through the homology functor, to a purely
algebraic fact: **the identity `id : ℤ →+ ℤ` cannot factor through the trivial
group**. Concretely, the homology of the disc `Bⁿ` is `0` and the homology of the
sphere `Sⁿ⁻¹` is `ℤ`, and a retraction would split `id_ℤ` through `0`.

The parent argues this with the specific computation `1 = ψ(()) = 2`. This raises
the structural question: **through exactly which groups can `id_ℤ` fail/refuse to
factor?** The trivial group is only the smallest case.

## Result

We isolate the general algebraic obstruction. Say `ℤ` is a **retract of `G`** if
there are additive homomorphisms `φ : ℤ →+ G` and `ψ : G →+ ℤ` with
`ψ ∘ φ = id`. Then:

1. `injective_of_retract` / `surjective_of_retract` — `φ` is injective and `ψ`
   is surjective (the section/retraction splitting).

2. `infinite_of_retract` — `G` must be **infinite**: `φ` embeds the infinite
   group `ℤ` into `G`.

3. `not_retract_of_finite` — therefore `ℤ` is **not a retract of any finite
   group**. The trivial-group case used by the parent is the instance `G = PUnit`
   (`not_retract_of_subsingleton`).

4. `gen_not_isOfFinAddOrder` — the image `φ 1` has **infinite additive order**:
   `n • φ 1 = 0` would force `n = ψ(n • φ 1) = 0`.

5. `not_isTorsion_of_retract` — therefore `ℤ` is **not a retract of any torsion
   group**: a retract must contain an element of infinite order. This strictly
   generalizes the finite case.

These pin down what the homology computation actually needs: not that `Bⁿ` has
*trivial* homology, but merely that its homology is *torsion* (in particular
finite) — any such group cannot receive `id_ℤ` as a retract.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace BrouwerFixedPointOQ01OQ02OQ02

variable {G : Type*} [AddCommGroup G]

/-- The splitting relation: `ψ ∘ φ = id` evaluated pointwise, `ψ (φ n) = n`. -/
theorem retract_apply (φ : ℤ →+ G) (ψ : G →+ ℤ)
    (h : ψ.comp φ = AddMonoidHom.id ℤ) (n : ℤ) : ψ (φ n) = n := by
  rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.id_apply]

/-- The section `φ` of a retract is injective (it has the left inverse `ψ`). -/
theorem injective_of_retract (φ : ℤ →+ G) (ψ : G →+ ℤ)
    (h : ψ.comp φ = AddMonoidHom.id ℤ) : Function.Injective φ :=
  Function.LeftInverse.injective (g := ψ) (retract_apply φ ψ h)

/-- The retraction `ψ` of a retract is surjective (it has the right inverse `φ`). -/
theorem surjective_of_retract (φ : ℤ →+ G) (ψ : G →+ ℤ)
    (h : ψ.comp φ = AddMonoidHom.id ℤ) : Function.Surjective ψ :=
  Function.RightInverse.surjective (g := φ) (retract_apply φ ψ h)

/-- **`ℤ` retracts only onto infinite groups.** The section `φ` embeds the
    infinite group `ℤ` into `G`, so `G` is infinite. -/
theorem infinite_of_retract (φ : ℤ →+ G) (ψ : G →+ ℤ)
    (h : ψ.comp φ = AddMonoidHom.id ℤ) : Infinite G :=
  Infinite.of_injective φ (injective_of_retract φ ψ h)

/-- **`ℤ` is not a retract of any finite group.** This is the general form of the
    parent's algebraic core; the trivial-group case is `G = PUnit`. -/
theorem not_retract_of_finite [Finite G] :
    ¬ ∃ (φ : ℤ →+ G) (ψ : G →+ ℤ), ψ.comp φ = AddMonoidHom.id ℤ := by
  rintro ⟨φ, ψ, h⟩
  haveI := infinite_of_retract φ ψ h
  exact not_finite G

/-- **The trivial-group core, recovered.** `ℤ` is not a retract of any
    subsingleton group — in particular not of the trivial group `0`, the
    homology of the disc. This is exactly the parent's `id_ℤ` cannot factor
    through `Unit`. -/
theorem not_retract_of_subsingleton [Subsingleton G] :
    ¬ ∃ (φ : ℤ →+ G) (ψ : G →+ ℤ), ψ.comp φ = AddMonoidHom.id ℤ :=
  haveI : Finite G := Finite.of_subsingleton
  not_retract_of_finite

/-- **The generator maps to an element of infinite order.** If `ψ ∘ φ = id`, then
    `φ 1` has infinite additive order: any `n • φ 1 = 0` with `n > 0` would give
    `n = ψ (n • φ 1) = 0`. -/
theorem gen_not_isOfFinAddOrder (φ : ℤ →+ G) (ψ : G →+ ℤ)
    (h : ψ.comp φ = AddMonoidHom.id ℤ) : ¬ IsOfFinAddOrder (φ 1) := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  rintro ⟨n, hn, hzero⟩
  have hψ : ψ (n • φ 1) = 0 := by rw [hzero, map_zero]
  rw [map_nsmul, retract_apply φ ψ h, nsmul_eq_mul, mul_one] at hψ
  omega

/-- **`ℤ` is not a retract of any torsion group.** A retract must contain an
    element of infinite order (the image of the generator), so a torsion group —
    in which every element has finite order — cannot be one. This strictly
    generalizes `not_retract_of_finite` (finite groups are torsion). -/
theorem not_isTorsion_of_retract (φ : ℤ →+ G) (ψ : G →+ ℤ)
    (h : ψ.comp φ = AddMonoidHom.id ℤ) : ¬ AddMonoid.IsTorsion G :=
  fun htor => gen_not_isOfFinAddOrder φ ψ h (htor (φ 1))

/-- Packaged: `ℤ` is not a retract of any torsion group. -/
theorem not_retract_of_isTorsion (htor : AddMonoid.IsTorsion G) :
    ¬ ∃ (φ : ℤ →+ G) (ψ : G →+ ℤ), ψ.comp φ = AddMonoidHom.id ℤ := by
  rintro ⟨φ, ψ, h⟩
  exact not_isTorsion_of_retract φ ψ h htor

/-
## Significance

The No-Retraction Theorem (and with it Brouwer's fixed-point theorem) is proved
homologically by observing that a retraction `r : Bⁿ → Sⁿ⁻¹` would split the
identity of `Hₙ₋₁(Sⁿ⁻¹) ≅ ℤ` through `Hₙ₋₁(Bⁿ) = 0`. The parent file reduces this
to "the identity of `ℤ` cannot factor through the trivial group" and proves the
trivial case by hand.

This entry identifies the *general* algebraic obstruction and shows the trivial
group was a red herring: the identity of `ℤ` cannot factor through **any finite
group**, indeed through **any torsion group**, because a retract of `ℤ` must
contain an element of infinite order (the image of `1`). Equivalently, the
homological proof never needed `Hₙ₋₁(Bⁿ)` to be *zero* — only *torsion*. Any
contractible-enough computation giving a torsion disc-homology suffices to drive
the contradiction.

The splitting lemmas (`injective_of_retract`, `surjective_of_retract`) and the
infinite-order obstruction are self-contained, reusable facts about retracts of
`ℤ` in the category of abelian groups, independent of the topological setting.
-/

end BrouwerFixedPointOQ01OQ02OQ02
