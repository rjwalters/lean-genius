import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic

/-
# Cayley's Theorem

## What This Proves

**Cayley's theorem** is the foundational result of group theory that says every
abstract group is "concrete": it can be realised as a group of permutations.

Precisely, for any group `G` the **left-regular representation**

    λ : G → Equiv.Perm G,   λ(g) = (x ↦ g * x)

is an injective group homomorphism.  Each `g` acts on the underlying set of `G`
by left multiplication; this is a bijection (with inverse left multiplication by
`g⁻¹`), the assignment respects the group law (`λ(g·h) = λ(g) ∘ λ(h)`), and it is
injective because `λ(g) = λ(h)` evaluated at the identity gives `g·1 = h·1`,
i.e. `g = h`.

Consequently `G` is isomorphic to its image — a **subgroup of the symmetric
group** `Sym(G) = Equiv.Perm G`.  In other words, every group embeds into a
symmetric group.

## Approach

The entire content is already available in Mathlib through the regular
self-action of a group:

* `MulAction.toPermHom G G : G →* Equiv.Perm G` is the bundled left-regular
  representation (the self-action `g • x = g * x` comes from `Mul.toSMul`).
* `MulAction.toPerm_injective` shows the underlying map is injective for any
  *faithful* action, and the self-action of a group is faithful via
  `RightCancelMonoid.faithfulSMul` (a group is right-cancellative).
* `MulEquiv.ofInjective` upgrades the injective hom to an isomorphism onto its
  range, giving the "isomorphic to a subgroup of `Sym(G)`" form.

No `decide`/`native_decide` is used, so the proof is axiom-free (only Mathlib's
foundational `propext`/`Classical.choice`/`Quot.sound`).

## Distinctness

Despite the shared name, this is **not** the Cayley–Hamilton theorem (a matrix
identity, of which the gallery has many entries).  The group-theoretic Cayley
theorem — every group is a permutation group — is absent from the gallery.
-/

namespace CayleysTheoremOQ01

variable (G : Type*) [Group G]

/-- **The left-regular representation** as a bundled group homomorphism
`G →* Equiv.Perm G`.  It sends `g` to the permutation of (the underlying set of)
`G` given by left multiplication `x ↦ g * x`.  This is exactly the regular
self-action `MulAction.toPermHom G G`. -/
abbrev leftRegular : G →* Equiv.Perm G := MulAction.toPermHom G G

/-- The left-regular representation sends `g` to left multiplication `x ↦ g * x`. -/
theorem leftRegular_apply (g x : G) : leftRegular G g x = g * x := rfl

/-- **Cayley's theorem (injectivity form).** The left-regular representation
`G →* Equiv.Perm G` is injective: distinct group elements act as distinct
permutations.  This is the heart of Cayley's theorem. -/
theorem leftRegular_injective : Function.Injective (leftRegular G) := by
  simpa only [leftRegular, MulAction.coe_toPermHom] using
    (MulAction.toPerm_injective (α := G) (β := G))

/-- **Cayley's theorem (existence form).** Every group `G` admits an injective
homomorphism into the symmetric group `Equiv.Perm G` on its own underlying set —
equivalently, `G` is (isomorphic to) a permutation group. -/
theorem cayley : ∃ f : G →* Equiv.Perm G, Function.Injective f :=
  ⟨leftRegular G, leftRegular_injective G⟩

/-- **Cayley's theorem (subgroup-embedding form).** `G` is isomorphic to a
subgroup of the symmetric group `Equiv.Perm G`, namely the range of its
left-regular representation. -/
noncomputable def cayleyEquivRange : G ≃* (leftRegular G).range :=
  MonoidHom.ofInjective (leftRegular_injective G)

/-- The embedding `cayleyEquivRange` is given on elements by `g ↦ left-regular g`,
realising `G` concretely as the subgroup of permutations of the form `x ↦ g * x`. -/
theorem cayleyEquivRange_apply (g : G) :
    (cayleyEquivRange G g : Equiv.Perm G) = leftRegular G g :=
  MonoidHom.ofInjective_apply (leftRegular_injective G)

end CayleysTheoremOQ01
