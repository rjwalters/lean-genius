/-
Proof: Cayley, bundled — the left-regular representation as a single homomorphism
`regularRepHom G : G →* Perm G`, its faithfulness, and the canonical isomorphism
`regularRep G : G ≃* (regularRepHom G).range`.
Research: cayleys-theorem-oq-01-oq-01-oq-02-oq-01-oq-02-oq-01-oq-01

Open question (from `cayleys-theorem-oq-01-oq-01-oq-02-oq-01-oq-02-oq-01`, first
listed): the parent records the **explicit regular representation** of a free
transitive `H ≤ Sym(α)` *element by element* — transporting the geometric action
of each `σ ∈ H` across the orbit bijection `e : H ≃ α` yields exactly
`Equiv.mulLeft σ` on `H` (`transportedAction_eq_mulLeft`), and that assignment is
injective (`mulLeft_injective`).  But this is a *family* of `Equiv.Perm`'s, not a
single morphism.  Here we bundle them.

What this file adds, relative to the parent's pointwise family:

* **`regularRepHom G : G →* Perm G`** — for an *arbitrary* group `G`, the
  left-regular representation `σ ↦ Equiv.mulLeft σ` packaged as a monoid
  homomorphism (multiplicativity is `Equiv.mulLeft (a*b) = Equiv.mulLeft a *
  Equiv.mulLeft b`, the unit law `Equiv.mulLeft 1 = 1`).  This is the single
  morphism underlying the parent's element-wise translations.

* **`regularRepHom_injective`** — faithfulness of the regular representation,
  i.e. **Cayley's theorem**: distinct group elements give distinct left
  translations, recovered by evaluating two equal translations at `1`.

* **`regularRep G : G ≃* (regularRepHom G).range`** — *the* bundled Cayley
  isomorphism, realising `G` as a concrete subgroup of `Sym(G)` via
  `MulEquiv.ofInjective`; `regularRep_coe_apply` records that its underlying
  permutation is `Equiv.mulLeft σ`.

* **`cayley`** — the packaged classical statement that every group is isomorphic
  to a subgroup of its own symmetric group: `∃ K ≤ Sym(G), Nonempty (G ≃* K)`.

* A closing section ties the bundle back to the parent's geometric setting: for a
  free transitive `H ≤ Sym(α)`, transporting the geometric action across the orbit
  bijection is, hom-for-hom, `regularRepHom H σ`
  (`transportedAction_eq_regularRepHom`), and `isBundledRegularRepresentation`
  upgrades the parent's `isExplicitRegularRepresentation` from a pair of pointwise
  identities to a single group isomorphism `φ : H ≃* (regularRepHom H).range` with
  `(φ σ : Perm H) = e.symm.permCongr (σ : Perm α)`.

No finiteness is used anywhere: this is the sharp form of Cayley, valid for an
arbitrary (possibly infinite) group `G`.  Mathlib supplies the unbundled
ingredients (`Equiv.mulLeft` and its arithmetic, `MulEquiv.ofInjective`); the
contribution is the assembled homomorphism, the range isomorphism, and their
identification with the parent's geometric regular representation.
-/

import Proofs.CayleysTheoremOQ01OQ01OQ02OQ01OQ02OQ01
import Mathlib.Algebra.Group.Subgroup.Ker

namespace CayleyConverse

open Equiv

/-! ## The bundled left-regular representation of an arbitrary group -/

/-- **The left-regular representation, bundled.**  For any group `G`, the map
`σ ↦ Equiv.mulLeft σ` (left translation `x ↦ σ * x`) is a monoid homomorphism
`G →* Perm G`.  This is the single morphism underlying the parent's element-wise
family of translations. -/
def regularRepHom (G : Type*) [Group G] : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

@[simp] theorem regularRepHom_apply {G : Type*} [Group G] (σ : G) :
    regularRepHom G σ = Equiv.mulLeft σ := rfl

/-- **Faithfulness of the regular representation = Cayley's theorem.**  The
left-regular representation `regularRepHom G` is injective: two elements with the
same left-translation are equal, seen by evaluating the translations at `1`. -/
theorem regularRepHom_injective (G : Type*) [Group G] :
    Function.Injective (regularRepHom G) := by
  intro σ τ h
  have := congrArg (fun e : Equiv.Perm G => e 1) h
  simpa using this

/-- **The image of the regular representation** is exactly the set of left
translations `{ Equiv.mulLeft g : g ∈ G }`. -/
theorem mem_regularRepHom_range {G : Type*} [Group G] (τ : Equiv.Perm G) :
    τ ∈ (regularRepHom G).range ↔ ∃ g : G, Equiv.mulLeft g = τ := by
  simp only [MonoidHom.mem_range, regularRepHom_apply]

/-- **The bundled Cayley isomorphism.**  An arbitrary group `G` is isomorphic to
the range of its regular representation — a concrete subgroup of `Sym(G)` — via
`MulEquiv.ofInjective` applied to the faithful homomorphism `regularRepHom G`. -/
noncomputable def regularRep (G : Type*) [Group G] :
    G ≃* (regularRepHom G).range :=
  MonoidHom.ofInjective (regularRepHom_injective G)

/-- The underlying permutation of `regularRep G σ` is the left translation
`Equiv.mulLeft σ`. -/
@[simp] theorem regularRep_coe_apply {G : Type*} [Group G] (σ : G) :
    ((regularRep G σ : (regularRepHom G).range) : Equiv.Perm G) = Equiv.mulLeft σ :=
  MonoidHom.ofInjective_apply (regularRepHom_injective G)

/-- **Cayley's theorem, packaged.**  Every group is isomorphic to a subgroup of
its own symmetric group. -/
theorem cayley (G : Type*) [Group G] :
    ∃ K : Subgroup (Equiv.Perm G), Nonempty (G ≃* K) :=
  ⟨(regularRepHom G).range, ⟨regularRep G⟩⟩

/-! ## Back to the geometric setting: the transported action is `regularRepHom H`

The parent transports the geometric action of a free transitive `H ≤ Sym(α)`
across the orbit bijection `e : H ≃ α`, obtaining `Equiv.mulLeft σ` element by
element.  We now identify that family with the single homomorphism `regularRepHom H`
and assemble the parent's `isExplicitRegularRepresentation` into one group
isomorphism. -/

variable {α : Type*} {H : Subgroup (Equiv.Perm α)}

/-- **The transported geometric action is `regularRepHom H`, hom-for-hom.**  For a
free transitive `H ≤ Sym(α)`, transporting the geometric action of `σ ∈ H` across
the orbit bijection equals `regularRepHom H σ`.  This identifies the parent's
element-wise transport with the bundled homomorphism. -/
theorem transportedAction_eq_regularRepHom (htrans : ActsTransitively H)
    (hfree : ActsFreely H) (a : α) (σ : H) :
    (regularEquiv htrans hfree a).symm.permCongr (σ : Equiv.Perm α)
      = regularRepHom H σ := by
  rw [regularRepHom_apply, transportedAction_eq_mulLeft]

/-- **The explicit regular representation, bundled as a group isomorphism.**  For
arbitrary nonempty `α`, a free transitive `H ≤ Sym(α)` admits an orbit bijection
`e : H ≃ α` together with the Cayley isomorphism `φ : H ≃* (regularRepHom H).range`
such that, for every `σ ∈ H`, the underlying permutation `φ σ : Perm H` is exactly
the transport `e.symm.permCongr (σ : Perm α)` of the geometric action.

This upgrades the parent's `isExplicitRegularRepresentation` from a pair of
pointwise identities to a single morphism: the free transitive action of `H` on
`α` is isomorphic, *as a bundled group action*, to the left-regular action of `H`
on itself.  No finiteness is used. -/
theorem isBundledRegularRepresentation [Nonempty α]
    (htrans : ActsTransitively H) (hfree : ActsFreely H) :
    ∃ (e : H ≃ α) (φ : H ≃* (regularRepHom H).range),
      ∀ σ : H, ((φ σ : (regularRepHom H).range) : Equiv.Perm H)
        = e.symm.permCongr (σ : Equiv.Perm α) := by
  refine ⟨regularEquiv htrans hfree (Classical.arbitrary α), regularRep H, fun σ => ?_⟩
  rw [regularRep_coe_apply, transportedAction_eq_mulLeft]

end CayleyConverse
