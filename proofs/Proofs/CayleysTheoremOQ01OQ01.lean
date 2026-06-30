/-
Proof: Finite Cayley's theorem — a group of order n embeds in Sₙ
Research: cayleys-theorem-oq-01-oq-01

Open question (from `cayleys-theorem-oq-01`): refine the abstract embedding
`G ↪ Sym(G)` into the classical *finite* form `G ↪ Sₙ` for a group `G` of
order `n`, by transporting the left-regular representation along a bijection
`G ≃ Fin n`.

Method: conjugate the regular representation `MulAction.toPermHom G G : G →*
Equiv.Perm G` by a relabelling `e : G ≃ Fin n`.  Conjugation by a fixed
bijection is a multiplicative isomorphism `Equiv.Perm G ≃* Equiv.Perm (Fin n)`,
so the composite is again an injective group homomorphism — now landing in the
concrete symmetric group `Sₙ = Equiv.Perm (Fin n)`.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic

/-
# Finite Cayley's theorem: `G` of order `n` embeds in `Sₙ`

The parent entry proves the abstract Cayley theorem: the left-regular
representation `λ : G →* Equiv.Perm G`, `λ(g) = (x ↦ g * x)`, is an injective
group homomorphism, so every group embeds into the symmetric group on its own
underlying set.

For a *finite* group of order `n`, the classical statement instead realises `G`
inside the standard symmetric group `Sₙ = Equiv.Perm (Fin n)`.  The two differ
only by a relabelling of the points being permuted: any bijection
`e : G ≃ Fin n` induces, by conjugation `σ ↦ e ∘ σ ∘ e⁻¹`, a multiplicative
isomorphism `Equiv.Perm G ≃* Equiv.Perm (Fin n)`.  Composing the regular
representation with this relabelling gives the finite Cayley embedding.
-/

namespace CayleyFin

open Equiv

variable {G : Type*} [Group G]

/-- Conjugation by a fixed bijection `e : α ≃ β`, packaged as a multiplicative
isomorphism `Equiv.Perm α ≃* Equiv.Perm β`.  On elements it is
`σ ↦ e ∘ σ ∘ e⁻¹`, the relabelling of permutations along `e`. -/
def permCongrMulEquiv {α β : Type*} (e : α ≃ β) : Equiv.Perm α ≃* Equiv.Perm β where
  toEquiv := Equiv.permCongr e
  map_mul' x y := by
    ext b
    simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply]

@[simp] theorem permCongrMulEquiv_apply {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α)
    (a : β) : permCongrMulEquiv e σ a = e (σ (e.symm a)) := rfl

/-- The finite Cayley homomorphism induced by a relabelling `e : G ≃ Fin n`:
conjugate the left-regular representation of `G` into `Sₙ = Equiv.Perm (Fin n)`. -/
def cayleyFinHom {n : ℕ} (e : G ≃ Fin n) : G →* Equiv.Perm (Fin n) :=
  (permCongrMulEquiv e).toMonoidHom.comp (MulAction.toPermHom G G)

theorem cayleyFinHom_apply {n : ℕ} (e : G ≃ Fin n) (g : G) (i : Fin n) :
    cayleyFinHom e g i = e (g * e.symm i) := rfl

/-- The finite Cayley homomorphism is injective: it is the composite of the
(injective) regular representation with a (bijective) relabelling. -/
theorem cayleyFinHom_injective {n : ℕ} (e : G ≃ Fin n) :
    Function.Injective (cayleyFinHom e) := by
  have hreg : Function.Injective (MulAction.toPermHom G G) :=
    MulAction.toPerm_injective
  have hcongr : Function.Injective (permCongrMulEquiv e) := (permCongrMulEquiv e).injective
  intro a b hab
  exact hreg (hcongr (by simpa [cayleyFinHom] using hab))

/-- **Finite Cayley's theorem.** Every finite group `G` of order `n` admits an
injective group homomorphism into the standard symmetric group
`Sₙ = Equiv.Perm (Fin n)`. -/
theorem cayley_fin (G : Type*) [Group G] [Fintype G] :
    ∃ f : G →* Equiv.Perm (Fin (Fintype.card G)), Function.Injective f :=
  ⟨cayleyFinHom (Fintype.equivFin G), cayleyFinHom_injective _⟩

/-- The finite Cayley embedding packaged as a bundled embedding `G ↪ Sₙ`. -/
noncomputable def cayleyFinEmbedding (G : Type*) [Group G] [Fintype G] :
    G ↪ Equiv.Perm (Fin (Fintype.card G)) :=
  ⟨cayleyFinHom (Fintype.equivFin G), cayleyFinHom_injective _⟩

/-- `G` is isomorphic to its image inside `Sₙ`: the finite form of "every group
is isomorphic to a subgroup of a symmetric group". -/
noncomputable def cayleyFinRangeEquiv {n : ℕ} (e : G ≃ Fin n) :
    G ≃* (cayleyFinHom e).range :=
  MonoidHom.ofInjective (cayleyFinHom_injective e)

/-- Sanity check: the embedding really lands in the symmetric group on `n`
points, with `n` the order of the group. -/
example (G : Type*) [Group G] [Fintype G] :
    ∃ f : G →* Equiv.Perm (Fin (Fintype.card G)), Function.Injective f :=
  cayley_fin G

/-- Concrete instance: the cyclic group of order 3 (`Multiplicative (ZMod 3)`)
embeds in `S₃ = Equiv.Perm (Fin 3)`. -/
example : ∃ f : Multiplicative (ZMod 3) →*
    Equiv.Perm (Fin (Fintype.card (Multiplicative (ZMod 3)))), Function.Injective f :=
  cayley_fin (Multiplicative (ZMod 3))

end CayleyFin
