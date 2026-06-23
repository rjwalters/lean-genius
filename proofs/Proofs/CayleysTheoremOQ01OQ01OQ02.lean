/-
Proof: The image of the finite Cayley embedding is a regular (sharply
transitive) subgroup of Sₙ.
Research: cayleys-theorem-oq-01-oq-01-oq-02

Open question (from `cayleys-theorem-oq-01-oq-01`):
  Show the image of `cayleyFinHom` is a *regular* (sharply transitive)
  subgroup of `Sₙ` — a subgroup of order `n` acting freely and transitively
  on the `n` points.

The parent entry builds, for a relabelling `e : G ≃ Fin n`, the finite Cayley
homomorphism `cayleyFinHom e : G →* Equiv.Perm (Fin n)` with
`cayleyFinHom e g i = e (g * e.symm i)`, and proves it injective.  Here we study
its *image* `H := (cayleyFinHom e).range` as a permutation group acting on the
`n` points `Fin n`, and prove the three classical facts characterising a regular
permutation group:

* **Transitive.** For all `i j`, some `σ ∈ H` maps `i ↦ j`
  (take `g = e.symm j * (e.symm i)⁻¹`).
* **Free / semiregular.** Any `σ ∈ H` fixing even a single point is the
  identity (the point stabilisers are trivial).
* **Sharply transitive (simply transitive).** Combining the two: for all `i j`
  there is a *unique* `σ ∈ H` with `σ i = j`.

We also record that `H` has order `n` and package transitivity as a
`MulAction.IsPretransitive` instance for the natural action of `H` on `Fin n`.
A finite permutation group that is both transitive and free is exactly a regular
representation, so these results identify `H` as the regular permutation group
of degree `n` — the concrete content of "Cayley's theorem realises `G` as a
regular subgroup of `Sₙ`".
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Proofs.CayleysTheoremOQ01OQ01

namespace CayleyFinRegular

open Equiv CayleyFin

variable {G : Type*} [Group G] {n : ℕ} (e : G ≃ Fin n)

/-- The regular permutation group: the image of the finite Cayley homomorphism,
viewed as a subgroup of `Sₙ = Equiv.Perm (Fin n)`. -/
abbrev regSubgroup : Subgroup (Equiv.Perm (Fin n)) := (cayleyFinHom e).range

/-- Membership in the regular subgroup is witnessed by a group element. -/
theorem mem_regSubgroup {σ : Equiv.Perm (Fin n)} :
    σ ∈ regSubgroup e ↔ ∃ g : G, cayleyFinHom e g = σ :=
  MonoidHom.mem_range

/-- The Cayley permutation `cayleyFinHom e g` sends `i ↦ e (g * e.symm i)`.
At the relabelled point `e x` it is simply left multiplication: `e x ↦ e (g*x)`. -/
theorem cayleyFinHom_apply_relabel (g x : G) :
    cayleyFinHom e g (e x) = e (g * x) := by
  rw [cayleyFinHom_apply, Equiv.symm_apply_apply]

/-! ### Transitivity -/

/-- **Transitivity.** For any two points `i j : Fin n`, some element of the
regular subgroup carries `i` to `j`.  The witness is the Cayley image of
`g = e.symm j * (e.symm i)⁻¹`. -/
theorem regSubgroup_transitive (i j : Fin n) :
    ∃ σ ∈ regSubgroup e, σ i = j := by
  refine ⟨cayleyFinHom e (e.symm j * (e.symm i)⁻¹), MonoidHom.mem_range.mpr ⟨_, rfl⟩, ?_⟩
  rw [cayleyFinHom_apply, inv_mul_cancel_right, Equiv.apply_symm_apply]

/-! ### Freeness (semiregularity) -/

/-- **Freeness.** Any element of the regular subgroup that fixes even a single
point of `Fin n` is the identity permutation.  Equivalently every point
stabiliser is trivial, so the action is free (semiregular). -/
theorem regSubgroup_free {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ regSubgroup e)
    {i : Fin n} (hfix : σ i = i) : σ = 1 := by
  obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hσ
  -- `cayleyFinHom e g i = i` forces `g = 1`, hence the permutation is identity.
  have hgx : g * e.symm i = e.symm i := by
    apply e.injective
    rw [Equiv.apply_symm_apply, ← cayleyFinHom_apply]
    exact hfix
  have hg : g = 1 := by
    have := congrArg (· * (e.symm i)⁻¹) hgx
    simpa [mul_inv_cancel_right] using this
  rw [hg, map_one]

/-- An element of the regular subgroup is determined by its value at any single
point: two members agreeing at one point are equal. -/
theorem regSubgroup_eq_of_apply_eq {σ τ : Equiv.Perm (Fin n)}
    (hσ : σ ∈ regSubgroup e) (hτ : τ ∈ regSubgroup e) {i : Fin n}
    (h : σ i = τ i) : σ = τ := by
  have hmem : τ⁻¹ * σ ∈ regSubgroup e := mul_mem (inv_mem hτ) hσ
  have hfix : (τ⁻¹ * σ) i = i := by
    rw [Equiv.Perm.mul_apply, h, ← Equiv.Perm.mul_apply, inv_mul_cancel,
      Equiv.Perm.one_apply]
  -- `τ⁻¹ * σ = 1` gives `σ = τ`.
  have hone : τ⁻¹ * σ = 1 := regSubgroup_free e hmem hfix
  exact (inv_mul_eq_one.mp hone).symm

/-! ### Sharp transitivity -/

/-- **Sharp (simple) transitivity.** For any two points `i j : Fin n` there is a
*unique* element of the regular subgroup carrying `i` to `j`.  This is the
defining property of a regular permutation group. -/
theorem regSubgroup_sharplyTransitive (i j : Fin n) :
    ∃! σ : Equiv.Perm (Fin n), σ ∈ regSubgroup e ∧ σ i = j := by
  obtain ⟨σ, hσmem, hσij⟩ := regSubgroup_transitive e i j
  refine ⟨σ, ⟨hσmem, hσij⟩, ?_⟩
  rintro τ ⟨hτmem, hτij⟩
  exact regSubgroup_eq_of_apply_eq e hτmem hσmem (by rw [hτij, hσij])

/-! ### Order of the regular subgroup -/

/-- **Order.** The regular subgroup has exactly `n` elements: it is the
isomorphic image of `G`, and `e : G ≃ Fin n` makes `G` an `n`-element group. -/
theorem regSubgroup_card : Nat.card (regSubgroup e) = n := by
  have h1 : Nat.card (regSubgroup e) = Nat.card G :=
    Nat.card_congr (cayleyFinRangeEquiv e).toEquiv.symm
  rw [h1, Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### Action packaging -/

/-- The natural action of the regular subgroup on the `n` points is transitive,
recorded as a `MulAction.IsPretransitive` instance. -/
instance regSubgroup_isPretransitive :
    MulAction.IsPretransitive (regSubgroup e) (Fin n) := by
  refine ⟨fun i j => ?_⟩
  obtain ⟨σ, hσmem, hσij⟩ := regSubgroup_transitive e i j
  exact ⟨⟨σ, hσmem⟩, hσij⟩

/-- The action of the regular subgroup on `Fin n` is free: a group element
fixing a point is the identity of the subgroup. -/
theorem regSubgroup_smul_free (σ : regSubgroup e) (i : Fin n)
    (h : σ • i = i) : σ = 1 := by
  have h' : (σ : Equiv.Perm (Fin n)) i = i := h
  have : (σ : Equiv.Perm (Fin n)) = 1 := regSubgroup_free e σ.2 h'
  exact Subtype.ext this

/-! ### Conclusion -/

/-- **Cayley's theorem, regular form.** For a relabelling `e : G ≃ Fin n`, the
image of the finite Cayley homomorphism is a subgroup of `Sₙ` of order `n` that
acts freely and transitively on the `n` points — a regular (sharply transitive)
permutation group of degree `n`. -/
theorem cayley_regular_subgroup :
    Nat.card (regSubgroup e) = n ∧
    (∀ i j : Fin n, ∃! σ : Equiv.Perm (Fin n), σ ∈ regSubgroup e ∧ σ i = j) := by
  exact ⟨regSubgroup_card e, regSubgroup_sharplyTransitive e⟩

/-- Concrete instance: the left-regular image of the cyclic group of order `3`
is a regular subgroup of `S₃` of order `3`. -/
example :
    Nat.card (regSubgroup (Fintype.equivFin (Multiplicative (ZMod 3)))) = 3 := by
  rw [regSubgroup_card]
  simp

end CayleyFinRegular
