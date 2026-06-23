/-
Proof: Converse to Cayley — a free transitive subgroup of `Sₙ` is regular of order `n`.
Research: cayleys-theorem-oq-01-oq-01-oq-02-oq-01

Open question (from `cayleys-theorem-oq-01-oq-01-oq-02`):
  The parent shows the *image* of the finite Cayley embedding is a regular
  (sharply transitive) subgroup of `Sₙ`.  Here we prove the *converse*: ANY
  subgroup `H ≤ Sₙ = Equiv.Perm α` (with `α` a finite nonempty type) that acts
  **freely** and **transitively** on the `n` points is regular of order `n`.

`regular` permutation group means: transitive + free (only the identity fixes a
point).  We prove the two structural payoffs that pin such an `H` down as the
regular representation of degree `n`:

* **Order `n`.**  `Nat.card H = Fintype.card α`.  The orbit map
  `σ ↦ σ • a` from `H` to `α` is a bijection: surjective by transitivity, and
  injective by freeness (an element is determined by its value at one point).
* **Sharp (simple) transitivity.**  For all `i j` there is a *unique* `σ ∈ H`
  with `σ i = j`.

Together these say `H` is sharply transitive of order `n` — exactly a regular
permutation group of degree `n`.  Combined with the parent (Cayley images are
regular), this closes the loop: the regular subgroups of `Sₙ` are precisely the
free transitive ones, and they all have order `n`.

The argument is entirely elementary — orbit-stabiliser specialised to a free
action, repackaged as a single explicit bijection `H ≃ α`.  No deep Mathlib
machinery and, in particular, no dependence on the parent's Cayley construction:
the statement is about an arbitrary subgroup.
-/

import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

namespace CayleyConverse

open Equiv

variable {α : Type*} (H : Subgroup (Equiv.Perm α))

/-- `H ≤ Sym(α)` acts **transitively** when some element of `H` carries any point
to any other. -/
def ActsTransitively : Prop := ∀ i j : α, ∃ σ ∈ H, σ i = j

/-- `H ≤ Sym(α)` acts **freely** (is *semiregular*) when only the identity fixes
a point. -/
def ActsFreely : Prop := ∀ σ ∈ H, ∀ i : α, σ i = i → σ = 1

/-- A **regular** permutation group: transitive and free. -/
def IsRegular : Prop := ActsTransitively H ∧ ActsFreely H

variable {H}

/-- **Rigidity from freeness.**  Two elements of a free subgroup that agree at a
single point are equal.  This is the converse engine: an element of a free
permutation group is determined by its value at one point. -/
theorem eq_of_free_of_eq_at_point (hfree : ActsFreely H)
    {σ τ : Equiv.Perm α} (hσ : σ ∈ H) (hτ : τ ∈ H) {i : α} (h : σ i = τ i) :
    σ = τ := by
  have hmem : τ⁻¹ * σ ∈ H := H.mul_mem (H.inv_mem hτ) hσ
  have hfix : (τ⁻¹ * σ) i = i := by
    rw [Equiv.Perm.mul_apply, h]
    exact Equiv.symm_apply_apply τ i
  have hone : τ⁻¹ * σ = 1 := hfree _ hmem i hfix
  exact (inv_mul_eq_one.mp hone).symm

/-- **The orbit map is a bijection.**  For a free transitive subgroup and a
basepoint `a`, the map `σ ↦ σ a` from `H` to `α` is bijective. -/
theorem orbitMap_bijective (htrans : ActsTransitively H) (hfree : ActsFreely H)
    (a : α) : Function.Bijective (fun σ : H => (σ : Equiv.Perm α) a) := by
  constructor
  · rintro σ τ h
    exact Subtype.ext (eq_of_free_of_eq_at_point hfree σ.2 τ.2 h)
  · intro j
    obtain ⟨σ, hσ, hσa⟩ := htrans a j
    exact ⟨⟨σ, hσ⟩, hσa⟩

/-- **The regular equivalence `H ≃ α`.**  A free transitive subgroup is in
bijection with the set it acts on, via the orbit map at any basepoint. -/
noncomputable def regularEquiv (htrans : ActsTransitively H) (hfree : ActsFreely H)
    (a : α) : H ≃ α :=
  Equiv.ofBijective _ (orbitMap_bijective htrans hfree a)

/-- **Order `n`.**  A free transitive subgroup of `Sym(α)` has order `|α|`.
This is the converse to Cayley: order equals degree. -/
theorem card_eq_of_free_transitive [Nonempty α] (htrans : ActsTransitively H)
    (hfree : ActsFreely H) : Nat.card H = Nat.card α :=
  Nat.card_congr (regularEquiv htrans hfree (Classical.arbitrary α))

/-- **Order `n`, finite restatement.**  With `α` a finite nonempty type of size
`n`, a free transitive subgroup has `Fintype.card H = n`. -/
theorem fintypeCard_eq_of_free_transitive [Fintype α] [Nonempty α]
    (htrans : ActsTransitively H) (hfree : ActsFreely H) :
    Nat.card H = Fintype.card α := by
  rw [card_eq_of_free_transitive htrans hfree, Nat.card_eq_fintype_card]

/-- **Sharp (simple) transitivity.**  For a free transitive subgroup and any two
points `i j`, there is a *unique* `σ ∈ H` with `σ i = j`.  This is the defining
property of a regular permutation group. -/
theorem existsUnique_of_free_transitive (htrans : ActsTransitively H)
    (hfree : ActsFreely H) (i j : α) :
    ∃! σ : H, (σ : Equiv.Perm α) i = j := by
  obtain ⟨σ, hσ, hσij⟩ := htrans i j
  refine ⟨⟨σ, hσ⟩, hσij, ?_⟩
  rintro ⟨τ, hτ⟩ hτij
  exact Subtype.ext (eq_of_free_of_eq_at_point hfree hτ hσ (hτij.trans hσij.symm))

/-- **Converse to Cayley, packaged.**  A regular (free transitive) subgroup of
`Sym(α)` over a finite nonempty `α` has order `n = |α|` and is sharply
transitive — i.e. it is the regular permutation group of degree `n`. -/
theorem regular_iff_card_and_sharp [Fintype α] [Nonempty α] (hreg : IsRegular H) :
    Nat.card H = Fintype.card α ∧
      ∀ i j : α, ∃! σ : H, (σ : Equiv.Perm α) i = j :=
  ⟨fintypeCard_eq_of_free_transitive hreg.1 hreg.2,
    fun i j => existsUnique_of_free_transitive hreg.1 hreg.2 i j⟩

end CayleyConverse
