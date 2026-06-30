/-
Proof: Explicit regular representation in the infinite setting — a free transitive
`H ≤ Sym(α)` is permutation-isomorphic to the left-regular action of `H` on itself,
together with a clean algebraic sufficient condition (abelian) for the hypotheses.
Research: cayleys-theorem-oq-01-oq-01-oq-02-oq-01-oq-02-oq-01

Open question (from `cayleys-theorem-oq-01-oq-01-oq-02-oq-01-oq-02`):
  The parent proves the genuine *infinite* converse to Cayley — a free transitive
  `H ≤ Sym(α)` satisfies `#H = #α` for arbitrary nonempty `α`, via the orbit
  bijection `regularEquiv : H ≃ α`.  But cardinality is only a *counting*
  invariant: it does not, by itself, pin down *which* representation `H` is.
  Here we record the structural heart — the **explicit regular representation** —
  and add a checkable *sufficient condition* for the (subtle) freeness hypothesis.

The orbit bijection is not merely a bijection of sets: it is **equivariant**.
With basepoint `a`, the map `e := regularEquiv : H ≃ α`, `e τ = τ • a`, intertwines
left multiplication on `H` with the tautological action of `H` on `α`:

  `e (σ * τ) = σ • (e τ)`     for all `σ τ ∈ H`.

Consequently, transporting the geometric action of any `σ ∈ H` (a permutation of
`α`) across `e` yields *exactly* left multiplication by `σ` on `H`:

  `e.symm.permCongr (σ : Perm α) = Equiv.mulLeft σ`.

In words: **up to the relabelling `e`, the free transitive action of `H` on `α`
is literally the left-regular action of `H` on itself.**  This is the converse to
Cayley in its sharpest form — Cayley embeds an abstract group into a permutation
group as its regular representation; here we recover, from a purely geometric
free transitive action, that the action *is* that regular representation.  None of
this needs finiteness, so it holds verbatim in the infinite setting.

The whole chain assumes the action is **free and transitive**.  Transitivity is
easy to exhibit, but freeness is the subtle hypothesis.  The final section records
a clean, purely algebraic *sufficient* condition: **an abelian transitive subgroup
acts freely**, hence is regular and carries the explicit regular representation
above.  This is the classical fact that a transitive *abelian* permutation group is
sharply transitive (regular); the proof is a three-line commutation argument and
needs no finiteness.

What is genuinely new relative to the ancestors:
* grandparent (`…-oq-02-oq-01`): the orbit map is a *bijection* `H ≃ α` (sets);
* parent (`…-oq-02-oq-01-oq-02`): that bijection transports *cardinality* (`#H = #α`);
* here: that bijection transports the *group action* — it is an **isomorphism of
  `H`-actions** carrying the geometric action onto the regular representation —
  plus the sufficient condition `abelian + transitive ⟹ regular`.

We reuse the ancestors' `regularEquiv` and predicates, so no construction is
duplicated.
-/

import Proofs.CayleysTheoremOQ01OQ01OQ02OQ01OQ02
import Mathlib.Algebra.Group.Units.Equiv

namespace CayleyConverse

open Equiv

variable {α : Type*} {H : Subgroup (Equiv.Perm α)}

/-- **Orbit map, unfolded.**  The regular equivalence sends `τ` to its value at the
basepoint: `e τ = τ • a`.  Definitional, but recorded so the equivariance proof
reads cleanly. -/
theorem regularEquiv_apply (htrans : ActsTransitively H) (hfree : ActsFreely H)
    (a : α) (τ : H) : regularEquiv htrans hfree a τ = (τ : Equiv.Perm α) a := rfl

/-- **Equivariance of the orbit map.**  The orbit bijection `e : H ≃ α` intertwines
left multiplication on `H` with the tautological `H`-action on `α`:
`e (σ * τ) = σ • (e τ)`.  This is the structural content that upgrades the parent's
bare set bijection to an isomorphism of `H`-actions, and it holds for any basepoint
`a` and arbitrary `α` (no finiteness, no freeness/transitivity beyond what builds
`e`). -/
theorem regularEquiv_equivariant (htrans : ActsTransitively H) (hfree : ActsFreely H)
    (a : α) (σ τ : H) :
    (σ : Equiv.Perm α) (regularEquiv htrans hfree a τ)
      = regularEquiv htrans hfree a (σ * τ) := by
  simp only [regularEquiv_apply, Subgroup.coe_mul, Equiv.Perm.mul_apply]

/-- **Explicit regular representation.**  Transporting the geometric action of
`σ ∈ H` (a permutation of `α`) across the orbit bijection `e : H ≃ α` produces
*exactly* left multiplication by `σ` on `H`:
`e.symm.permCongr (σ : Perm α) = Equiv.mulLeft σ`.

This is the precise sense in which a free transitive `H ≤ Sym(α)` "is" the
left-regular representation of `H`: relabel `α` by `e` and every group element acts
by translation.  The proof is the equivariance identity followed by cancelling
`e.symm ∘ e`. -/
theorem transportedAction_eq_mulLeft (htrans : ActsTransitively H) (hfree : ActsFreely H)
    (a : α) (σ : H) :
    (regularEquiv htrans hfree a).symm.permCongr (σ : Equiv.Perm α)
      = Equiv.mulLeft σ := by
  ext τ
  simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.coe_mulLeft]
  rw [regularEquiv_equivariant, Equiv.symm_apply_apply]

/-- **Faithfulness of the regular representation.**  The left-regular assignment
`σ ↦ Equiv.mulLeft σ` is injective, so the transported action above is a *faithful*
copy of `H` inside `Sym(H)` — this is Cayley's theorem for `H` itself, recovered
from the geometric action. -/
theorem mulLeft_injective :
    Function.Injective (fun σ : H => Equiv.mulLeft σ) := by
  intro σ τ h
  have := congrArg (fun e : Equiv.Perm H => e 1) h
  simpa using this

/-- **Explicit regular representation, packaged.**  For arbitrary nonempty `α`, a
free transitive `H ≤ Sym(α)` admits an equivariant bijection `e : H ≃ α` that
carries left multiplication on `H` to the geometric action on `α`, and under which
each `σ ∈ H` acts as `Equiv.mulLeft σ`.  Equivalently: the free transitive action
of `H` on `α` is isomorphic, as an `H`-action, to the left-regular action of `H` on
itself — the sharp converse to Cayley, valid in the infinite setting. -/
theorem isExplicitRegularRepresentation [Nonempty α]
    (htrans : ActsTransitively H) (hfree : ActsFreely H) :
    ∃ e : H ≃ α,
      (∀ σ τ : H, (σ : Equiv.Perm α) (e τ) = e (σ * τ)) ∧
        (∀ σ : H, e.symm.permCongr (σ : Equiv.Perm α) = Equiv.mulLeft σ) :=
  ⟨regularEquiv htrans hfree (Classical.arbitrary α),
    fun σ τ => regularEquiv_equivariant htrans hfree _ σ τ,
    fun σ => transportedAction_eq_mulLeft htrans hfree _ σ⟩

/-! ## A checkable sufficient condition: abelian transitive actions are free

Everything above assumes the action is free and transitive.  Transitivity is easy
to exhibit; freeness is the subtle one.  We record a clean, purely algebraic
*sufficient* condition for freeness — commutativity — which is trivial to check
and turns the whole regular-representation machinery into an unconditional
statement about *abelian* transitive subgroups. -/

/-- **Abelian + transitive ⟹ free.**  If `H ≤ Sym(α)` acts transitively and its
elements pairwise commute, then the action is free: any `σ ∈ H` fixing a point is
the identity.

Proof: suppose `σ a = a`, and let `b` be arbitrary.  By transitivity pick `τ ∈ H`
with `τ a = b`.  Then, using `σ τ = τ σ`,
`σ b = σ (τ a) = (σ τ) a = (τ σ) a = τ (σ a) = τ a = b`,
so `σ` fixes every point and hence `σ = 1`. -/
theorem actsFreely_of_abelian_transitive
    (htrans : ActsTransitively H)
    (hcomm : ∀ σ ∈ H, ∀ τ ∈ H, σ * τ = τ * σ) :
    ActsFreely H := by
  intro σ hσ a hfix
  ext b
  obtain ⟨τ, hτ, hτa⟩ := htrans a b
  have hb : (σ : Equiv.Perm α) b = b :=
    calc (σ : Equiv.Perm α) b
        = σ (τ a) := by rw [hτa]
      _ = (σ * τ) a := (Equiv.Perm.mul_apply σ τ a).symm
      _ = (τ * σ) a := by rw [hcomm σ hσ τ hτ]
      _ = τ (σ a) := Equiv.Perm.mul_apply τ σ a
      _ = τ a := by rw [hfix]
      _ = b := hτa
  simpa using hb

/-- **Abelian transitive subgroups are regular.**  Immediate from
`actsFreely_of_abelian_transitive`: transitivity is assumed and freeness is
supplied by commutativity. -/
theorem isRegular_of_abelian_transitive
    (htrans : ActsTransitively H)
    (hcomm : ∀ σ ∈ H, ∀ τ ∈ H, σ * τ = τ * σ) :
    IsRegular H :=
  ⟨htrans, actsFreely_of_abelian_transitive htrans hcomm⟩

/-- **Abelian transitive ⟹ `#H = #α`.**  A transitive abelian subgroup of
`Sym(α)` over arbitrary nonempty `α` has the same cardinality as `α` — the converse
to Cayley applies, with freeness coming for free from commutativity. -/
theorem cardinalMk_eq_of_abelian_transitive [Nonempty α]
    (htrans : ActsTransitively H)
    (hcomm : ∀ σ ∈ H, ∀ τ ∈ H, σ * τ = τ * σ) :
    Cardinal.mk H = Cardinal.mk α :=
  cardinalMk_eq_of_free_transitive htrans (actsFreely_of_abelian_transitive htrans hcomm)

/-- **Abelian transitive ⟹ `Nat.card H = Fintype.card α`** for finite nonempty `α`.
The finite specialisation of `cardinalMk_eq_of_abelian_transitive`. -/
theorem natCard_eq_of_abelian_transitive [Fintype α] [Nonempty α]
    (htrans : ActsTransitively H)
    (hcomm : ∀ σ ∈ H, ∀ τ ∈ H, σ * τ = τ * σ) :
    Nat.card H = Fintype.card α :=
  natCard_eq_of_cardinalMk htrans (actsFreely_of_abelian_transitive htrans hcomm)

/-- **An abelian transitive subgroup carries the explicit regular representation.**
The capstone: combining `actsFreely_of_abelian_transitive` with
`isExplicitRegularRepresentation`, a transitive *abelian* `H ≤ Sym(α)` over
arbitrary nonempty `α` is — up to the orbit relabelling — the left-regular action
of `H` on itself.  No finiteness, no freeness assumption; commutativity alone
suffices. -/
theorem isExplicitRegularRepresentation_of_abelian_transitive [Nonempty α]
    (htrans : ActsTransitively H)
    (hcomm : ∀ σ ∈ H, ∀ τ ∈ H, σ * τ = τ * σ) :
    ∃ e : H ≃ α,
      (∀ σ τ : H, (σ : Equiv.Perm α) (e τ) = e (σ * τ)) ∧
        (∀ σ : H, e.symm.permCongr (σ : Equiv.Perm α) = Equiv.mulLeft σ) :=
  isExplicitRegularRepresentation htrans (actsFreely_of_abelian_transitive htrans hcomm)

/-- **`IsMulCommutative` form.**  Restatement of `actsFreely_of_abelian_transitive`
using Mathlib's `IsMulCommutative` typeclass on the subgroup: a transitive subgroup
that is commutative as a group acts freely. -/
theorem actsFreely_of_isMulCommutative_transitive [IsMulCommutative H]
    (htrans : ActsTransitively H) : ActsFreely H :=
  actsFreely_of_abelian_transitive htrans
    (fun _ hσ _ hτ => Subgroup.mul_comm_of_mem_isMulCommutative (H := H) hσ hτ)

end CayleyConverse
