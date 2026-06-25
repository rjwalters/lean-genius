import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
import Proofs.SchursLemma

/-!
# Irreducible representations of abelian groups are one-dimensional

## What This Proves

This is the foundational classification result of character theory: **over an
algebraically closed field, every finite-dimensional irreducible representation
of an abelian group is one-dimensional.**

The parent file (`SchursLemma.lean`) proves the *scalar form* of Schur's lemma:
every `A`-linear endomorphism of a finite-dimensional simple `A`-module over an
algebraically closed field is multiplication by a scalar. That statement controls
the endomorphisms that *commute* with the action. The new content here turns that
into a **dimension count** in the one situation where the algebra itself supplies
those commuting endomorphisms: when `A` is **commutative**.

The key observation is that for a commutative algebra `A`, *every* element `a : A`
acts as an `A`-linear endomorphism `m ↦ a • m` (this is exactly where
commutativity is used). Schur forces each such map to be a scalar, so the whole
algebra acts by scalars; a single nonzero vector then already spans an
`A`-submodule, and simplicity collapses the module to a line.

## Mathematical Statements

* `simple_module_over_commutative_finrank_eq_one` — the algebraic heart: a simple
  module over a **commutative** `k`-algebra `A`, finite-dimensional over an
  algebraically closed field `k`, has `Module.finrank k M = 1`.
* `irreducible_rep_abelian_group_finrank_eq_one` — specialization to a group
  representation: an irreducible `k[G]`-module for an abelian group `G` is
  one-dimensional over `k` (because the group algebra of an abelian group is
  commutative).
* `irreducible_complex_rep_abelian_one_dim` — the headline complex case (`k = ℂ`).

## Approach

Let `A` be a commutative `k`-algebra acting on a simple module `M` that is
finite-dimensional over an algebraically closed field `k`.

1. **Each scalar multiplication is `A`-linear.** Because `A` is commutative,
   `a • (b • m) = (a*b) • m = (b*a) • m = b • (a • m)`, so `LinearMap.lsmul A M a`
   is an `A`-linear endomorphism of `M`.
2. **Schur ⟹ scalars.** By the parent's `schur_endomorphism_scalar`, for each
   `a : A` there is `c : k` with `a • m = c • m` for all `m`.
3. **One vector spans an `A`-submodule.** Fix a nonzero `v` (exists by simplicity).
   The `k`-line `Submodule.span k {v}` is closed under the `A`-action: for
   `a : A`, `a • (t • v) = t • (a • v) = t • (c • v) ∈ span k {v}`. So it is the
   carrier of an `A`-submodule `N`.
4. **Simplicity ⟹ the line is everything.** `v ≠ 0` makes `N ≠ ⊥`, so `N = ⊤`,
   i.e. `Submodule.span k {v} = ⊤`. Hence
   `finrank k M = finrank k (span k {v}) = 1`. ∎

## References
* Serre, *Linear Representations of Finite Groups*, §3.1 (abelian groups).
* Fulton–Harris, *Representation Theory*, §1.3.
-/

open Module

namespace SchursLemmaOQ01OQ02

section Commutative

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {A : Type*} [CommRing A] [Algebra k A]
variable {M : Type*} [AddCommGroup M] [Module k M] [Module A M]
  [IsScalarTower k A M] [IsSimpleModule A M] [FiniteDimensional k M]

omit [IsAlgClosed k] [IsSimpleModule A M] [FiniteDimensional k M] in
/-- The `k`-action and the `A`-action on `M` commute: `a • (t • w) = t • (a • w)`.
This is the scalar-tower compatibility, routed through `algebraMap`. -/
private theorem smul_k_comm (a : A) (t : k) (w : M) : a • (t • w) = t • (a • w) := by
  rw [← algebraMap_smul A t w, ← algebraMap_smul A t (a • w), smul_smul, smul_smul,
    mul_comm]

/-- **Schur for commutative algebras (scalar action).** For every `a : A` there is a
scalar `c : k` with `a • m = c • m` for all `m`. The `A`-linearity of `m ↦ a • m`
is exactly where commutativity of `A` enters. -/
theorem exists_scalar_smul (a : A) : ∃ c : k, ∀ m : M, a • m = c • m := by
  -- `LinearMap.lsmul A M a : M →ₗ[A] M` is the (A-linear) multiplication by `a`.
  have h := SchursLemma.schur_endomorphism_scalar (k := k) (A := A) (M := M)
    (LinearMap.lsmul A M a)
  simpa using h

include A in
/-- **Irreducible ⟹ one-dimensional, algebraic core.** A simple module over a
commutative `k`-algebra `A`, finite-dimensional over an algebraically closed field
`k`, is one-dimensional over `k`. -/
theorem simple_module_over_commutative_finrank_eq_one :
    Module.finrank k M = 1 := by
  haveI : Nontrivial M := IsSimpleModule.nontrivial A M
  -- A nonzero vector to build the line from.
  obtain ⟨v, hvne⟩ := exists_ne (0 : M)
  -- The `k`-line through `v` is closed under the `A`-action; package it as a
  -- `Submodule A M` with carrier `Submodule.span k {v}`.
  set L : Submodule k M := Submodule.span k {v} with hL
  have hsmul_mem : ∀ (a : A) {x : M}, x ∈ L → a • x ∈ L := by
    intro a x hx
    rw [hL, Submodule.mem_span_singleton] at hx
    obtain ⟨t, rfl⟩ := hx
    obtain ⟨c, hc⟩ := exists_scalar_smul (k := k) (M := M) a
    rw [smul_k_comm, hc v]
    -- `t • (c • v) = (t * c) • v ∈ span k {v}`
    rw [smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  let N : Submodule A M :=
    { carrier := (L : Set M)
      add_mem' := fun hx hy => L.add_mem hx hy
      zero_mem' := L.zero_mem
      smul_mem' := fun a x hx => hsmul_mem a hx }
  have hvN : v ∈ N := Submodule.mem_span_singleton_self v
  -- Simplicity: `N` is `⊥` or `⊤`; it is nonzero, so it is `⊤`.
  have hNtop : N = ⊤ := by
    rcases eq_bot_or_eq_top N with hbot | htop
    · exact absurd (by simpa [hbot, Submodule.mem_bot] using hvN) hvne
    · exact htop
  -- Transfer to the `k`-line: `span k {v} = ⊤`.
  have hLtop : L = ⊤ := by
    refine Submodule.eq_top_iff'.2 fun m => ?_
    have : m ∈ N := by rw [hNtop]; exact Submodule.mem_top
    exact this
  -- Finrank of a line is 1.
  have h1 : Module.finrank k L = 1 := finrank_span_singleton hvne
  rw [hLtop, finrank_top] at h1
  exact h1

end Commutative

section GroupRep

variable {k : Type*} [Field k] [IsAlgClosed k]
variable {G : Type*} [CommGroup G]
variable {M : Type*} [AddCommGroup M] [Module k M]
  [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M]
  [hsm : IsSimpleModule (MonoidAlgebra k G) M] [FiniteDimensional k M]

include hsm in
/-- **Irreducible representations of abelian groups are one-dimensional.** Over an
algebraically closed field `k`, every finite-dimensional simple `k[G]`-module for
an abelian group `G` is one-dimensional over `k`. The group algebra of an abelian
group is commutative, so this is an instance of
`simple_module_over_commutative_finrank_eq_one`. -/
theorem irreducible_rep_abelian_group_finrank_eq_one :
    Module.finrank k M = 1 :=
  simple_module_over_commutative_finrank_eq_one (k := k) (A := MonoidAlgebra k G)

end GroupRep

section ComplexRep

variable {G : Type*} [CommGroup G]
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
  [Module (MonoidAlgebra ℂ G) M] [IsScalarTower ℂ (MonoidAlgebra ℂ G) M]
  [hsm : IsSimpleModule (MonoidAlgebra ℂ G) M] [FiniteDimensional ℂ M]

include hsm in
/-- **The headline complex case.** Every finite-dimensional irreducible *complex*
representation of an abelian group is one-dimensional — the classification that
underlies the character theory of abelian groups. -/
theorem irreducible_complex_rep_abelian_one_dim :
    Module.finrank ℂ M = 1 :=
  irreducible_rep_abelian_group_finrank_eq_one (k := ℂ) (G := G)

end ComplexRep

end SchursLemmaOQ01OQ02
