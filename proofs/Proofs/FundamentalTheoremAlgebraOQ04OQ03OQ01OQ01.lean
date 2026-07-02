import Mathlib

/-
# `Gal(L/K) ≃* Multiplicative (ZMod 2)` for every quadratic Galois extension

## What this proves

This is the leaf `oq-04-oq-03-oq-01-oq-01`, extending
`FundamentalTheoremAlgebraOQ04OQ03OQ01` ("the explicit iso
`Gal(ℂ/ℝ) ≃* Multiplicative (ZMod 2)`, generator = complex conjugation").

The parent's open question OQ[0] asks to **generalize from `ℝ` to an arbitrary
real-closed field `R`**: build `Gal(R(√-1)/R) ≃* Multiplicative (ZMod 2)` with
Artin–Schreier conjugation as generator.  The full real-closed-field statement
depends on the **Artin–Schreier theorem** ("if `R` is real closed then `R(√-1)`
is algebraically closed and `[R(√-1):R] = 2`"), which is *not* in Mathlib —
Mathlib has no `IsRealClosed` typeclass at all.  Building that theory is a
>1000-line foundational project, so it is out of reach this session (documented
honestly below).

What *is* fully general, and what this file proves with **zero axioms**, is the
**group-theoretic core** the open question is really about: the shape of the
Galois group depends only on the extension being **degree 2 and Galois**, never
on `R` being real closed.  Concretely:

* `galEquivZMod2` : for **any** finite-dimensional Galois extension `L/K` with
  `[L:K] = 2`, there is a multiplicative isomorphism
  `(L ≃ₐ[K] L) ≃* Multiplicative (ZMod 2)`;
* `card_gal_eq_two`, `isCyclic_gal`, `gal_mul_comm` : the group has order `2`,
  is cyclic, and is commutative;
* `galCyclicEquiv` : identifies the group with Mathlib's canonical
  `zmodCyclicMulEquiv` (the parent's OQ[1]) — the abstract cyclic-structure iso;
* `complex_gal_equiv_zmod2` : instantiating `K = ℝ`, `L = ℂ` recovers the
  parent's `Gal(ℂ/ℝ) ≃* Multiplicative (ZMod 2)`, confirming the generalization
  subsumes the base case.

Since `R(√-1)/R` is a degree-2 Galois extension exactly *when* Artin–Schreier
holds, `galEquivZMod2` is the correct target theorem for every real-closed `R`
the moment that missing hypothesis is supplied — the whole content beyond
"degree 2 + Galois" is the analytic Artin–Schreier input, which we isolate rather
than hide.

The proof is one line of mathematics: `|Gal(L/K)| = [L:K] = 2`
(`IsGalois.card_aut_eq_finrank`), and any two groups of the same prime
cardinality are isomorphic (`mulEquivOfPrimeCardEq`).

*Reference:* Galois theory of quadratic extensions; Artin–Schreier theory of
real-closed fields (Lang, *Algebra*, XI §2). Mathlib
`Mathlib.FieldTheory.Galois.Basic`, `Mathlib.GroupTheory.SpecificGroups.Cyclic`.
-/

namespace FTAGaloisIsoGeneral

open Module

/-! ## Cardinality helper -/

/-- **`Multiplicative (ZMod 2)` has exactly two elements.** -/
theorem card_multiplicative_zmod_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  simp [Nat.card_eq_fintype_card]

/-! ## The general theorem: quadratic Galois ⇒ `Gal ≃* ZMod 2`

Everything below abstracts over an arbitrary base field `K` and a degree-2
Galois extension `L`.  Nothing uses order structure, real-closedness, or the
identity of the base field — only `finrank K L = 2` together with the `IsGalois`
hypothesis. -/

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **`|Gal(L/K)| = 2`** for a quadratic Galois extension: for a Galois extension
the automorphism group has cardinality equal to the degree. -/
theorem card_gal_eq_two (h : finrank K L = 2) : Nat.card (L ≃ₐ[K] L) = 2 := by
  rw [IsGalois.card_aut_eq_finrank K L, h]

/-- **`Gal(L/K)` is cyclic.** A finite group of prime order is cyclic. -/
theorem isCyclic_gal (h : finrank K L = 2) : IsCyclic (L ≃ₐ[K] L) :=
  isCyclic_of_prime_card (p := 2) (card_gal_eq_two K L h)

/-- **The generalized isomorphism `Gal(L/K) ≃* Multiplicative (ZMod 2)`.**

Two groups of the same prime cardinality are isomorphic
(`mulEquivOfPrimeCardEq`); here both sides have cardinality `2`.  This is the
group-theoretic heart of the open question — valid for the Galois group of every
quadratic Galois extension, hence in particular for `Gal(R(√-1)/R)` of any
real-closed field `R` once `[R(√-1):R] = 2` and Galois are supplied via
Artin–Schreier. -/
noncomputable def galEquivZMod2 (h : finrank K L = 2) :
    (L ≃ₐ[K] L) ≃* Multiplicative (ZMod 2) :=
  mulEquivOfPrimeCardEq (p := 2) (card_gal_eq_two K L h) card_multiplicative_zmod_two

/-- **`Gal(L/K)` is commutative** (transport of `mul_comm` across the iso, or
directly: a group of prime order is abelian). -/
theorem gal_mul_comm (h : finrank K L = 2) (a b : L ≃ₐ[K] L) : a * b = b * a := by
  apply (galEquivZMod2 K L h).injective
  rw [map_mul, map_mul, mul_comm]

/-- **Identification with Mathlib's canonical cyclic-structure iso** (parent OQ[1]).

`zmodCyclicMulEquiv` is Mathlib's canonical isomorphism
`Multiplicative (ZMod (Nat.card G)) ≃* G` for a cyclic group `G`.  Rewriting
`Nat.card (L ≃ₐ[K] L) = 2` turns it into an iso from `Multiplicative (ZMod 2)`,
witnessing that the abstract `IsCyclic` structure of the parent is realized by
the same `ZMod 2` on the nose. -/
noncomputable def galCyclicEquiv (h : finrank K L = 2) :
    Multiplicative (ZMod 2) ≃* (L ≃ₐ[K] L) :=
  haveI := isCyclic_gal K L h
  (card_gal_eq_two K L h) ▸ zmodCyclicMulEquiv (isCyclic_gal K L h)

end FTAGaloisIsoGeneral

/-! ## Recovering the base case `Gal(ℂ/ℝ) ≃* Multiplicative (ZMod 2)`

Instantiating the general theorem at `K = ℝ`, `L = ℂ` reproduces the parent
leaf's isomorphism, confirming the generalization subsumes the concrete result. -/

namespace FTAGaloisIsoGeneral.ComplexReal

open Complex Module

/-- ℂ is algebraic over ℝ (finite ⇒ algebraic). -/
instance : Algebra.IsAlgebraic ℝ ℂ := Algebra.IsAlgebraic.of_finite ℝ ℂ

/-- ℂ is an algebraic closure of ℝ — supplies `Normal ℝ ℂ`. -/
instance : IsAlgClosure ℝ ℂ where
  isAlgClosed := Complex.isAlgClosed
  isAlgebraic := inferInstance

/-- `ℂ/ℝ` is Galois: finite + separable (char 0) + normal (algebraic closure). -/
instance : IsGalois ℝ ℂ := IsGalois.mk

/-- **`Gal(ℂ/ℝ) ≃* Multiplicative (ZMod 2)`**, obtained as the `K = ℝ, L = ℂ`
instance of the general `galEquivZMod2`. -/
noncomputable def complex_gal_equiv_zmod2 : (ℂ ≃ₐ[ℝ] ℂ) ≃* Multiplicative (ZMod 2) :=
  galEquivZMod2 ℝ ℂ Complex.finrank_real_complex

/-- **`|Gal(ℂ/ℝ)| = 2`**, as the instance of `card_gal_eq_two`. -/
theorem card_complex_gal_eq_two : Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2 :=
  card_gal_eq_two ℝ ℂ Complex.finrank_real_complex

end FTAGaloisIsoGeneral.ComplexReal
