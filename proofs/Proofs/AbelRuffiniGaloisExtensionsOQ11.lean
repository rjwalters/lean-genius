/-
# Noether's rationality problem for the symmetric group `Sₙ` (openQuestion #11)

This file formalizes the **universally positive core** of Noether's rationality
problem (Emmy Noether 1918, *Gleichungen mit vorgeschriebener Gruppe*,
Math. Ann. 78: 221–229) for the full symmetric group `G = Sₙ` acting on
`K(x₁, …, xₙ)` by permuting the indeterminates.

## Noether's problem

For a finite group `G ≤ Sₙ` acting on the rational function field
`K(x₁, …, xₙ)` by permuting the variables, Noether's problem asks whether the
fixed field `K(x₁, …, xₙ)ᴳ` is *purely transcendental* over `K`, i.e. isomorphic
to `K(y₁, …, yₙ)` for algebraically independent generators `yⱼ`.  A positive
answer ("`G` is Noether-rational") upgrades the abstract inverse-Galois existence
to an *explicit parametric* family of `G`-extensions of `K` (via Hilbert
irreducibility).

For arbitrary `G` the answer is **negative in general** — the first
counterexample is Swan's `ℤ/47ℤ` (1969), and the precise obstruction is the
Bogomolov multiplier `B₀(G)` (Saltman 1984, Bogomolov 1988).  But for the
**full symmetric group `G = Sₙ`** the answer is positive for *every* `n`,
independently of solvability: the invariant ring is the polynomial ring in the
elementary symmetric polynomials `e₁, …, eₙ` (the fundamental theorem of
symmetric functions), and its fraction field is `K(e₁, …, eₙ)`, purely
transcendental of transcendence degree `n`.

## The formalizable kernel

The arithmetic heart is purely algebraic and holds over any commutative ring `R`:

* `MvPolynomial.esymm_algebraicIndependent` — the `n` elementary symmetric
  polynomials `e₁, …, eₙ` in the variables `σ` (with `n ≤ #σ`) are
  **algebraically independent** over `R`.  Combined with the fundamental
  theorem this is the transcendence-degree-`n` statement that makes the
  `Sₙ`-fixed field purely transcendental.  (Mathlib has the fundamental theorem
  `esymmAlgEquiv` but does *not* package algebraic independence of `esymm`.)

* `MvPolynomial.noetherWitnessSn` / `Sn_invariantRing_polynomial` — re-exports
  Mathlib's `esymmAlgEquiv` as the explicit **Noether-rationality witness for
  `Sₙ`**: the ring of `Sₙ`-invariants `MvPolynomial σ R` is isomorphic, as an
  `R`-algebra, to a polynomial ring in `n` generators.

* `Sn_noetherRational_all_n` — the witness exists for **every** `n`.

* `S5_not_solvable_but_noether_rational` — the **threshold contrast** with the
  parent file (`Sₙ` solvable ↔ `n ≤ 4`): `S₅` is *not* solvable, yet its
  invariant ring is still a polynomial ring.  Universal Noether-rationality of
  `Sₙ` crosses the Abel–Ruffini solvability threshold untouched, isolating
  *parametric construction* from *radical solvability*.

All results are machine-checked with no `sorry` and no extra axioms.
-/

import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.GroupTheory.Solvable

open scoped BigOperators

namespace MvPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ] (R : Type*) [CommRing R] {n : ℕ}

omit [DecidableEq σ] in
/-- **Algebraic independence of the elementary symmetric polynomials.**

If `n ≤ #σ`, then the `n` elementary symmetric polynomials `e₁, …, eₙ`
(`fun i : Fin n ↦ esymm σ R (i + 1)`) are algebraically independent over `R`.

This is the transcendence-degree-`n` core of Noether-rationality for `Sₙ`:
together with the fundamental theorem of symmetric functions it shows that the
ring of `Sₙ`-invariants is a *polynomial* ring in `n` algebraically independent
generators, whence its fraction field is purely transcendental.

The proof reduces algebraic independence to injectivity of
`aeval (fun i ↦ esymm σ R (i + 1))`, which is exactly the injectivity of
Mathlib's `esymmAlgHom` (the fundamental theorem provides it for `n ≤ #σ`). -/
theorem esymm_algebraicIndependent (hn : n ≤ Fintype.card σ) :
    AlgebraicIndependent R (fun i : Fin n => esymm σ R (i + 1)) := by
  rw [algebraicIndependent_iff_injective_aeval]
  intro p q h
  apply esymmAlgHom_injective R hn
  apply Subtype.ext
  rw [esymmAlgHom_apply, esymmAlgHom_apply]
  exact h

/-- **Noether-rationality witness for `Sₙ` (algebra level).**

When `#σ = n`, the ring of `Sₙ`-invariant polynomials `symmetricSubalgebra σ R`
is isomorphic as an `R`-algebra to the polynomial ring `MvPolynomial (Fin n) R`,
the isomorphism sending the `i`-th coordinate to the `(i+1)`-st elementary
symmetric polynomial.  This is the constructive heart of Noether's positive
answer for the full symmetric group; passing to fraction fields gives pure
transcendence of the fixed field `K(x₁, …, xₙ)^{Sₙ} ≅ K(e₁, …, eₙ)`.

This is a re-export of Mathlib's fundamental theorem of symmetric functions
`esymmAlgEquiv`, named for its role in Noether's problem. -/
noncomputable def noetherWitnessSn (hn : Fintype.card σ = n) :
    MvPolynomial (Fin n) R ≃ₐ[R] symmetricSubalgebra σ R :=
  esymmAlgEquiv σ R hn

omit [DecidableEq σ] in
/-- The ring of `Sₙ`-invariants is a polynomial ring in `n` generators
(packaged as `Nonempty` of the algebra equivalence). -/
theorem Sn_invariantRing_polynomial (hn : Fintype.card σ = n) :
    Nonempty (MvPolynomial (Fin n) R ≃ₐ[R] symmetricSubalgebra σ R) :=
  ⟨noetherWitnessSn R hn⟩

/-- **Universal Noether-rationality of `Sₙ`.**

For *every* `n`, the ring of `Sₙ`-invariants `symmetricSubalgebra (Fin n) R` is a
polynomial ring in `n` generators — Noether's problem has a positive answer for
the full symmetric group with no restriction on `n` (in particular, no
solvability hypothesis). -/
theorem Sn_noetherRational_all_n (n : ℕ) :
    Nonempty (MvPolynomial (Fin n) R ≃ₐ[R] symmetricSubalgebra (Fin n) R) :=
  ⟨esymmAlgEquiv (Fin n) R (Fintype.card_fin n)⟩

/-- **Noether-rationality crosses the Abel–Ruffini solvability threshold.**

The parent file proves `Sₙ` is solvable iff `n ≤ 4`.  Here we exhibit the sharp
contrast at `n = 5`: the symmetric group `S₅` is **not** solvable
(`Equiv.Perm.fin_5_not_solvable`, the group-theoretic heart of Abel–Ruffini),
yet its invariant ring `symmetricSubalgebra (Fin 5) R` is **still** a polynomial
ring in `5` generators (Noether-rational).

Thus universal Noether-rationality of `Sₙ` is *independent* of solvability:
the quintic has an explicit elementary-symmetric-function parametrization of its
splitting data even though it has no radical recipe.  This separates *parametric
construction* (always available for `Sₙ`) from *radical solvability* (only for
`n ≤ 4`). -/
theorem S5_not_solvable_but_noether_rational :
    ¬ IsSolvable (Equiv.Perm (Fin 5)) ∧
      Nonempty (MvPolynomial (Fin 5) R ≃ₐ[R] symmetricSubalgebra (Fin 5) R) :=
  ⟨Equiv.Perm.fin_5_not_solvable, Sn_noetherRational_all_n R 5⟩

end MvPolynomial
