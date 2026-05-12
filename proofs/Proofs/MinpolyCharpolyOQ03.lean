import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic
import Proofs.MinpolyCharpoly

/-
# Rational Canonical Form via Minimal-Polynomial Invariant Factors

## Open Question (minpoly-charpoly-oq-03)

> Can the rational canonical form (based on minpoly factorization) be
> formalized in Lean 4?

This is `conclusion.openQuestions[2]` of the parent gallery entry
`minpoly-charpoly` (Minimal Polynomial vs Characteristic Polynomial of
Matrices — 17 theorems, 0 axioms).

## Resolution (S1 OBSERVE — affirmative)

**Yes, the rational canonical form (RCF) is formalizable in Lean 4** —
all three ingredients required for a clean formalisation are already
available either in the in-tree gallery or in Mathlib:

1. **Companion-matrix infrastructure (already in-tree).** The file
   `Proofs/CayleyHamiltonReductionOQ02OQ01.lean` defines
   `companionMatrix : F[X] → Matrix (Fin d) (Fin d) F` and proves the
   two key block-level identities:

     * `charpoly (companionMatrix p) = p`
     * `minpoly  (companionMatrix p) = p`   (companion is non-derogatory)

   Each invariant-factor block in the eventual RCF assembly therefore
   has the expected charpoly/minpoly contribution.

2. **Structure theorem for finitely generated modules over a PID
   (Mathlib).** Specifically:

     * `Module.equiv_directSum_of_isTorsion`
     * `Module.equiv_free_prod_directSum`

   both in `Mathlib.Algebra.Module.PID` (cross-referenced from
   `Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean`).

   Apply this to `K^n` viewed as an `F[X]`-module via the action of `M`:
   the module is finitely generated and torsion (annihilated by
   `charpoly M`), hence splits as
   `K^n  ≅_{F[X]}  ⊕ᵢ  F[X] / (pᵢ)`
   with the divisibility chain `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ`, where
   `pₖ = minpoly M` and `∏ᵢ pᵢ = charpoly M`.

3. **Cyclic summand ↔ companion block.** On the cyclic `F[X]`-module
   `F[X] / (pᵢ)`, the basis `{1, X, X², ..., X^{dᵢ-1}}`
   (with `dᵢ = deg pᵢ`) realises multiplication-by-`X` as the
   companion matrix `companionMatrix pᵢ`. Reassembling these blocks
   gives the global similarity
   `M  ~  blockDiag (companionMatrix p₁) ⋯ (companionMatrix pₖ)`.

**No genuine Mathlib gap or axiomatic assumption is required.** The
remaining work is purely integrative: glue these three pieces together.

## Decomposition into Sub-OQs (proposed)

For follow-up iterations / child OQs, the work decomposes naturally:

| Sub-OQ | Content | Estimated lines |
|--------|---------|-----------------|
| **OQ-03-OQ-01** | `F[X]`-module structure on `K^n` via `M`; show finitely generated and torsion. | ~150 |
| **OQ-03-OQ-02** | Apply `Module.equiv_directSum_of_isTorsion` to get the invariant-factor decomposition with divisibility chain. | ~300 |
| **OQ-03-OQ-03** | Cyclic-summand ↔ companion-block correspondence. | ~250 |
| **OQ-03-OQ-04** | Global assembly of the similarity transform. | ~200 |

Total roadmap: ≈ 900 lines (smaller than the file-level estimate in
`CayleyHamiltonReductionOQ02OQ01.lean`'s gap assessment, which routed
through a separate Smith-normal-form pass; here we use the Mathlib
structure theorem directly).

## What This File Contributes (S1 scaffold)

* **`InvariantFactorChain`** — data structure capturing a list of monic
  polynomials together with a proof of the divisibility chain
  `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ`.
* **`InvariantFactorChain.prodFactors`** — the product `∏ᵢ pᵢ` of the
  chain, target value `charpoly M`.
* **`InvariantFactorChain.lastFactor`** — the last factor `pₖ`, target
  value `minpoly M`.
* **`rational_canonical_form_exists`** — the **main RCF theorem
  statement**, guarded by a single `sorry` that this S1 OBSERVE iteration
  leaves for the four sub-OQs above to discharge.
* **`prodFactors_empty`** — unconditional sanity check that an empty
  chain has product 1.

## References

* Frobenius, *Über die mit einer Matrix vertauschbaren Matrizen* (1896)
* Mathlib `Module.equiv_directSum_of_isTorsion`
  (`Mathlib.Algebra.Module.PID`)
* `Proofs/CayleyHamiltonReductionOQ02OQ01.lean` — companion matrix
  infrastructure (charpoly, minpoly, orbit lemma)
* `Proofs/MinpolyCharpoly.lean` — parent file (17 theorems on
  `minpoly ∣ charpoly`)
* Dummit & Foote, *Abstract Algebra* (3rd ed., 2004), §12.2

Tags: linear-algebra, matrices, rational-canonical-form,
minimal-polynomial, characteristic-polynomial, structure-theorem-pid
-/

namespace MinpolyCharpolyOQ03

open Matrix Polynomial BigOperators

variable {F : Type*} [Field F]

/-! ## Part 1: Invariant Factor Data

We capture the invariant-factor data abstractly: a list of monic
polynomials of positive degree, with the divisibility chain enforced
as a structure field. -/

/-- An **invariant-factor chain** over a field `F`: a list of monic
    polynomials of positive degree, ordered so that each divides the
    next (`p₁ ∣ p₂ ∣ ⋯ ∣ pₖ`).

    This is the abstract data that parametrises the rational canonical
    form: a matrix is "in RCF" if it is block-diagonal with companion
    blocks `companionMatrix pᵢ` corresponding to an `InvariantFactorChain`. -/
structure InvariantFactorChain (F : Type*) [Field F] where
  /-- The list of invariant factors `(p₁, …, pₖ)`. -/
  factors : List F[X]
  /-- Each factor is monic. -/
  monic : ∀ p ∈ factors, p.Monic
  /-- Each factor has positive degree (nontriviality of each block). -/
  posDegree : ∀ p ∈ factors, 0 < p.natDegree
  /-- Divisibility chain: `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ`. -/
  chain : ∀ i j : Fin factors.length, i.val ≤ j.val → factors[i] ∣ factors[j]

/-- The product `∏ᵢ pᵢ` of the invariant factors — target value
    `charpoly M` in the eventual RCF correspondence. -/
noncomputable def InvariantFactorChain.prodFactors
    (c : InvariantFactorChain F) : F[X] :=
  c.factors.prod

/-- The last factor `pₖ` of the chain — target value `minpoly M` in the
    eventual RCF correspondence. Falls back to `1` for the empty chain
    (a degenerate case that does not arise for a nontrivial matrix). -/
noncomputable def InvariantFactorChain.lastFactor
    (c : InvariantFactorChain F) : F[X] :=
  c.factors.getLast?.getD 1

/-! ## Part 2: Main Theorem Statement (S1 — sorry placeholder)

The S1 deliverable is the **statement** of the rational canonical form
existence theorem. The proof is left as a `sorry` and will be
discharged by the four-step decomposition documented at the top of
this file (sub-OQs `oq-03-oq-01` through `oq-03-oq-04`).
-/

/-- **Rational Canonical Form — Existence (S1 statement, S2+ proof)**:

    Every square matrix `M` over a field `F` admits an
    `InvariantFactorChain` whose product equals `charpoly M`.

    *Status*: **S1 OBSERVE scaffold** — statement only, proof deferred
    to the four-step decomposition (sub-OQs `oq-03-oq-01` through
    `oq-03-oq-04`).

    The full Frobenius theorem additionally asserts that `M` is
    similar to the block diagonal of the companion matrices of the
    chain, with the last factor equal to `minpoly M`. Those refinements
    are intentionally omitted from this S1 statement to keep the
    scaffold minimal; they will be added incrementally as sub-OQs
    discharge them. -/
theorem rational_canonical_form_exists
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n F) :
    ∃ c : InvariantFactorChain F, c.prodFactors = M.charpoly := by
  sorry

/-! ## Part 3: Unconditional structural lemma

A single trivial sanity check, verifying that the data captured by
`InvariantFactorChain` and `prodFactors` is internally consistent. -/

/-- The empty invariant-factor chain has product `1`. -/
theorem prodFactors_empty
    (c : InvariantFactorChain F) (h : c.factors = []) :
    c.prodFactors = 1 := by
  unfold InvariantFactorChain.prodFactors
  rw [h]
  simp

end MinpolyCharpolyOQ03
