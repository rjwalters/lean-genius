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

## What This File Contributes (S1 scaffold + S2 helpers)

* **`InvariantFactorChain`** — data structure capturing a list of monic
  polynomials together with a proof of the divisibility chain
  `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ`.
* **`InvariantFactorChain.prodFactors`** — the product `∏ᵢ pᵢ` of the
  chain, target value `charpoly M`.
* **`InvariantFactorChain.lastFactor`** — the last factor `pₖ`, target
  value `minpoly M`.
* **`rational_canonical_form_exists`** — the **main RCF theorem
  statement**, guarded by a single `sorry` that the S1 OBSERVE iteration
  leaves for the four sub-OQs above to discharge.
* **`prodFactors_empty`** — unconditional sanity check that an empty
  chain has product 1.
* **`prodFactors_monic`** *(S2)* — the product of the invariant factors
  is monic. Unconditional; uses `Polynomial.Monic.mul` and the chain's
  monicness hypothesis.
* **`factor_dvd_prodFactors`** *(S2)* — every invariant factor divides
  the chain's product. Unconditional; instance of `List.dvd_prod`.
* **`prodFactors_ne_zero`** *(S3)* — the product of the invariant
  factors is nonzero. Direct corollary of `prodFactors_monic` via
  `Polynomial.Monic.ne_zero`.
* **`prodFactors_natDegree`** *(S3)* — the natDegree of the product
  equals the sum of factor natDegrees. Useful for the eventual
  block-diagonal dimension argument (∑ deg pᵢ = n).
* **`chain_natDegree_le`** *(S3)* — the divisibility chain implies the
  natDegree chain: `factors[i].natDegree ≤ factors[j].natDegree` for
  `i ≤ j`. Direct use of the structure's `chain` field plus
  `Polynomial.natDegree_le_of_dvd`.
* **`lastFactor_mem`** *(S4)* — when the chain is nonempty, the last
  factor is a member of the chain.
* **`lastFactor_monic`** *(S4)* — when the chain is nonempty, the last
  factor is monic. One-line application of `lastFactor_mem` + the
  structure's `monic` field.
* **`lastFactor_natDegree_maximal`** *(S4)* — every factor's natDegree
  is at most `lastFactor.natDegree`. One-line application of
  `chain_natDegree_le` with the last index. Abstract counterpart of
  "`pₖ = minpoly M` has the maximal degree among invariant factors".

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

/-! ## Part 3: Unconditional structural lemmas

Three sanity-level facts about the abstract `InvariantFactorChain` data,
independent of any matrix `M`. They isolate the cleanest part of the
RCF formalisation surface: anything that follows directly from
"`factors` is a list of monic polynomials with `prodFactors = .prod`"
should already be available here, sorry-free. -/

/-- The empty invariant-factor chain has product `1`. -/
theorem prodFactors_empty
    (c : InvariantFactorChain F) (h : c.factors = []) :
    c.prodFactors = 1 := by
  unfold InvariantFactorChain.prodFactors
  rw [h]
  simp

/-- Auxiliary: the product of a list of monic polynomials is monic. -/
private theorem list_prod_monic_of_all_monic
    {l : List F[X]} (hl : ∀ p ∈ l, p.Monic) : l.prod.Monic := by
  induction l with
  | nil =>
    rw [List.prod_nil]
    exact monic_one
  | cons p ps ih =>
    rw [List.prod_cons]
    refine Monic.mul ?_ ?_
    · exact hl p List.mem_cons_self
    · exact ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))

/-- The product of the invariant factors is monic. Follows from
    `Polynomial.Monic.mul` plus the chain's monicness hypothesis,
    by induction on the underlying list. -/
theorem prodFactors_monic (c : InvariantFactorChain F) :
    c.prodFactors.Monic :=
  list_prod_monic_of_all_monic c.monic

/-- Each invariant factor divides the product of the chain. Direct
    instance of `List.dvd_prod`. -/
theorem factor_dvd_prodFactors
    (c : InvariantFactorChain F) {p : F[X]} (hp : p ∈ c.factors) :
    p ∣ c.prodFactors :=
  List.dvd_prod hp

/-! ## Part 4: S3 unconditional helpers — nonzero, natDegree sum,
       natDegree chain.

These extend the auditor follow-through (S2) with three more
unconditional facts about `InvariantFactorChain`:

* `prodFactors_ne_zero` — trivial corollary of `prodFactors_monic`.
* `prodFactors_natDegree` — the natDegree of the product equals the
  sum of factor natDegrees. Needed for the eventual dimension argument
  `∑ deg pᵢ = n` in OQ-03-OQ-04.
* `chain_natDegree_le` — divisibility chain ⇒ natDegree chain. Useful
  for proving that `lastFactor` has the maximal natDegree, which is
  what makes it the minimal polynomial in the RCF correspondence.
-/

/-- The product of the invariant factors is nonzero. Direct corollary
    of `prodFactors_monic` (via `Polynomial.Monic.ne_zero`). -/
theorem prodFactors_ne_zero (c : InvariantFactorChain F) :
    c.prodFactors ≠ 0 :=
  (prodFactors_monic c).ne_zero

/-- Auxiliary: the natDegree of a list-product of monic polynomials is
    the sum of their natDegrees. Follows from `Polynomial.natDegree_mul`
    on monic factors (monic ⇒ nonzero), by induction on the list. -/
private theorem list_prod_natDegree_of_all_monic
    {l : List F[X]} (hl : ∀ p ∈ l, p.Monic) :
    l.prod.natDegree = (l.map (·.natDegree)).sum := by
  induction l with
  | nil =>
    simp
  | cons p ps ih =>
    have hp : p.Monic := hl p List.mem_cons_self
    have hps_all : ∀ q ∈ ps, q.Monic :=
      fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hps_monic : ps.prod.Monic := list_prod_monic_of_all_monic hps_all
    rw [List.prod_cons, List.map_cons, List.sum_cons,
        Polynomial.natDegree_mul hp.ne_zero hps_monic.ne_zero,
        ih hps_all]

/-- The natDegree of the product of the invariant factors equals the
    sum of the factors' natDegrees. Bridges between the abstract
    chain data and the dimensional bookkeeping needed for the
    block-diagonal assembly (OQ-03-OQ-04). -/
theorem prodFactors_natDegree (c : InvariantFactorChain F) :
    c.prodFactors.natDegree = (c.factors.map (·.natDegree)).sum :=
  list_prod_natDegree_of_all_monic c.monic

/-- Divisibility chain ⇒ natDegree chain. If `i ≤ j` (so
    `factors[i] ∣ factors[j]`) then `factors[i].natDegree ≤
    factors[j].natDegree`. Direct use of the structure's `chain` field
    plus `Polynomial.natDegree_le_of_dvd` (which needs the larger
    factor nonzero — supplied by monicness). -/
theorem chain_natDegree_le
    (c : InvariantFactorChain F)
    {i j : Fin c.factors.length} (h : i.val ≤ j.val) :
    c.factors[i].natDegree ≤ c.factors[j].natDegree := by
  have hdvd : c.factors[i] ∣ c.factors[j] := c.chain i j h
  have hmem : c.factors[j] ∈ c.factors := List.getElem_mem j.isLt
  have hmonic : c.factors[j].Monic := c.monic _ hmem
  exact Polynomial.natDegree_le_of_dvd hdvd hmonic.ne_zero


/-! ## Part 5: S4 unconditional helpers — `lastFactor` membership,
       monicness, and degree maximality.

These extend S3 with three more sorry-free facts about the
`InvariantFactorChain` data, all conditional on `c.factors ≠ []`:

* `lastFactor_mem` — `lastFactor c ∈ c.factors` (when factors are
  nonempty). Direct consequence of `getLast?.getD 1 = getLast h`
  for nonempty lists, combined with `List.getLast_mem`.
* `lastFactor_monic` — `(lastFactor c).Monic`. One-liner via the
  chain's `monic` field applied to `lastFactor_mem`.
* `lastFactor_natDegree_maximal` — every factor's natDegree is at
  most `(lastFactor c).natDegree`. The abstract counterpart of the
  RCF fact "`pₖ = minpoly M` has the maximal degree among invariant
  factors" — one-line application of `chain_natDegree_le` with the
  last index. With S3's `prodFactors_natDegree` this also yields
  the bookkeeping bound `lastFactor.natDegree ≤ ∑ deg pᵢ`, useful
  when the chain is eventually instantiated by a matrix M.
-/

/-- The `lastFactor` of a nonempty chain coincides with the indexed
    access at the last position. Internal-use lemma bridging the
    `getLast?.getD 1` definition with the `Fin`-indexed access used
    by `chain_natDegree_le`. -/
private theorem lastFactor_eq_getElem_pred
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.lastFactor = c.factors[c.factors.length - 1]'(by
      have hpos : 0 < c.factors.length := List.length_pos.mpr h
      omega) := by
  show c.factors.getLast?.getD 1 = _
  rw [List.getLast?_eq_getLast h]
  -- Now: `(some (c.factors.getLast h)).getD 1 = c.factors[...]`
  show c.factors.getLast h = _
  exact List.getLast_eq_getElem h

/-- The last factor of a nonempty invariant-factor chain is a member of
    the chain. -/
theorem lastFactor_mem (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.lastFactor ∈ c.factors := by
  rw [lastFactor_eq_getElem_pred c h]
  exact List.getElem_mem _

/-- The last factor of a nonempty invariant-factor chain is monic. -/
theorem lastFactor_monic
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.lastFactor.Monic :=
  c.monic _ (lastFactor_mem c h)

/-- Every invariant factor has natDegree at most that of the last
    factor. This is the abstract counterpart of the RCF fact that the
    last invariant factor `pₖ` (which equals `minpoly M` in the matrix
    instantiation) has the maximal degree among the invariant factors.
    One-line application of `chain_natDegree_le` with `j = length - 1`. -/
theorem lastFactor_natDegree_maximal
    (c : InvariantFactorChain F) (h : c.factors ≠ [])
    {p : F[X]} (hp : p ∈ c.factors) :
    p.natDegree ≤ c.lastFactor.natDegree := by
  rw [List.mem_iff_getElem] at hp
  obtain ⟨i, hi, hip⟩ := hp
  have hpos : 0 < c.factors.length := List.length_pos.mpr h
  let i' : Fin c.factors.length := ⟨i, hi⟩
  let j  : Fin c.factors.length := ⟨c.factors.length - 1, by omega⟩
  have hij : i'.val ≤ j.val := by
    show i ≤ c.factors.length - 1
    omega
  have hdeg : c.factors[i'].natDegree ≤ c.factors[j].natDegree :=
    chain_natDegree_le c hij
  rw [← hip, lastFactor_eq_getElem_pred c h]
  exact hdeg

end MinpolyCharpolyOQ03
