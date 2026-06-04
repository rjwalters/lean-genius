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
   `charpoly M`), hence splits as a direct sum of **primary cyclic
   summands**
   `K^n  ≅_{F[X]}  ⊕ᵢ  F[X] / (pᵢ^{eᵢ})`
   where each `pᵢ ∈ F[X]` is **irreducible**. A second *regrouping*
   step (not provided by Mathlib v4.26.0) converts these elementary
   divisors into the invariant-factor chain
   `d₁ ∣ d₂ ∣ ⋯ ∣ dₖ`, where each `dⱼ` is a product of certain
   `pᵢ^{eᵢ}`. The chain then satisfies `dₖ = minpoly M` and
   `∏ⱼ dⱼ = charpoly M`. See sub-OQ OQ-03-OQ-02 for the regrouping
   bookkeeping (~290 LOC over Multiset/Finset/List structures;
   substantive Mathlib gap). The S11 PREP audit
   (`research/problems/minpoly-charpoly-oq-03/sessions/
   2026-05-13-s11-prep-oq03-oq02-elementary-divisors-erratum.md`)
   pinned the exact `Module.equiv_directSum_of_isTorsion` signature
   at Mathlib v4.26.0 `Mathlib/Algebra/Module/PID.lean:233`:
   the witness `p : ι → R` satisfies `Irreducible (p i)` (not a
   chain), so the cyclic summands are `R ⧸ R ∙ p i ^ e i` —
   *prime powers*, not invariant factors.

3. **Cyclic summand ↔ companion block.** On each cyclic `F[X]`-module
   `F[X] / (dⱼ)` of the invariant-factor decomposition, the basis
   `{1, X, X², ..., X^{cⱼ-1}}` (with `cⱼ = deg dⱼ`) realises
   multiplication-by-`X` as the companion matrix `companionMatrix dⱼ`.
   Reassembling these blocks gives the global similarity
   `M  ~  blockDiag (companionMatrix d₁) ⋯ (companionMatrix dₖ)`.

**Mathlib gap status (post-S11 audit, 2026-05-13).** Exactly **one
genuine Mathlib gap** is required: the **elementary-divisors →
invariant-factors regrouping** algorithm (sub-OQ OQ-03-OQ-02,
~290 LOC of `Multiset`/`Finset`/`List` bookkeeping). Mathlib v4.26.0
provides only the primary form via `Module.equiv_directSum_of_isTorsion`
(`p i` irreducible, no chain). A potential alternative — Smith
normal form on `X·I − M` (`Submodule.smithNormalForm` at
`Mathlib/LinearAlgebra/FreeModule/PID.lean:541`) — has its own gap
(the diagonal entries are not certified to satisfy `a 0 ∣ a 1 ∣ ⋯ ∣
a (n-1)`). Both gaps are upstreamable as Mathlib contributions. The
rest of the OQ-03 work is integrative.

## Decomposition into Sub-OQs (proposed)

For follow-up iterations / child OQs, the work decomposes naturally:

| Sub-OQ | Content | Estimated lines |
|--------|---------|-----------------|
| **OQ-03-OQ-01** | `F[X]`-module structure on `K^n` via `M`; show finitely generated and torsion. | ~150 |
| **OQ-03-OQ-02** | Apply `Module.equiv_directSum_of_isTorsion` (primary form) **then regroup elementary divisors into invariant factors**. The regrouping is the substantive Mathlib gap (~290 LOC bookkeeping + ~50 LOC API plumbing ≈ 340 LOC; see S11 PREP §6 for full skeleton). | ~340 |
| **OQ-03-OQ-03** | Cyclic-summand ↔ companion-block correspondence. | ~250 |
| **OQ-03-OQ-04** | Global assembly of the similarity transform. | ~200 |

Total roadmap: ≈ 940 lines (slightly larger than the original
~900-line estimate after the S11 PREP audit revised OQ-03-OQ-02
upward to account for the elementary→invariant regrouping; still
smaller than the alternative ~1800-line SNF-via-`X·I − M` route
mentioned in `CayleyHamiltonReductionOQ02OQ01.lean`'s gap
assessment).

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

/-- **Rational Canonical Form — Existence (S1 statement; S14 strengthened; S2+ proof)**:

    Every square matrix `M` over a field `F` admits an
    `InvariantFactorChain` whose product equals `charpoly M` **and**
    whose last factor equals `minpoly M`.

    *Status*: **S14 strong-form statement** — statement only, proof
    deferred to the four-step decomposition (sub-OQs `oq-03-oq-01`
    through `oq-03-oq-04`) plus the `lastFactor = minpoly`
    follow-up (state.md next-action option 2).

    The strong form adds the conjunct `c.lastFactor = M.minpoly` to
    the S1 statement. This sets up the deliverable surface for the
    follow-up proof (option 2 in state.md): the structural fact that
    `ann(xModule M) = (M.minpoly)` (via
    `annihilator_top_eq_ker_aeval`) plus monic uniqueness forces
    `c.lastFactor = M.minpoly`. The strengthened statement remains
    consistent with the full Frobenius theorem; only the similarity-
    transform assertion (`M` is similar to the block diagonal of the
    companion matrices) is still omitted, to be added when sub-OQ
    `oq-03-oq-04` lands. -/
theorem rational_canonical_form_exists
    {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n F) :
    ∃ c : InvariantFactorChain F,
      c.prodFactors = M.charpoly ∧ c.lastFactor = M.minpoly := by
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

/-- Internal robust witness for `0 < l.length` from `l ≠ []`. Replaces
    the post-merge fragile `List.length_pos.mpr` invocation in S4
    (PR #18086) whose `List.length_pos` reference no longer exists at
    the pinned Mathlib v4.26.0 rev (see "Build status" in PR header). -/
private lemma length_pos_of_ne_nil {α : Type*} {l : List α} (h : l ≠ []) :
    0 < l.length := by
  rcases l with _ | _
  · exact absurd rfl h
  · exact Nat.succ_pos _

/-- The `lastFactor` of a nonempty chain coincides with the indexed
    access at the last position. Internal-use lemma bridging the
    `getLast?.getD 1` definition with the `Fin`-indexed access used
    by `chain_natDegree_le`. -/
private theorem lastFactor_eq_getElem_pred
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.lastFactor = c.factors[c.factors.length - 1]'(by
      have hpos : 0 < c.factors.length := length_pos_of_ne_nil h
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
  have hpos : 0 < c.factors.length := length_pos_of_ne_nil h
  let i' : Fin c.factors.length := ⟨i, hi⟩
  let j  : Fin c.factors.length := ⟨c.factors.length - 1, by omega⟩
  have hij : i'.val ≤ j.val := by
    show i ≤ c.factors.length - 1
    omega
  have hdeg : c.factors[i'].natDegree ≤ c.factors[j].natDegree :=
    chain_natDegree_le c hij
  rw [← hip, lastFactor_eq_getElem_pred c h]
  exact hdeg


/-! ## Part 6: S5 bookkeeping bound — `prodFactors.natDegree ≤ length ×
       lastFactor.natDegree`.

This composes S3's `prodFactors_natDegree` (sum-of-degrees identity) with
S4's `lastFactor_natDegree_maximal` (degree maximality) to yield a single
coarse upper bound: the natDegree of the product is at most
`factors.length` copies of the last factor's natDegree.

* Abstract counterpart of "`deg charpoly M ≤ k · deg minpoly M`" once the
  chain is instantiated by a matrix M (where `prodFactors = charpoly M`
  per S3's plan and `lastFactor = minpoly M`). Useful as a coarse
  a-priori upper bound on the natDegree of `prodFactors` before the
  sharper `deg charpoly M = n` instantiation lands at OQ-03-OQ-04.

The proof is an `induction`-based step: each summand of
`(factors.map (·.natDegree)).sum` is bounded by `lastFactor.natDegree`
via `lastFactor_natDegree_maximal`; the sum-bound-by-length-times-max
is a one-line `Nat`-arithmetic fact handled by a private helper that is
independent of `Polynomial` content.
-/

/-- Auxiliary `Nat`-arithmetic helper: a sum over a list of naturals is
    bounded by the length times any common upper bound. Pure `Nat`
    induction; no `Polynomial` content. -/
private theorem nat_list_sum_le_length_mul_of_all_le
    (l : List ℕ) (M : ℕ) (h : ∀ d ∈ l, d ≤ M) :
    l.sum ≤ l.length * M := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    have h_a : a ≤ M := h a List.mem_cons_self
    have h_tail : ∀ d ∈ tail, d ≤ M :=
      fun d hd => h d (List.mem_cons_of_mem _ hd)
    have h_ih : tail.sum ≤ tail.length * M := ih h_tail
    -- Goal: (a :: tail).sum ≤ (a :: tail).length * M
    --     = a + tail.sum ≤ (tail.length + 1) * M
    simp only [List.sum_cons, List.length_cons]
    calc a + tail.sum
        ≤ M + tail.length * M := Nat.add_le_add h_a h_ih
      _ = (tail.length + 1) * M := by ring

/-- The natDegree of `prodFactors` is at most `factors.length` times
    the natDegree of `lastFactor`. Composes S3's `prodFactors_natDegree`
    (sum-of-degrees identity) with S4's `lastFactor_natDegree_maximal`
    (degree maximality among factors).

    Abstract counterpart of the matrix-level bound
    `deg (charpoly M) ≤ k · deg (minpoly M)` (where `k` is the number of
    invariant factors), useful as a coarse a-priori upper bound before
    the sharper `deg (charpoly M) = n` instantiation lands at
    OQ-03-OQ-04. -/
theorem prodFactors_natDegree_le_lastFactor_natDegree_mul
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.prodFactors.natDegree ≤ c.factors.length * c.lastFactor.natDegree := by
  rw [prodFactors_natDegree]
  -- Goal: (c.factors.map (·.natDegree)).sum ≤ c.factors.length * c.lastFactor.natDegree
  -- (1) each (mapped) summand is at most lastFactor.natDegree by S4.
  have h_bound : ∀ d ∈ c.factors.map (·.natDegree),
      d ≤ c.lastFactor.natDegree := by
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    exact lastFactor_natDegree_maximal c h hp
  -- (2) sum-of-bounded-list ≤ length × bound, via the Nat helper.
  have h_sum :
      (c.factors.map (·.natDegree)).sum
        ≤ (c.factors.map (·.natDegree)).length * c.lastFactor.natDegree :=
    nat_list_sum_le_length_mul_of_all_le _ _ h_bound
  -- (3) rewrite map.length = original length.
  rwa [List.length_map] at h_sum


/-! ## Part 7: S13 `firstFactor`-side mirror — membership, monicness,
       degree minimality, and length×first lower bound on
       `prodFactors.natDegree`.

This is the symmetric counterpart to Parts 5 and 6: the four
`lastFactor`-side helpers established the natDegree-maximum direction
on `InvariantFactorChain F`; this Part 7 adds the natDegree-minimum
direction. The divisibility chain `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ` is
bi-directional in terms of natDegree (via `chain_natDegree_le`), so
both endpoints' structural facts are accessible without further
mathematical input.

Together with Part 6's
`prodFactors_natDegree_le_lastFactor_natDegree_mul`, the new
`prodFactors_natDegree_ge_firstFactor_natDegree_mul` bookend yields
the matrix-level sandwich

    k · deg(firstFactor M) ≤ deg(prodFactors) ≤ k · deg(lastFactor M)

once the chain is instantiated by a matrix `M` (so that
`prodFactors = charpoly M`, `lastFactor = minpoly M`).

Design memo: `sessions/2026-05-12-s06-prep-firstfactor-mirror-design.md`
(PR #18425). All four mirror lemmas follow the §3 sketches verbatim;
the `firstFactor_eq_getElem_zero` bridging lemma uses the design's
Plan-B `rcases` form (§4) to remain independent of any pinned Mathlib
`List.head?`/`List.head` API names. -/

/-- The **first factor** `p₁` of the chain — the structural counterpart
    of the divisibility-chain *minimum* (`p₁ ∣ p_i` for every later
    factor, so `deg p₁ ≤ deg p_i`). Falls back to `1` for the empty
    chain, exactly mirroring the `lastFactor` `getD 1` convention so
    that `Monic`/`natDegree`-style facts remain hypothesis-free on the
    empty-chain edge case. -/
noncomputable def InvariantFactorChain.firstFactor
    (c : InvariantFactorChain F) : F[X] :=
  c.factors.head?.getD 1

/-- The `firstFactor` of a nonempty chain coincides with the indexed
    access at position 0. Internal-use lemma bridging the
    `head?.getD 1` definition with the `Fin`-indexed access used by
    `chain_natDegree_le`. Mirror of `lastFactor_eq_getElem_pred`.

    Uses the design memo's Plan-B `rcases` form to avoid depending on
    pinned Mathlib `List.head?_eq_head` / `List.head_eq_getElem` API
    names (which may drift). The `firstFactor`-side cons-case reduces
    to `rfl` since `(a :: t).head?.getD 1 = a` and `(a :: t)[0] = a`
    are both definitional. -/
private theorem firstFactor_eq_getElem_zero
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.firstFactor = c.factors[0]'(length_pos_of_ne_nil h) := by
  rcases hl : c.factors with _ | ⟨a, t⟩
  · exact absurd hl h
  · rfl

/-- The first factor of a nonempty invariant-factor chain is a member
    of the chain. Mirror of `lastFactor_mem`. -/
theorem firstFactor_mem (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.firstFactor ∈ c.factors := by
  rw [firstFactor_eq_getElem_zero c h]
  exact List.getElem_mem _

/-- The first factor of a nonempty invariant-factor chain is monic.
    Mirror of `lastFactor_monic`. -/
theorem firstFactor_monic
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.firstFactor.Monic :=
  c.monic _ (firstFactor_mem c h)

/-- Every invariant factor has natDegree at least that of the first
    factor. This is the abstract counterpart of the RCF fact that the
    first invariant factor `p₁` (a divisor of every later factor) has
    the minimal degree among the invariant factors. One-line
    application of `chain_natDegree_le` with `i = 0`. Mirror of
    `lastFactor_natDegree_maximal`. -/
theorem firstFactor_natDegree_minimal
    (c : InvariantFactorChain F) (h : c.factors ≠ [])
    {p : F[X]} (hp : p ∈ c.factors) :
    c.firstFactor.natDegree ≤ p.natDegree := by
  rw [List.mem_iff_getElem] at hp
  obtain ⟨j, hj, hjp⟩ := hp
  have hpos : 0 < c.factors.length := length_pos_of_ne_nil h
  let i  : Fin c.factors.length := ⟨0, hpos⟩
  let j' : Fin c.factors.length := ⟨j, hj⟩
  have hij : i.val ≤ j'.val := Nat.zero_le _
  have hdeg : c.factors[i].natDegree ≤ c.factors[j'].natDegree :=
    chain_natDegree_le c hij
  rw [firstFactor_eq_getElem_zero c h, ← hjp]
  exact hdeg

/-- Auxiliary `Nat`-arithmetic helper: a sum over a list of naturals
    is at least the length times any common lower bound. Pure `Nat`
    induction; no `Polynomial` content. Mirror of
    `nat_list_sum_le_length_mul_of_all_le`. -/
private theorem nat_list_sum_ge_length_mul_of_all_ge
    (l : List ℕ) (m : ℕ) (h : ∀ d ∈ l, m ≤ d) :
    l.length * m ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a tail ih =>
    have h_a : m ≤ a := h a List.mem_cons_self
    have h_tail : ∀ d ∈ tail, m ≤ d :=
      fun d hd => h d (List.mem_cons_of_mem _ hd)
    have h_ih : tail.length * m ≤ tail.sum := ih h_tail
    -- Goal: (a :: tail).length * m ≤ (a :: tail).sum
    --     = (tail.length + 1) * m ≤ a + tail.sum
    simp only [List.sum_cons, List.length_cons]
    calc (tail.length + 1) * m
        = m + tail.length * m := by ring
      _ ≤ a + tail.sum := Nat.add_le_add h_a h_ih

/-- The natDegree of `prodFactors` is at least `factors.length` times
    the natDegree of `firstFactor`. Composes S3's `prodFactors_natDegree`
    (sum-of-degrees identity) with S13's `firstFactor_natDegree_minimal`
    (degree minimality among factors).

    Abstract counterpart of the matrix-level bound
    `k · deg(firstFactor M) ≤ deg(charpoly M)` (where `k` is the number
    of invariant factors and `firstFactor M` is the leading invariant
    divisor), the dual of S5's
    `prodFactors_natDegree_le_lastFactor_natDegree_mul`. Together with
    S5 gives a two-sided sandwich on `prodFactors.natDegree`. -/
theorem prodFactors_natDegree_ge_firstFactor_natDegree_mul
    (c : InvariantFactorChain F) (h : c.factors ≠ []) :
    c.factors.length * c.firstFactor.natDegree ≤ c.prodFactors.natDegree := by
  rw [prodFactors_natDegree]
  -- Goal: factors.length * firstFactor.natDegree ≤ (factors.map natDegree).sum
  have h_bound : ∀ d ∈ c.factors.map (·.natDegree),
      c.firstFactor.natDegree ≤ d := by
    intro d hd
    rw [List.mem_map] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    exact firstFactor_natDegree_minimal c h hp
  have h_sum :
      (c.factors.map (·.natDegree)).length * c.firstFactor.natDegree
        ≤ (c.factors.map (·.natDegree)).sum :=
    nat_list_sum_ge_length_mul_of_all_ge _ _ h_bound
  rwa [List.length_map] at h_sum

end MinpolyCharpolyOQ03
