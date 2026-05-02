/-
  Aristotle target for BallotProblemOQ03OQ01OQ01OQ01 (Jacobi-Trudi Identity)

  HARD bijection lemma: closes the b = 1 branch of `jdt_weight_sum`.

  ## Context

  In `BallotProblemOQ03OQ01OQ01OQ01.lean`, the private lemma `jdt_weight_sum n a b`
  (line 373) has one `sorry` (line 448) that covers the b ≥ 1 case. Extracting b = 1
  as a clean helper removes one branch of that sorry; the remaining b ≥ 2 case is
  the genuine frontier requiring the full JDT seam construction.

  Statement (b = 1):
    For a ≥ 1, the sum of pair-weights over non-col-strict (P, Q) pairs
    of shapes (a, 1) equals h_{a+1}.

  This is a known JDT-style identity that, combined with `Sym.oneEquiv`, reduces
  to a weight-preserving bijection
    ψ : {(P, q) : Sym n a × Fin n // q ≤ P.sort[0]} ≃ Sym (Fin n) (a + 1)
  with forward map (P, q) ↦ q ::ₛ P and inverse P' ↦ (P'.erase q', oneEquiv.symm q')
  where q' is the smallest element of P'.sort.

  ## Proof Recipe (verified Mathlib v4.26.0, session 14)

  Key lemmas — all confirmed present in current Mathlib:

  * `Sym.oneEquiv : α ≃ Sym α 1`   (Data/Sym/Basic.lean:477, @[simps apply])
      forward a ↦ ⟨{a}, _⟩
  * `Sym.cons_erase : a ::ₛ s.erase a h = s`   (Data/Sym/Basic.lean:219, simp)
  * `Sym.erase_cons_head : (a ::ₛ s).erase a _ = s`   (Data/Sym/Basic.lean:223, simp)
  * `Multiset.sort_cons` — `(∀ b ∈ s, r a b) → sort(a ::ₘ s) r = a :: sort s r`
      (Data/Multiset/Sort.lean:69)
  * `Multiset.prod_cons`, `Multiset.map_cons` — multiplicativity for weight preservation
  * `hsymm_zero : hsymm σ R 0 = 1`   (RingTheory/MvPolynomial/Symmetric/Defs.lean:318)

  ## Strategy outline (~80-100 lines expected)

  1. Set up Equiv between `{(P, Q : Sym n a × Sym n 1) // ¬ColStrictSym a 1 P Q}`
     and `{(P, q : Sym n a × Fin n) // q ≤ P.sort[0]}` via `Sym.oneEquiv` on Q.
     The negation of `ColStrictSym a 1` (with min a 1 = 1, given a ≥ 1) reduces to
     `P.sort[0] ≥ Q.sort[0]`, and `Q.sort[0] = q` when `Q = oneEquiv q`.

  2. Set up Equiv ψ between `{(P, q) // q ≤ P.sort[0]}` and `Sym (Fin n) (a + 1)`:
     forward (P, q) ↦ q ::ₛ P
     inverse P' ↦ ((P'.erase q' h, q')) where:
       L  := P'.1.sort (· ≤ ·)
       q' := L.head (List.length_pos_of_ne_nil ...) = smallest element of P'
       h  := List.head_mem  /  Multiset.sort_eq  to coerce q' ∈ P'.1
     Constraint q' ≤ (P'.erase q').sort[0] follows from sortedness of L:
       L = q' :: L.tail (List.head_cons_tail), so L.tail[0] = L[1] ≥ L[0] = q'.

  3. Show forward and inverse are mutual inverses using
     `Sym.cons_erase` and `Sym.erase_cons_head` simp lemmas.

  4. Weight preservation: under ψ,
       wt(P) * wt(Q)  =  (P.1.map X).prod * (oneEquiv q).1.map X .prod
                      =  (P.1.map X).prod * X q                          -- (oneEquiv q).1 = {q}
                      =  ((q ::ₘ P.1).map X).prod                        -- map_cons + prod_cons
                      =  wt(q ::ₛ P)
     so `Equiv.sum_comp ψ` finishes the equality with `∑ P', wt P' = hsymm (a+1)`.

  ## Status

  Aristotle target. Bijection-heavy proofs (cf. OQ-03-OQ-01-OQ-02 targets) have
  historically been challenging for Aristotle, but the recipe here is unusually
  concrete and the API symbols are all present. Worth submitting.

  If Aristotle solves this, the helper can be inlined into the b = 1 branch of
  `jdt_weight_sum` (~10 lines including hsymm_zero rewrite for the RHS).
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Multiset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Proofs.BallotProblemOQ03OQ01OQ01OQ01

open MvPolynomial Matrix Finset

namespace BallotProblemOQ03OQ01OQ01OQ01Aristotle

variable {R : Type*} [CommRing R]

/--
TARGET: jdt_weight_sum_b_one

The b = 1 specialization of the Jeu de Taquin weight sum identity. For a ≥ 1, the
sum of pair-weights over non-col-strict (P, Q) pairs of shapes (a, 1) equals h_{a+1}.

This is the helper that closes the b = 1 branch of `JacobiTrudi.jdt_weight_sum`.
**Status (2026-05-02):** The private lemma `jdt_weight_sum_b_one` in the main file
now proves this (via the same bijection construction). This companion target remains
as a standalone Aristotle submission for the standalone form.

Proof strategy: bijection
  ψ : {(P, Q) // ¬ColStrictSym a 1 P Q} ≃ Sym (Fin n) (a + 1)
via the chain
  {(P, Q) // ¬ColStrictSym} ≃ {(P, q) // q ≤ P.sort[0]} ≃ Sym (Fin n) (a + 1)
with weight preservation by `Multiset.map_cons` + `Multiset.prod_cons`.
-/
theorem jdt_weight_sum_b_one_Aristotle (n a : ℕ) (ha : 1 ≤ a) :
    ∑ PQ : { PQ : Sym (Fin n) a × Sym (Fin n) 1 //
              ¬ JacobiTrudi.ColStrictSym a 1 PQ.1 PQ.2 },
      (PQ.1.1.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod *
      (PQ.1.2.1.map (X : Fin n → MvPolynomial (Fin n) R)).prod =
    hsymm (Fin n) R (a + 1) := by
  sorry

end BallotProblemOQ03OQ01OQ01OQ01Aristotle
