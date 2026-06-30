/-
# Joint Independence of Disjoint Subsets in the Binomial Model

*Open Question from BinomialTheoremOQ02OQ01OQ02* (Marginal Distributions of
Multinomial Are Binomial): in the binomial model — a family of independent
Bernoulli indicators (Xᵢ)ᵢ — are the block-sums over **disjoint** index subsets
jointly independent?

## What This Proves

The binomial random variable Binomial(n, p) is the sum of n independent
Bernoulli(p) indicators. For disjoint index subsets S, T the partial sums
U = ∑_{i∈S} Xᵢ and V = ∑_{i∈T} Xᵢ are independent, and each is itself a
Binomial (of size |S| resp. |T|).

Following the **probability generating function (PGF)** methodology of the parent
file, we encode this through factorization of the joint PGF. For independent
indicators the joint PGF is the product of the per-index Bernoulli PGFs

    bernoulliPGF p t = (1 - p) + p · t = E[t^X],   X ~ Bernoulli(p).

The two results that make "joint independence" precise in this framework:

1. `jointPGF_union` — the joint PGF over a disjoint union `S ∪ T` factors as the
   product of the block PGFs. This is the generating-function certificate that
   the two blocks are jointly independent (the joint transform separates).

2. `disjoint_blocks_pgf` — specialising to the homogeneous binomial parameter
   `p` and assigning formal variable `u` to block `S` and `v` to block `T`, the
   bivariate PGF of `(U, V)` factors as

       E[u^U v^V] = ((1-p) + p·u)^|S| · ((1-p) + p·v)^|T| = E[u^U] · E[v^V],

   with each factor the PGF of a Binomial. The clean separation into a
   `u`-function times a `v`-function is exactly the PGF independence criterion,
   and each factor being a binomial PGF gives the marginals.

Supporting normalisation lemmas (`bernoulliPGF_one`, `jointPGF_one`) confirm
these are genuine PGFs: evaluating all variables at `1` returns total
probability `1`.

## Mathlib Dependencies

- `Finset.prod_union`   : products split over disjoint unions
- `Finset.prod_const`   : product of a constant = constant ^ card
- `Finset.prod_congr`   : rewrite a product factorwise
- `Finset.disjoint_right`, `Finset.prod_eq_one`

## Scope

The PGF factorization is the standard generating-function certificate of
independence; we prove the factorization rigorously. We do not re-derive the
measure-theoretic PGF ⇒ independence equivalence (not part of this combinatorial
chain).
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace BinomialTheoremOQ02OQ01OQ02OQ01

open Finset BigOperators

/-! ## Setup: Bernoulli and joint generating functions -/

/-- The probability generating function of a single `Bernoulli(p)` indicator:
`E[t^X] = (1 - p) + p · t`. -/
noncomputable def bernoulliPGF (p t : ℝ) : ℝ := (1 - p) + p * t

/-- The joint generating function of independent Bernoulli indicators
`(Xᵢ)_{i ∈ s}`, each with success probability `p i`, evaluated at the formal
variables `t i`:  `E[∏ᵢ tᵢ^{Xᵢ}] = ∏ᵢ ((1 - pᵢ) + pᵢ · tᵢ)`. -/
noncomputable def jointPGF {α : Type*} (s : Finset α) (p t : α → ℝ) : ℝ :=
  ∏ i ∈ s, bernoulliPGF (p i) (t i)

/-! ## Normalisation: these are genuine PGFs -/

/-- A Bernoulli PGF evaluated at `1` is `1` (probabilities sum to one). -/
theorem bernoulliPGF_one (p : ℝ) : bernoulliPGF p 1 = 1 := by
  unfold bernoulliPGF; ring

/-- The joint PGF evaluated at all variables `= 1` is `1`. -/
theorem jointPGF_one {α : Type*} (s : Finset α) (p : α → ℝ) :
    jointPGF s p (fun _ => 1) = 1 := by
  unfold jointPGF
  apply Finset.prod_eq_one
  intro i _
  exact bernoulliPGF_one (p i)

/-! ## Part I: Joint independence via PGF factorization

For independent indicators the joint PGF over a disjoint union of index sets
factors as the product of the block PGFs. This separation of the joint transform
is the generating-function certificate of joint independence.
-/

/-- **Joint independence of disjoint blocks.** The joint PGF over a disjoint
union `S ∪ T` factors as the product of the two block PGFs. -/
theorem jointPGF_union {α : Type*} [DecidableEq α] (S T : Finset α) (p t : α → ℝ)
    (h : Disjoint S T) :
    jointPGF (S ∪ T) p t = jointPGF S p t * jointPGF T p t := by
  unfold jointPGF
  exact Finset.prod_union h

/-! ## Part II: Each block is a Binomial PGF (homogeneous parameter)

With a common success probability `p` and a common formal variable `u`, the
block PGF over `s` collapses to the Binomial PGF `((1-p) + p·u)^|s|`.
-/

/-- The joint PGF of `|s|` i.i.d. `Bernoulli(p)` indicators at a common variable
`u` is the Binomial PGF `((1-p) + p·u)^|s|`. -/
theorem jointPGF_const {α : Type*} (s : Finset α) (p u : ℝ) :
    jointPGF s (fun _ => p) (fun _ => u) = bernoulliPGF p u ^ s.card := by
  unfold jointPGF
  rw [Finset.prod_const]

/-! ## Part III: Bivariate block PGF factorizes into two Binomial PGFs

Assign formal variable `u` to block `S` and `v` to the disjoint block `T`. The
bivariate PGF of `(U, V) = (∑_{i∈S} Xᵢ, ∑_{i∈T} Xᵢ)` separates as a function of
`u` times a function of `v`, each a Binomial PGF — the precise statement that the
two block-sums are independent Binomials.
-/

/-- **Disjoint block-sums are independent Binomials.** The bivariate PGF
`E[u^U v^V]` of the two disjoint block-sums factors as
`((1-p) + p·u)^|S| · ((1-p) + p·v)^|T|`, i.e. into a `u`-part times a `v`-part,
each the PGF of a Binomial. -/
theorem disjoint_blocks_pgf {α : Type*} [DecidableEq α] (S T : Finset α)
    (p u v : ℝ) (h : Disjoint S T) :
    (∏ i ∈ S ∪ T, bernoulliPGF p (if i ∈ S then u else v))
      = bernoulliPGF p u ^ S.card * bernoulliPGF p v ^ T.card := by
  rw [Finset.prod_union h]
  congr 1
  · -- block S: every `i ∈ S` selects `u`
    rw [Finset.prod_congr rfl (fun i hi => by rw [if_pos hi]), Finset.prod_const]
  · -- block T: every `i ∈ T` is outside `S` (disjointness), so selects `v`
    rw [Finset.prod_congr rfl
          (fun i hi => by rw [if_neg (Finset.disjoint_right.mp h hi)]),
        Finset.prod_const]

end BinomialTheoremOQ02OQ01OQ02OQ01
