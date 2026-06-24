/-
  Weighted (generating-function) Lindström–Gessel–Viennot — algebraic core
  (ballot-problem-oq-03-oq-02-oq-03)

  Open question inherited from the parent `ballot-problem-oq-03-oq-02`
  (the fully-proved general r×r LGV lemma `lgv_lemma_rxr`):

      "Extend to weighted lattice paths (generating function version of LGV)."

  In the weighted LGV lemma each lattice path `P` carries a weight `w(P)` in a
  commutative ring `R` (typically a monomial recording the path's steps), and the
  plain path count `e(Aᵢ, Bⱼ)` is replaced by the generating function
      `h(Aᵢ, Bⱼ) = Σ_{P : Aᵢ → Bⱼ} w(P)`.
  The theorem then reads
      `det[h(Aᵢ, Bⱼ)] = Σ_{(P₁,…,P_r) pairwise non-intersecting} ∏ᵢ w(Pᵢ)`,
  the Leibniz expansion's signed sum collapsing — by the Gessel–Viennot
  sign-reversing involution — to the non-intersecting families, which all occur
  with the identity permutation (sign `+1`).

  This file formalizes the **algebraic core** of that identity over an arbitrary
  commutative ring, *abstractly*: paths between source `i` and target `j` form an
  arbitrary finite type `Path i j`, and weights are arbitrary `R`-valued
  functions. The core identity is exactly the "generating function" half and is
  fully machine-checked:

      det H = Σ_σ sign(σ) • Σ_{f : ∏ᵢ Path i (σ i)} ∏ᵢ w(i, σ i, fᵢ).        (★)

  (★) is the column Leibniz expansion of the determinant (`Matrix.det_apply`
  after transpose) with each product of generating-function entries expanded into
  a sum over path families (`Finset.prod_sum`). Specializing every weight to `1`
  recovers the *counting* form `det = Σ_σ sign(σ) • #(σ-families)` used by the
  unweighted parent, so this genuinely generalizes it (`det_matrix_eq_signed_card_sum`).

  **What remains open** (the combinatorial core, recorded as `weighted_lgv` below):
  the sign-reversing involution showing the `σ ≠ 1` terms cancel against
  intersecting `σ = 1` families, leaving `det H = Σ_{non-intersecting families} ∏ w`.
  The involution is precisely the tail-swap of the unweighted development in
  `BallotProblemOQ03OQ02.lean`; it preserves the family's total multiset of steps
  and hence the product of weights, so the unweighted proof transfers once the
  weight-invariance of the tail swap is established. That step is left for a
  follow-up session and is *not* assumed anywhere in this file (no `axiom`, no
  `sorry`): everything below is the unconditional algebraic half.

  References:
  - Lindström, B. (1973). "On the vector representations of induced matroids."
  - Gessel, I. & Viennot, G. (1985). "Binomial determinants, paths, and hook
    length formulae." Adv. Math. 58, 300–321. (Weighted version, §2.)
  - Aigner, M. (2007). A Course in Enumeration, §5.4 (the generating-function LGV).
-/
import Mathlib

namespace BallotOQ03OQ02OQ03

open scoped BigOperators
open Equiv (Perm)

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Abstract weighted-path data for an `r × r` LGV configuration: for every
    source `i` and target `j`, a finite type `Path i j` of lattice paths together
    with a weight `weight i j : Path i j → R`.  This is the generating-function
    abstraction of an `LGVConfig`: a concrete configuration of lattice paths in a
    grid, with `weight` a monomial recording each path's steps, is one instance. -/
structure WeightedLGV (R : Type*) [CommRing R] (r : ℕ) where
  /-- The (finite) type of paths from source `i` to target `j`. -/
  Path : Fin r → Fin r → Type
  /-- Each path type is finite, so its generating function is a finite sum. -/
  [pathFintype : ∀ i j, Fintype (Path i j)]
  /-- The weight assigned to each path, valued in the ring `R`. -/
  weight : ∀ i j, Path i j → R

attribute [instance] WeightedLGV.pathFintype

namespace WeightedLGV

variable (W : WeightedLGV R r)

/-- The generating-function matrix `H i j = Σ_{P : i → j} w(P)`. -/
noncomputable def matrix : Matrix (Fin r) (Fin r) R :=
  Matrix.of fun i j => ∑ p : W.Path i j, W.weight i j p

/-- A `σ`-path family: a path `i → σ(i)` for every source `i`. -/
def Family (σ : Perm (Fin r)) : Type := ∀ i, W.Path i (σ i)

noncomputable instance instFintypeFamily (σ : Perm (Fin r)) :
    Fintype (W.Family σ) := by unfold Family; infer_instance

/-- The weight of a `σ`-path family is the product of its individual path
    weights. -/
noncomputable def familyWeight {σ : Perm (Fin r)} (f : W.Family σ) : R :=
  ∏ i, W.weight i (σ i) (f i)

/-- **Generating-function LGV, algebraic core.** The determinant of the
    generating-function matrix `H` equals the signed sum, over all permutations
    `σ`, of the generating function of `σ`-path families.

    This is the unconditional algebraic half of the weighted LGV lemma: the
    Leibniz expansion of `det H` with each entry's generating function expanded
    into a sum over path families. The combinatorial collapse to non-intersecting
    families (the Gessel–Viennot involution) is the remaining open core. -/
theorem det_matrix_eq_signed_family_sum :
    W.matrix.det =
      ∑ σ : Perm (Fin r), Equiv.Perm.sign σ • ∑ f : W.Family σ, W.familyWeight f := by
  -- Use the column form of Leibniz: det H = det Hᵀ = Σ_σ sign σ • ∏ i, H i (σ i).
  rw [← Matrix.det_transpose W.matrix, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  -- ∏ i, Hᵀ (σ i) i = ∏ i, H i (σ i) = ∏ i, ∑ p, w i (σ i) p
  simp only [Matrix.transpose_apply, matrix, Matrix.of_apply, familyWeight, Family]
  -- A product of sums is a sum of products over the pi type = Family σ.
  rw [Fintype.prod_sum]

/-- Specialising every weight to `1`, the algebraic core reduces to the
    *counting* form of the determinant expansion used by the unweighted parent:
    `det H = Σ_σ sign(σ) • #(σ-families)`, where now `H i j = #(Path i j)`. This
    shows the weighted statement genuinely generalises the unweighted one. -/
theorem det_matrix_eq_signed_card_sum
    (W : WeightedLGV R r) (hw : ∀ i j p, W.weight i j p = 1) :
    W.matrix.det =
      ∑ σ : Perm (Fin r),
        Equiv.Perm.sign σ • (Fintype.card (W.Family σ) : R) := by
  rw [det_matrix_eq_signed_family_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  -- Each family weight is a product of 1's = 1, so the sum counts the families.
  have : ∀ f : W.Family σ, W.familyWeight f = 1 := by
    intro f; simp only [familyWeight, hw, Finset.prod_const_one]
  rw [Finset.sum_congr rfl fun f _ => this f]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- A `σ`-path family is **non-intersecting** when, regarded as a tuple of paths
    with path `i` running `i → σ(i)`, no two of its paths share a lattice point.
    (Abstract placeholder predicate: a concrete instance supplies the lattice
    geometry; for the identity permutation this is the usual non-intersection of
    an `r`-tuple of paths.) The full weighted LGV lemma asserts that only the
    identity-permutation non-intersecting families survive the signed sum. -/
def IsNonIntersecting {σ : Perm (Fin r)} (_ : W.Family σ) : Prop := True

end WeightedLGV

open Classical in
/-- **The weighted (generating-function) LGV lemma — open goal of this entry.**

    Over a commutative ring `R`, the determinant of the generating-function
    matrix equals the (necessarily positive-sign) generating function of the
    *non-intersecting* identity-permutation path families:
        `det H = Σ_{f : Family 1, non-intersecting} ∏ᵢ w(fᵢ)`.

    The algebraic half `det_matrix_eq_signed_family_sum` reduces this to the
    Gessel–Viennot sign-reversing involution (tail swap), which pairs each
    intersecting or non-identity family with an opposite-sign partner of equal
    weight. That involution — proved unweighted in `BallotProblemOQ03OQ02.lean`
    via `gv_involution_cancellation`/`lgv_lemma_rxr` — must be shown to preserve
    `familyWeight` (the tail swap permutes the steps among paths but preserves
    their total multiset, hence the product of monomial weights). This statement
    is recorded for downstream work and is deliberately *not* proved or assumed
    here; nothing in this file depends on it. -/
def WeightedLGVConjecture (R : Type*) [CommRing R] (r : ℕ) : Prop :=
  ∀ W : WeightedLGV R r,
    W.matrix.det =
      ∑ f : W.Family 1, if WeightedLGV.IsNonIntersecting W f then W.familyWeight f else 0

end BallotOQ03OQ02OQ03
