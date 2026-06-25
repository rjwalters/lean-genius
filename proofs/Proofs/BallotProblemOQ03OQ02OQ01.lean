/-
  Weighted (generating-function) Lindström–Gessel–Viennot —
  multiplicativity of the LGV determinant under path-system composition
  (ballot-problem-oq-03-oq-02-oq-01)

  Open question inherited from the parent `ballot-problem-oq-03-oq-02` (the
  fully-proved general r×r LGV lemma `lgv_lemma_rxr`) and its weighted sibling
  `ballot-problem-oq-03-oq-02-oq-03` (the algebraic core
  `det_matrix_eq_signed_family_sum`):

      "Connect to applications via the product structure of LGV determinants."

  Many of the headline applications of the Lindström–Gessel–Viennot lemma —
  Schur polynomials via Jacobi–Trudi, MacMahon's box formula for plane
  partitions, the `2^{n(n+1)/2}` count of Aztec-diamond tilings — ultimately
  rest on a single algebraic fact: the LGV generating-function determinant is
  **multiplicative under composition of path systems**.  If lattice paths from a
  source `i` to a sink `j` are built by first running a path through an
  intermediate layer (`i → k`) and then a second path out of it (`k → j`), with
  the weight of the concatenation the product of the two weights, then the
  generating-function matrix of the composite system is the *matrix product* of
  the two layers' generating-function matrices:

      H(W₁ ∘ W₂) = H(W₁) · H(W₂),                                            (★)

  and therefore, by the Cauchy–Binet/`det_mul` law,

      det H(W₁ ∘ W₂) = det H(W₁) · det H(W₂).                               (★★)

  This file formalizes (★) and (★★) abstractly over an arbitrary commutative
  ring, reusing the `WeightedLGV` abstraction of the sibling entry: paths between
  a source `i` and a target `j` form an arbitrary finite type `Path i j`, and
  weights are arbitrary `R`-valued functions.  The composite system `comp W₁ W₂`
  has path type `Σ k, Path₁ i k × Path₂ k j` (choose the intermediate sink `k`,
  then a first- and second-layer path) with multiplicative weight; the single
  entry identity is the distributive law `Fintype.sum_mul_sum` summed over the
  intermediate layer.

  We additionally derive:
    * `det_comp_list`  — det multiplicativity for an arbitrary *list* of stacked
      layers, `det H(W₁ ∘ ⋯ ∘ Wₙ) = ∏ det H(Wᵢ)` (the iterated product law that
      underlies multi-layer LGV product formulas), and
    * `comp_card_matrix` / `det_comp_signed_family_sum` — the unweighted counting
      specialization and the bridge back to the sibling's signed family-sum core.

  Everything is unconditional and fully machine-checked: no `axiom`, no `sorry`.
  The combinatorial Gessel–Viennot collapse to non-intersecting families is *not*
  needed here — multiplicativity is a statement about the determinants alone.

  References:
  - Lindström, B. (1973). "On the vector representations of induced matroids."
  - Gessel, I. & Viennot, G. (1985). "Binomial determinants, paths, and hook
    length formulae." Adv. Math. 58, 300–321.
  - Aigner, M. (2007). A Course in Enumeration, §5.4 (generating-function LGV).
  - Stanley, R. (1999). Enumerative Combinatorics, Vol. 2, §2.7 (LGV and
    transfer-matrix products).
-/
import Mathlib
import Proofs.BallotProblemOQ03OQ02OQ03

namespace BallotOQ03OQ02OQ01

open scoped BigOperators
open Equiv (Perm)
open BallotOQ03OQ02OQ03 (WeightedLGV)

variable {R : Type*} [CommRing R] {r : ℕ}

/-- **Composition of two weighted path systems.**  A composite path from source
    `i` to sink `j` is a choice of an intermediate sink `k`, a first-layer path
    `i → k` of `W₁`, and a second-layer path `k → j` of `W₂`.  Its weight is the
    product of the two constituent weights.  This is the generating-function
    abstraction of "concatenate a path through an intermediate lattice layer". -/
noncomputable def comp (W₁ W₂ : WeightedLGV R r) : WeightedLGV R r where
  Path i j := Σ k, W₁.Path i k × W₂.Path k j
  pathFintype i j := inferInstance
  weight i j := fun x => W₁.weight i x.1 x.2.1 * W₂.weight x.1 j x.2.2

@[inherit_doc] scoped infixl:70 " ∘w " => comp

/-- **The generating-function matrix is multiplicative (★).**  The matrix of a
    composite path system is the ordinary matrix product of the two layers'
    generating-function matrices: `H(W₁ ∘ W₂) = H(W₁) · H(W₂)`.

    Entrywise this is the distributive law
    `(Σ_p w₁ p)(Σ_q w₂ q) = Σ_{(p,q)} w₁ p · w₂ q`, summed over the choice of the
    intermediate sink `k`. -/
theorem comp_matrix (W₁ W₂ : WeightedLGV R r) :
    (W₁ ∘w W₂).matrix = W₁.matrix * W₂.matrix := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [comp, WeightedLGV.matrix, Matrix.of_apply]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.sum_prod_type, Fintype.sum_mul_sum]

/-- **Multiplicativity of the LGV determinant (★★).**  The determinant of the
    composite generating-function matrix is the product of the two layers'
    determinants:
        `det H(W₁ ∘ W₂) = det H(W₁) · det H(W₂)`.
    This is the algebraic engine behind the product formulas obtained from LGV
    (Schur polynomials, MacMahon's box formula, Aztec-diamond tilings): a
    multi-layer non-intersecting-path count factors as a product of single-layer
    determinants. -/
theorem det_comp (W₁ W₂ : WeightedLGV R r) :
    (W₁ ∘w W₂).matrix.det = W₁.matrix.det * W₂.matrix.det := by
  rw [comp_matrix, Matrix.det_mul]

/-- Composition is commutative *at the level of determinants*: stacking the two
    layers in either order yields the same LGV determinant (the underlying
    matrices need not commute, but their determinants do). -/
theorem det_comp_comm (W₁ W₂ : WeightedLGV R r) :
    (W₁ ∘w W₂).matrix.det = (W₂ ∘w W₁).matrix.det := by
  rw [det_comp, det_comp, mul_comm]

/-- **Iterated multiplicativity for a stack of layers.**  Folding composition
    over a list `Ws` of weighted path systems (with a base layer `W₀`) yields a
    determinant equal to the product of all the individual determinants:
        `det H(W₁ ∘ ⋯ ∘ Wₙ ∘ W₀) = (∏ᵢ det H(Wᵢ)) · det H(W₀)`.
    This is the multi-layer LGV product law: a transfer-matrix stack of length
    `n` has LGV determinant equal to the product of its `n` single-step
    determinants. -/
theorem det_comp_list (W₀ : WeightedLGV R r) (Ws : List (WeightedLGV R r)) :
    (Ws.foldr comp W₀).matrix.det
      = (Ws.map (fun W => W.matrix.det)).prod * W₀.matrix.det := by
  induction Ws with
  | nil => simp
  | cons W Ws ih =>
      simp only [List.foldr_cons, List.map_cons, List.prod_cons]
      rw [det_comp, ih]; ring

/-- The composite of two *unweighted* systems (every weight `1`) again counts
    paths: its generating-function matrix is the number of length-two
    concatenated paths,
    `H(W₁ ∘ W₂) i j = #(Σ k, Path₁ i k × Path₂ k j)`. -/
theorem comp_card_matrix (W₁ W₂ : WeightedLGV R r)
    (h₁ : ∀ i j p, W₁.weight i j p = 1) (h₂ : ∀ i j p, W₂.weight i j p = 1)
    (i j : Fin r) :
    (W₁ ∘w W₂).matrix i j
      = (Fintype.card (Σ k, W₁.Path i k × W₂.Path k j) : R) := by
  simp only [WeightedLGV.matrix, Matrix.of_apply, comp, h₁, h₂, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Bridge to the sibling's algebraic core.**  Combining multiplicativity with
    the sibling entry's Leibniz/family expansion `det_matrix_eq_signed_family_sum`,
    the composite determinant is the *product* of two signed family sums — making
    explicit that each layer contributes its own signed sum over path families. -/
theorem det_comp_signed_family_sum (W₁ W₂ : WeightedLGV R r) :
    (W₁ ∘w W₂).matrix.det =
      (∑ σ : Perm (Fin r), Equiv.Perm.sign σ • ∑ f : W₁.Family σ, W₁.familyWeight f) *
      (∑ τ : Perm (Fin r), Equiv.Perm.sign τ • ∑ g : W₂.Family τ, W₂.familyWeight g) := by
  rw [det_comp, W₁.det_matrix_eq_signed_family_sum, W₂.det_matrix_eq_signed_family_sum]

end BallotOQ03OQ02OQ01
