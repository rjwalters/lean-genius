import Proofs.Erdos85EvenExcessOneDefectKernel
import Proofs.Erdos85AdjacencyCharpolySquareModTwo
import Proofs.Erdos85ComponentFactorization
import Proofs.Erdos85ComponentLocalObstruction
import Proofs.Erdos85QuotientGramIdentity
import Proofs.Erdos85ExcessEigenspace
import Proofs.Erdos85ResidueSignedCount

/-!
# Characteristic-two parity for regular square-order cores

The mod-two defect-kernel argument is not peculiar to the order-64 endpoint
or to the excess-one order.  On any even square order, an even-regular
`C₄`-free graph has a second adjacency-kernel vector, hence the same
nonconstant vector lies in the kernel of `I + J + D`.  This is the uniform parity input for the
regular binary square-order branch.
-/

open SimpleGraph

namespace Erdos85

/-- **Uniform binary-square defect kernel.**  Let `G` be an even-regular
`C₄`-free graph on `q²` vertices, with `q > 0`.  Over `𝔽₂`, the matrix
`A` has a kernel vector distinct from both zero and the all-ones vector, and
that same vector is killed by `I + J + D`.

The proof uses only that `q²` is even.  Thus every hypothetical regular core
in the characteristic-two square-order branch carries this extra parity
structure, independently of any finite component census. -/
theorem binarySquare_regular_exists_nontrivial_defect_kernel_vector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q) (heven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    ∃ w : V → ZMod 2, w ≠ 0 ∧ w ≠ (fun _ => 1) ∧
      (G.adjMatrix (ZMod 2)).mulVec w = 0 ∧
      ((1 : Matrix V V (ZMod 2)) + Matrix.of (fun _ _ => (1 : ZMod 2)) +
        (secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec w = 0 := by
  haveI : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]
    positivity
  have hnEven : Even (Fintype.card V) := by
    obtain ⟨k, hk⟩ := heven
    refine ⟨k * q, ?_⟩
    rw [hcard, hk]
    ring
  have hsymm : ∀ x y : V,
      G.adjMatrix (ZMod 2) x y = G.adjMatrix (ZMod 2) y x := by
    intro x y
    simp only [SimpleGraph.adjMatrix_apply]
    by_cases h : G.Adj x y
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hdiag : ∀ x : V, G.adjMatrix (ZMod 2) x x = 0 := by
    intro x
    rw [SimpleGraph.adjMatrix_apply, if_neg (G.loopless.irrefl x)]
  have hones := adjMatrix_zmodTwo_mulVec_ones_eq_zero G heven hreg
  obtain ⟨w, hker, hw0, hw1⟩ := exists_kernel_vector_ne_zero_ne_ones
    hnEven (G.adjMatrix (ZMod 2)) hsymm hdiag hones
  refine ⟨w, hw0, hw1, hker, ?_⟩
  rw [← adjMatrix_sq_eq_defect_mod_two_of_even_regular G hfree heven hreg,
    ← Matrix.mulVec_mulVec, hker, Matrix.mulVec_zero]

/-- **Coupled parity-set form.**  Under the same binary square-order
hypotheses, there is a proper nonempty vertex set `W` such that every vertex
has an even number of `G`-neighbors in `W`, while its defect neighborhood
satisfies the parity forced by membership in `W` and by `|W|`.

This is the combinatorial interface intended for component and Gram arguments:
it remembers both halves of the coupled kernel statement without mentioning
matrix-vector multiplication. -/
theorem binarySquare_regular_exists_coupled_parity_set
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 0 < q) (heven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    ∃ W : Finset V, W ≠ ∅ ∧ W ≠ Finset.univ ∧
      (∀ v : V, (((G.neighborFinset v ∩ W).card : ZMod 2)) = 0) ∧
      (∀ v : V,
        (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
          ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card : ZMod 2))
            = 0) := by
  obtain ⟨w, hw0, hw1, hA, hDker⟩ :=
    binarySquare_regular_exists_nontrivial_defect_kernel_vector
      G hfree hq heven hreg hcard
  set W : Finset V := Finset.univ.filter (fun v => w v = 1) with hWdef
  have hmem : ∀ v, v ∈ W ↔ w v = 1 := by
    intro v
    simp [hWdef]
  have hval : ∀ v, w v = if v ∈ W then (1 : ZMod 2) else 0 := by
    intro v
    by_cases h : v ∈ W
    · rw [if_pos h]
      exact (hmem v).mp h
    · rw [if_neg h]
      have hne : w v ≠ 1 := fun hc => h ((hmem v).mpr hc)
      have hcases : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide
      exact hcases _ hne
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro hW
    apply hw0
    funext v
    rw [Pi.zero_apply, hval v, hW]
    simp
  · intro hW
    apply hw1
    funext v
    rw [hval v, hW]
    simp
  · intro v
    have hcomp := congrFun hA v
    rw [Matrix.mulVec, dotProduct] at hcomp
    simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul] at hcomp
    rw [← Finset.sum_filter] at hcomp
    have hfilt : Finset.univ.filter (fun u => G.Adj v u) =
        G.neighborFinset v := by
      ext u
      simp [SimpleGraph.mem_neighborFinset]
    rw [hfilt] at hcomp
    calc
      (((G.neighborFinset v ∩ W).card : ZMod 2)) =
          ∑ u ∈ G.neighborFinset v,
            (if u ∈ W then (1 : ZMod 2) else 0) := by
        symm
        rw [Finset.sum_boole, Finset.filter_mem_eq_inter]
      _ = ∑ u ∈ G.neighborFinset v, w u :=
        Finset.sum_congr rfl fun u _ => (hval u).symm
      _ = 0 := by simpa using hcomp
  · intro v
    have hcomp := congrFun hDker v
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] at hcomp
    simp only [Pi.add_apply, Pi.zero_apply] at hcomp
    have hJ : ((Matrix.of (fun _ _ => (1 : ZMod 2))).mulVec w) v =
        (W.card : ZMod 2) := by
      rw [Matrix.mulVec, dotProduct]
      simp only [Matrix.of_apply, one_mul]
      calc
        ∑ u, w u = ∑ u, (if u ∈ W then (1 : ZMod 2) else 0) :=
          Finset.sum_congr rfl fun u _ => hval u
        _ = ((Finset.univ.filter (· ∈ W)).card : ZMod 2) := by
          rw [Finset.sum_boole]
        _ = (W.card : ZMod 2) := by rw [Finset.filter_univ_mem]
    have hD :
        (((secondOrderDefectGraph G).adjMatrix (ZMod 2)).mulVec w) v =
          ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
            ZMod 2)) := by
      rw [Matrix.mulVec, dotProduct]
      simp only [SimpleGraph.adjMatrix_apply, ite_mul, one_mul, zero_mul]
      rw [← Finset.sum_filter]
      have hfilt : Finset.univ.filter
          (fun u => (secondOrderDefectGraph G).Adj v u) =
          (secondOrderDefectGraph G).neighborFinset v := by
        ext u
        simp [SimpleGraph.mem_neighborFinset]
      rw [hfilt]
      calc
        ∑ u ∈ (secondOrderDefectGraph G).neighborFinset v, w u =
            ∑ u ∈ (secondOrderDefectGraph G).neighborFinset v,
              (if u ∈ W then (1 : ZMod 2) else 0) :=
          Finset.sum_congr rfl fun u _ => hval u
        _ = ((((secondOrderDefectGraph G).neighborFinset v).filter
            (· ∈ W)).card : ZMod 2) := by
          rw [Finset.sum_boole]
        _ = ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
            ZMod 2)) := by
          rw [Finset.filter_mem_eq_inter]
    rw [hJ, hD] at hcomp
    rw [← hval v]
    exact hcomp

/-- On an even square order, the mod-two characteristic polynomial of the
second-order defect graph is a square.  No transfer through the adjacency
square identity is needed: the defect graph is itself a simple graph on the
same even vertex type. -/
theorem binarySquare_defect_charpoly_isSquare_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    {q : ℕ} (heven : Even q) (hcard : Fintype.card V = q * q) :
    ∃ p : Polynomial (ZMod 2),
      ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).charpoly = p ^ 2 := by
  apply adjMatrix_charpoly_isSquare_zmodTwo
  obtain ⟨k, hk⟩ := heven
  refine ⟨k * q, ?_⟩
  rw [hcard, hk]
  ring

/-- Every normalized polynomial factor occurs with even valuation in the
mod-two defect characteristic polynomial at an even square order. -/
theorem binarySquare_defect_charpoly_factorization_even_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    {q : ℕ} (heven : Even q) (hcard : Fintype.card V = q * q)
    (r : Polynomial (ZMod 2)) :
    Even (factorization
      ((secondOrderDefectGraph G).adjMatrix (ZMod 2)).charpoly r) := by
  obtain ⟨p, hp⟩ :=
    binarySquare_defect_charpoly_isSquare_zmodTwo G heven hcard
  exact factorization_even_of_eq_sq hp r

/-- Componentwise form of the mod-two factor parity: for each polynomial
factor, the sum of its valuations in the induced defect-component
characteristic polynomials is even. -/
theorem binarySquare_sum_defectComponent_charpoly_factorization_even_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    {q : ℕ} (heven : Even q) (hcard : Fintype.card V = q * q)
    (r : Polynomial (ZMod 2)) :
    Even (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      factorization
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix
          (ZMod 2)).charpoly r) := by
  rw [← adjMatrix_charpoly_factorization_eq_sum_connectedComponents]
  exact binarySquare_defect_charpoly_factorization_even_zmodTwo
    G heven hcard r

/-- In a regular even square-order candidate, every defect component has even
order.  Indeed the defect graph is `(q-1)`-regular, hence odd-regular, and the
handshaking lemma applies inside each connected component. -/
theorem binarySquare_regular_defectComponent_card_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (heven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    Even (Fintype.card c.supp) := by
  let D := secondOrderDefectGraph G
  let H := D.induce c.supp
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdegree : ∀ x : V, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    change D.degree x = q - 1
    omega
  have hHdegree : ∀ x : c.supp, H.degree x = q - 1 := by
    intro x
    rw [degree_induce_connectedComponent_supp D c x]
    exact hDdegree x.1
  have hqpredOdd : Odd (q - 1) := by
    obtain ⟨k, hk⟩ := heven
    refine ⟨k - 1, ?_⟩
    omega
  have hhandshake := H.even_card_odd_degree_vertices
  simpa [hHdegree, hqpredOdd] using hhandshake

/-- Consequently, each defect component characteristic polynomial is already
a square modulo two individually.  This shows that global component-factor
parity cannot by itself be the missing regular-sector contradiction. -/
theorem binarySquare_regular_defectComponent_charpoly_isSquare_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (heven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    ∃ p : Polynomial (ZMod 2),
      (((secondOrderDefectGraph G).induce c.supp).adjMatrix
        (ZMod 2)).charpoly = p ^ 2 := by
  apply adjMatrix_charpoly_isSquare_zmodTwo
  exact binarySquare_regular_defectComponent_card_even
    G hfree hq heven hreg hcard c

/-- **Uniform binary-square weighted quotient Gram identity.**  In a regular
square-order candidate, the defect graph has degree `q-1` and commutes with
the ambient adjacency operator.  Therefore distinct defect components `c,c'`
satisfy the exact weighted quotient inner-product law below. -/
theorem binarySquare_regular_componentQuotient_weightedGram_offDiagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c c' : (secondOrderDefectGraph G).ConnectedComponent) (hne : c ≠ c') :
    (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
        e.supp.ncard *
          (componentQuotientMatrix G (secondOrderDefectGraph G) e c *
            componentQuotientMatrix G (secondOrderDefectGraph G) e c')) =
      c.supp.ncard * c'.supp.ncard := by
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdegree : ∀ x : V,
      (secondOrderDefectGraph G).degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change (secondOrderDefectGraph G).degree x = (q - 3) + 2 at h
    omega
  have hcomm : G.adjMatrix ℝ * (secondOrderDefectGraph G).adjMatrix ℝ =
      (secondOrderDefectGraph G).adjMatrix ℝ * G.adjMatrix ℝ :=
    adjMatrix_comm_secondOrderDefect_of_regular_field G hfree hreg
  exact sum_ncard_mul_componentQuotient_eq_of_ne_of_regular_comm
    G hfree hDdegree hcomm c c' hne

/-- **Uniform binary-square weighted quotient Gram diagonal.**  Detailed
balance converts the weighted column norm into the diagonal entry of `Q²`.
At square order the scalar part of the transported defect identity cancels,
so this norm is exactly the square of the component order. -/
theorem binarySquare_regular_componentQuotient_weightedGram_diagonal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
        (e.supp.ncard : ℝ) *
          ((componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℝ) *
            (componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℝ))) =
      (c.supp.ncard : ℝ) * (c.supp.ncard : ℝ) := by
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdegree : ∀ x : V,
      (secondOrderDefectGraph G).degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change (secondOrderDefectGraph G).degree x = (q - 3) + 2 at h
    omega
  have hcomm : G.adjMatrix ℝ * (secondOrderDefectGraph G).adjMatrix ℝ =
      (secondOrderDefectGraph G).adjMatrix ℝ * G.adjMatrix ℝ :=
    adjMatrix_comm_secondOrderDefect_of_regular_field G hfree hreg
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  have hsq := componentQuotientMatrixReal_sq_apply_of_regular_comm
    G hfree hreg hDdegree hcomm c c
  have hcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    norm_num
  rw [hcast] at hsq
  have hsq' : (∑ e, (Q c e : ℝ) * (Q e c : ℝ)) =
      (c.supp.ncard : ℝ) := by
    simpa [Matrix.mul_apply, componentQuotientMatrixReal, D, Q] using hsq
  calc
    (∑ e : D.ConnectedComponent,
        (e.supp.ncard : ℝ) * ((Q e c : ℝ) * (Q e c : ℝ))) =
        ∑ e : D.ConnectedComponent,
          (c.supp.ncard : ℝ) * ((Q c e : ℝ) * (Q e c : ℝ)) := by
      apply Finset.sum_congr rfl
      intro e _
      have hbal := componentQuotientMatrix_balance
        G D (q - 1) hDdegree hcomm c e
      have hbalR : (c.supp.ncard : ℝ) * (Q c e : ℝ) =
          (e.supp.ncard : ℝ) * (Q e c : ℝ) := by
        exact_mod_cast hbal
      rw [← mul_assoc, ← hbalR]
      ring
    _ = (c.supp.ncard : ℝ) *
        ∑ e : D.ConnectedComponent, (Q c e : ℝ) * (Q e c : ℝ) := by
      rw [Finset.mul_sum]
    _ = (c.supp.ncard : ℝ) * (c.supp.ncard : ℝ) := by rw [hsq']

/-- The diagonal and off-diagonal formulas combine into the full weighted
Gram identity. -/
theorem binarySquare_regular_componentQuotient_weightedGram
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c c' : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
        (e.supp.ncard : ℝ) *
          ((componentQuotientMatrix G (secondOrderDefectGraph G) e c : ℝ) *
            (componentQuotientMatrix G (secondOrderDefectGraph G) e c' : ℝ))) =
      (c.supp.ncard : ℝ) * (c'.supp.ncard : ℝ) := by
  by_cases hcc' : c = c'
  · subst c'
    exact binarySquare_regular_componentQuotient_weightedGram_diagonal
      G hfree hq hreg hcard c
  · exact_mod_cast binarySquare_regular_componentQuotient_weightedGram_offDiagonal
      G hfree hq hreg hcard c c' hcc'

/-- **Rank-one consumer.**  Equality in the full weighted Gram identity
forces every two quotient columns to be proportional after scaling by their
component orders. -/
theorem binarySquare_regular_componentQuotient_cross_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e c c' : (secondOrderDefectGraph G).ConnectedComponent) :
    c'.supp.ncard *
        componentQuotientMatrix G (secondOrderDefectGraph G) e c =
      c.supp.ncard *
        componentQuotientMatrix G (secondOrderDefectGraph G) e c' := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  have hcc := binarySquare_regular_componentQuotient_weightedGram
    G hfree hq hreg hcard c c
  have hcc' := binarySquare_regular_componentQuotient_weightedGram
    G hfree hq hreg hcard c' c'
  have hcross := binarySquare_regular_componentQuotient_weightedGram
    G hfree hq hreg hcard c c'
  have hsum : (∑ x : D.ConnectedComponent,
      (x.supp.ncard : ℝ) *
        ((c'.supp.ncard : ℝ) * (Q x c : ℝ) -
          (c.supp.ncard : ℝ) * (Q x c' : ℝ)) ^ 2) = 0 := by
    calc
      (∑ x : D.ConnectedComponent,
          (x.supp.ncard : ℝ) *
            ((c'.supp.ncard : ℝ) * (Q x c : ℝ) -
              (c.supp.ncard : ℝ) * (Q x c' : ℝ)) ^ 2) =
          (c'.supp.ncard : ℝ) ^ 2 *
              (∑ x : D.ConnectedComponent,
                (x.supp.ncard : ℝ) * ((Q x c : ℝ) * (Q x c : ℝ))) -
            2 * (c.supp.ncard : ℝ) * (c'.supp.ncard : ℝ) *
              (∑ x : D.ConnectedComponent,
                (x.supp.ncard : ℝ) * ((Q x c : ℝ) * (Q x c' : ℝ))) +
            (c.supp.ncard : ℝ) ^ 2 *
              (∑ x : D.ConnectedComponent,
                (x.supp.ncard : ℝ) * ((Q x c' : ℝ) * (Q x c' : ℝ))) := by
        have hterm : ∀ x : D.ConnectedComponent,
            (x.supp.ncard : ℝ) *
                ((c'.supp.ncard : ℝ) * (Q x c : ℝ) -
                  (c.supp.ncard : ℝ) * (Q x c' : ℝ)) ^ 2 =
              (c'.supp.ncard : ℝ) ^ 2 *
                  ((x.supp.ncard : ℝ) * ((Q x c : ℝ) * (Q x c : ℝ))) -
                (2 * (c.supp.ncard : ℝ) * (c'.supp.ncard : ℝ)) *
                  ((x.supp.ncard : ℝ) * ((Q x c : ℝ) * (Q x c' : ℝ))) +
                (c.supp.ncard : ℝ) ^ 2 *
                  ((x.supp.ncard : ℝ) * ((Q x c' : ℝ) * (Q x c' : ℝ))) := by
          intro x
          ring
        rw [Finset.sum_congr rfl (fun x _ => hterm x),
          Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 0 := by
        rw [show (∑ x : D.ConnectedComponent,
              (x.supp.ncard : ℝ) * ((Q x c : ℝ) * (Q x c : ℝ))) =
            (c.supp.ncard : ℝ) * (c.supp.ncard : ℝ) by simpa [D, Q] using hcc,
          show (∑ x : D.ConnectedComponent,
              (x.supp.ncard : ℝ) * ((Q x c : ℝ) * (Q x c' : ℝ))) =
            (c.supp.ncard : ℝ) * (c'.supp.ncard : ℝ) by
              simpa [D, Q] using hcross,
          show (∑ x : D.ConnectedComponent,
              (x.supp.ncard : ℝ) * ((Q x c' : ℝ) * (Q x c' : ℝ))) =
            (c'.supp.ncard : ℝ) * (c'.supp.ncard : ℝ) by
              simpa [D, Q] using hcc']
        ring
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ =>
      mul_nonneg (Nat.cast_nonneg x.supp.ncard) (sq_nonneg _))).mp
      hsum e (Finset.mem_univ e)
  have hepos : (0 : ℝ) < (e.supp.ncard : ℝ) := by
    exact_mod_cast e.nonempty_supp.ncard_pos
  have hsqzero :
      ((c'.supp.ncard : ℝ) * (Q e c : ℝ) -
        (c.supp.ncard : ℝ) * (Q e c' : ℝ)) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hepos)
  have hreal : (c'.supp.ncard : ℝ) * (Q e c : ℝ) =
      (c.supp.ncard : ℝ) * (Q e c' : ℝ) := by
    nlinarith [sq_nonneg
      ((c'.supp.ncard : ℝ) * (Q e c : ℝ) -
        (c.supp.ncard : ℝ) * (Q e c' : ℝ))]
  exact_mod_cast hreal

/-- **Exact quotient formula.**  At square order every row of the component
quotient sees a component `c` in exactly `|c|/q` vertices.  The integral
form avoids division and immediately exposes component-size divisibility. -/
theorem binarySquare_regular_mul_componentQuotient_eq_componentCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e c : (secondOrderDefectGraph G).ConnectedComponent) :
    q * componentQuotientMatrix G (secondOrderDefectGraph G) e c =
      c.supp.ncard := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  have hsize : (∑ c' : D.ConnectedComponent, c'.supp.ncard) = q * q := by
    rw [sum_connectedComponent_supp_ncard D, hcard]
  have hrow : (∑ c' : D.ConnectedComponent, Q e c') = q := by
    rw [sum_componentQuotientMatrix_row, hreg]
  have hsumCross :
      (∑ c' : D.ConnectedComponent, c'.supp.ncard * Q e c) =
        ∑ c' : D.ConnectedComponent, c.supp.ncard * Q e c' := by
    apply Finset.sum_congr rfl
    intro c' _
    exact binarySquare_regular_componentQuotient_cross_mul
      G hfree hq hreg hcard e c c'
  have heq : q * q * Q e c = c.supp.ncard * q := by
    calc
      q * q * Q e c = (∑ c' : D.ConnectedComponent, c'.supp.ncard) * Q e c := by
        rw [hsize]
      _ = ∑ c' : D.ConnectedComponent, c'.supp.ncard * Q e c := by
        rw [Finset.sum_mul]
      _ = ∑ c' : D.ConnectedComponent, c.supp.ncard * Q e c' := hsumCross
      _ = c.supp.ncard * (∑ c' : D.ConnectedComponent, Q e c') := by
        rw [Finset.mul_sum]
      _ = c.supp.ncard * q := by rw [hrow]
  have heq' : q * (q * Q e c) = q * c.supp.ncard := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using heq
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) heq'

/-- Every defect-component order in a regular binary square-order candidate
is divisible by the square root `q` of the ambient order. -/
theorem binarySquare_regular_dvd_defectComponent_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    q ∣ c.supp.ncard := by
  let e := c
  refine ⟨componentQuotientMatrix G (secondOrderDefectGraph G) e c, ?_⟩
  exact (binarySquare_regular_mul_componentQuotient_eq_componentCard
    G hfree hq hreg hcard e c).symm

/-- Graph-facing form of the exact quotient formula: every vertex, regardless
of its source defect component, has exactly `|c|/q` ambient neighbors in the
target defect component `c`. -/
theorem binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e c : (secondOrderDefectGraph G).ConnectedComponent)
    {x : V} (hx : x ∈ e.supp) :
    q * (componentNeighborFinset G (secondOrderDefectGraph G) c x).card =
      c.supp.ncard := by
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdegree : ∀ y : V,
      (secondOrderDefectGraph G).degree y = q - 1 := by
    intro y
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus y
    change (secondOrderDefectGraph G).degree y = (q - 3) + 2 at h
    omega
  have hcomm : G.adjMatrix ℝ * (secondOrderDefectGraph G).adjMatrix ℝ =
      (secondOrderDefectGraph G).adjMatrix ℝ * G.adjMatrix ℝ :=
    adjMatrix_comm_secondOrderDefect_of_regular_field G hfree hreg
  have hQ := componentQuotientMatrix_apply_eq
    G (secondOrderDefectGraph G) (q - 1) hDdegree hcomm e c hx
  rw [← hQ]
  exact binarySquare_regular_mul_componentQuotient_eq_componentCard
    G hfree hq hreg hcard e c

/-- Every row of the defect-component quotient is identical. -/
theorem binarySquare_regular_componentQuotient_row_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e e' c : (secondOrderDefectGraph G).ConnectedComponent) :
    componentQuotientMatrix G (secondOrderDefectGraph G) e c =
      componentQuotientMatrix G (secondOrderDefectGraph G) e' c := by
  have he := binarySquare_regular_mul_componentQuotient_eq_componentCard
    G hfree hq hreg hcard e c
  have he' := binarySquare_regular_mul_componentQuotient_eq_componentCard
    G hfree hq hreg hcard e' c
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) (he.trans he'.symm)

/-- Pointwise equitability with a fixed reference row: the number of
neighbors of an arbitrary vertex in `c` is the same quotient entry, with no
dependence on the source component. -/
theorem binarySquare_regular_componentNeighborCard_eq_quotient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e₀ c : (secondOrderDefectGraph G).ConnectedComponent) (x : V) :
    (componentNeighborFinset G (secondOrderDefectGraph G) c x).card =
      componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c := by
  let e := (secondOrderDefectGraph G).connectedComponentMk x
  have hlocal := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    G hfree hq hreg hcard e c (x := x) (by rfl)
  have href := binarySquare_regular_mul_componentQuotient_eq_componentCard
    G hfree hq hreg hcard e₀ c
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) (hlocal.trans href.symm)

/-- Characteristic-two indicator of one defect component. -/
def defectComponentIndicatorZModTwo
    {V : Type*} (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) : V → ZMod 2 :=
  fun x => if D.connectedComponentMk x = c then 1 else 0

/-- **Component-constant mod-two action.**  The ambient adjacency matrix sends
the indicator of a defect component `c` to the constant vector whose value is
the common quotient entry toward `c`.  This is the formal source of the
automatic quotient-kernel vectors in disconnected candidates. -/
theorem binarySquare_regular_adj_mulVec_defectComponentIndicatorZModTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e₀ c : (secondOrderDefectGraph G).ConnectedComponent) :
    (G.adjMatrix (ZMod 2)).mulVec
        (defectComponentIndicatorZModTwo (secondOrderDefectGraph G) c) =
      fun _ => (componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c :
        ZMod 2) := by
  funext x
  rw [Matrix.mulVec, dotProduct]
  simp only [SimpleGraph.adjMatrix_apply, defectComponentIndicatorZModTwo,
    ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilt : Finset.univ.filter (fun y => G.Adj x y) =
      G.neighborFinset x := by
    ext y
    simp [SimpleGraph.mem_neighborFinset]
  rw [hfilt]
  calc
    (∑ y ∈ G.neighborFinset x,
        if (secondOrderDefectGraph G).connectedComponentMk y = c
          then (1 : ZMod 2) else 0) =
        ((componentNeighborFinset G (secondOrderDefectGraph G) c x).card :
          ZMod 2) := by
      rw [Finset.sum_boole]
      congr 2
    _ = (componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c :
          ZMod 2) := by
      exact congrArg (fun n : ℕ => (n : ZMod 2))
        (binarySquare_regular_componentNeighborCard_eq_quotient
          G hfree hq hreg hcard e₀ c x)

/-- A component whose normalized order is even already supplies an ambient
adjacency-kernel vector over `𝔽₂`. -/
theorem binarySquare_regular_defectComponentIndicator_mem_kernel_of_evenRow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e₀ c : (secondOrderDefectGraph G).ConnectedComponent)
    (hevenRow : (componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c :
      ZMod 2) = 0) :
    (G.adjMatrix (ZMod 2)).mulVec
        (defectComponentIndicatorZModTwo (secondOrderDefectGraph G) c) = 0 := by
  rw [binarySquare_regular_adj_mulVec_defectComponentIndicatorZModTwo
    G hfree hq hreg hcard e₀ c]
  funext x
  simpa using hevenRow

/-- Two component indicators whose normalized orders have the same parity
also sum to an ambient adjacency-kernel vector over `𝔽₂`. -/
theorem binarySquare_regular_add_defectComponentIndicators_mem_kernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e₀ c c' : (secondOrderDefectGraph G).ConnectedComponent)
    (hparity :
      (componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c : ZMod 2) +
        (componentQuotientMatrix G (secondOrderDefectGraph G) e₀ c' : ZMod 2) =
          0) :
    (G.adjMatrix (ZMod 2)).mulVec
        (defectComponentIndicatorZModTwo (secondOrderDefectGraph G) c +
          defectComponentIndicatorZModTwo (secondOrderDefectGraph G) c') = 0 := by
  rw [Matrix.mulVec_add,
    binarySquare_regular_adj_mulVec_defectComponentIndicatorZModTwo
      G hfree hq hreg hcard e₀ c,
    binarySquare_regular_adj_mulVec_defectComponentIndicatorZModTwo
      G hfree hq hreg hcard e₀ c']
  funext x
  simpa using hparity

/-- A smallest defect component, of order `q`, is a clique in the
`(q-1)`-regular defect graph. -/
theorem binarySquare_regular_sizeQ_defectComponent_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q) {x y : V}
    (hx : (secondOrderDefectGraph G).connectedComponentMk x = c)
    (hy : (secondOrderDefectGraph G).connectedComponentMk y = c)
    (hxy : x ≠ y) :
    (secondOrderDefectGraph G).Adj x y := by
  classical
  let D := secondOrderDefectGraph G
  change D.connectedComponentMk x = c at hx
  change D.connectedComponentMk y = c at hy
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdegree : ∀ z : V, D.degree z = q - 1 := by
    intro z
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus z
    change D.degree z = (q - 3) + 2 at h
    omega
  let cs : Finset V := Finset.univ.filter (fun z => D.connectedComponentMk z = c)
  have hcardcs : cs.card = q := by
    calc
      cs.card = c.supp.ncard := by
        rw [← Set.ncard_coe_finset]
        congr 1
        ext z
        simp [cs, D, SimpleGraph.ConnectedComponent.mem_supp_iff]
      _ = q := hc
  have hxmem : x ∈ cs := by simp [cs, hx]
  have hneighbors : D.neighborFinset x = cs.erase x := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      have hxz : D.Adj x z := (D.mem_neighborFinset x z).mp hz
      have hcomp : D.connectedComponentMk z = c :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm.trans hx
      exact Finset.mem_erase.mpr ⟨(D.ne_of_adj hxz).symm, by simp [cs, hcomp]⟩
    · rw [D.card_neighborFinset_eq_degree, hDdegree,
        Finset.card_erase_of_mem hxmem, hcardcs]
  have hymem : y ∈ cs.erase x := by simp [cs, hy, hxy.symm]
  rw [← hneighbors] at hymem
  exact (D.mem_neighborFinset x y).mp hymem

/-- Distinct vertices of a unit defect part have disjoint ambient
neighborhoods. -/
theorem binarySquare_regular_sizeQ_component_commonNeighbors_card_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q) {x y : V}
    (hx : (secondOrderDefectGraph G).connectedComponentMk x = c)
    (hy : (secondOrderDefectGraph G).connectedComponentMk y = c)
    (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by
  have hD := binarySquare_regular_sizeQ_defectComponent_adj
    G hfree hq hreg hcard c hc hx hy hxy
  have hmem : y ∈ (secondOrderDefectGraph G).neighborFinset x :=
    ((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hD
  rw [card_common_eq_if_secondOrderDefect G hfree x y hxy, if_pos hmem]

/-- Every vertex has exactly one ambient neighbor in a smallest order-`q`
defect component. -/
theorem binarySquare_regular_card_componentNeighbors_sizeQ_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q) (x : V) :
    (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 1 := by
  let e := (secondOrderDefectGraph G).connectedComponentMk x
  have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    G hfree hq hreg hcard e c (x := x) (by rfl)
  rw [hc] at h
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) (by simpa using h)

/-- The normalized defect-component orders form an honest partition of `q`.
Concretely, one may take the parts to be any row of the component quotient. -/
theorem binarySquare_regular_exists_defectComponent_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    ∃ m : (secondOrderDefectGraph G).ConnectedComponent → ℕ,
      (∀ c, c.supp.ncard = q * m c) ∧ ∑ c, m c = q := by
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by
    rw [hcard]
    positivity)
  let x : V := Classical.choice hV
  let e := (secondOrderDefectGraph G).connectedComponentMk x
  let m : (secondOrderDefectGraph G).ConnectedComponent → ℕ :=
    fun c => componentQuotientMatrix G (secondOrderDefectGraph G) e c
  refine ⟨m, ?_, ?_⟩
  · intro c
    exact (binarySquare_regular_mul_componentQuotient_eq_componentCard
      G hfree hq hreg hcard e c).symm
  · simpa [m] using
      (show (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
          componentQuotientMatrix G (secondOrderDefectGraph G) e c) = q by
        rw [sum_componentQuotientMatrix_row, hreg])

/-- There are at most `q` defect components: their positive normalized orders
sum to `q`. -/
theorem binarySquare_regular_card_defectComponents_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    Fintype.card (secondOrderDefectGraph G).ConnectedComponent ≤ q := by
  obtain ⟨m, hmSize, hmSum⟩ :=
    binarySquare_regular_exists_defectComponent_partition
      G hfree hq hreg hcard
  calc
    Fintype.card (secondOrderDefectGraph G).ConnectedComponent =
        ∑ c : (secondOrderDefectGraph G).ConnectedComponent, 1 := by simp
    _ ≤ ∑ c : (secondOrderDefectGraph G).ConnectedComponent, m c := by
      apply Finset.sum_le_sum
      intro c _
      have hcpos : 0 < c.supp.ncard := c.nonempty_supp.ncard_pos
      have hqpos : 0 < q := by omega
      have hmpos : 0 < m c := by
        by_contra hm0
        push Not at hm0
        have : m c = 0 := by omega
        rw [hmSize c, this, mul_zero] at hcpos
        omega
      omega
    _ = q := hmSum

end Erdos85
