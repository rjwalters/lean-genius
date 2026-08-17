import Proofs.Erdos85EvenExcessOneDefectKernel
import Proofs.Erdos85AdjacencyCharpolySquareModTwo
import Proofs.Erdos85ComponentFactorization
import Proofs.Erdos85ComponentLocalObstruction
import Proofs.Erdos85QuotientGramIdentity
import Proofs.Erdos85ExcessEigenspace
import Proofs.Erdos85ResidueSignedCount
import Proofs.Erdos85GlobalLocalTriangleCount
import Proofs.Erdos85IsCyclesComponentCharpoly
import Proofs.Erdos85DefectComponentBlockCommute

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

/-- A normalized component part `m` is also the exact internal ambient degree:
the graph induced by `G` on that defect component is `m`-regular. -/
theorem binarySquare_regular_degree_induce_defectComponent_eq_part
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = q * m) (x : c.supp) :
    (G.induce c.supp).degree x = m := by
  have hinduced : (G.induce c.supp).degree x =
      (componentNeighborFinset G (secondOrderDefectGraph G) c x.1).card := by
    show ((G.induce c.supp).neighborFinset x).card = _
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      rw [SimpleGraph.mem_neighborFinset] at hy
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset x.1 y.1).mpr hy,
          (SimpleGraph.ConnectedComponent.mem_supp_iff c y.1).mp y.2⟩
    · intro y₁ h₁ y₂ h₂ hy
      exact Subtype.ext hy
    · intro y hy
      rw [componentNeighborFinset, Finset.mem_filter] at hy
      have hySupp : y ∈ c.supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mpr hy.2
      refine ⟨⟨y, hySupp⟩, ?_, rfl⟩
      apply ((G.induce c.supp).mem_neighborFinset x ⟨y, hySupp⟩).mpr
      exact (G.mem_neighborFinset x.1 y).mp hy.1
  have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    G hfree hq hreg hcard
    ((secondOrderDefectGraph G).connectedComponentMk x.1) c (x := x.1) (by rfl)
  rw [hc] at hmul
  calc
    (G.induce c.supp).degree x =
        (componentNeighborFinset G (secondOrderDefectGraph G) c x.1).card := hinduced
    _ = m := Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul

/-- Triangle-free edges stay inside their source defect component. -/
theorem triangleFreeNeighbors_subset_componentNeighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) {x : V}
    (hx : x ∈ c.supp) :
    triangleFreeNeighbors G x ⊆
      componentNeighborFinset G (secondOrderDefectGraph G) c x := by
  intro y hy
  have hyData := (mem_triangleFreeNeighbors G x y).mp hy
  have hxc : (secondOrderDefectGraph G).connectedComponentMk x = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp hx
  have hDxy : (secondOrderDefectGraph G).Adj x y := by
    change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y
    rw [SimpleGraph.sup_adj]
    exact Or.inr ((triangleFreeEdgeGraph_adj G x y).mpr hy)
  have hyc : (secondOrderDefectGraph G).connectedComponentMk y = c :=
    (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hDxy).symm.trans hxc
  rw [componentNeighborFinset]
  exact Finset.mem_filter.mpr
    ⟨(G.mem_neighborFinset x y).mpr hyData.1, hyc⟩

/-- Any exhibited common neighbor forbids a second-order defect edge.  This is
the pointwise graph-specific constraint later applied to distance-two pairs on
the internal cycles of a normalized size-two component. -/
theorem not_secondOrderDefect_adj_of_commonNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y z : V} (hxy : x ≠ y)
    (hxz : G.Adj x z) (hyz : G.Adj y z) :
    ¬ (secondOrderDefectGraph G).Adj x y := by
  intro hD
  have hmem : y ∈ (secondOrderDefectGraph G).neighborFinset x :=
    ((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hD
  have hzero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by
    rw [card_common_eq_if_secondOrderDefect G hfree x y hxy, if_pos hmem]
  have hz : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset x z).mpr hxz,
        (G.mem_neighborFinset y z).mpr hyz⟩
  have hpos : 0 < (G.neighborFinset x ∩ G.neighborFinset y).card :=
    Finset.card_pos.mpr ⟨z, hz⟩
  omega

/-- A second-order defect edge has disjoint neighbor selectors in every defect
component: any vertex in both selectors would be a common ambient neighbor of
the endpoints, contradicting the defining zero-common-neighbor relation. -/
theorem componentNeighborFinset_disjoint_of_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {x y : V} (hxy : (secondOrderDefectGraph G).Adj x y)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    Disjoint
      (componentNeighborFinset G (secondOrderDefectGraph G) c x)
      (componentNeighborFinset G (secondOrderDefectGraph G) c y) := by
  rw [Finset.disjoint_left]
  intro z hzx hzy
  rw [componentNeighborFinset, Finset.mem_filter] at hzx hzy
  exact (not_secondOrderDefect_adj_of_commonNeighbor G hfree
    ((secondOrderDefectGraph G).ne_of_adj hxy)
    ((G.mem_neighborFinset x z).mp hzx.1)
    ((G.mem_neighborFinset y z).mp hzy.1)) hxy

/-- Triangle-free edges stay inside the defect component, so their degree at
a vertex is bounded by the normalized component part. -/
theorem binarySquare_regular_triangleFree_degree_le_part
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = q * m) (x : c.supp) :
    (triangleFreeEdgeGraph G).degree x.1 ≤ m := by
  have hsubset : triangleFreeNeighbors G x.1 ⊆
      componentNeighborFinset G (secondOrderDefectGraph G) c x.1 :=
    triangleFreeNeighbors_subset_componentNeighborFinset G c x.2
  have hcomponent :
      (componentNeighborFinset G (secondOrderDefectGraph G) c x.1).card = m := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard
      ((secondOrderDefectGraph G).connectedComponentMk x.1) c (x := x.1) (by rfl)
    rw [hc] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
    triangleFreeEdgeGraph_neighborFinset]
  exact (Finset.card_le_card hsubset).trans_eq hcomponent

/-- At even ambient degree, the triangle-free degree at every vertex is even:
all other incident edges are paired by their unique triangles. -/
theorem binarySquare_regular_triangleFree_degree_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q) (x : V) :
    Even ((triangleFreeEdgeGraph G).degree x) := by
  have hlocal := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  have htfcard : (triangleFreeNeighbors G x).card =
      (triangleFreeEdgeGraph G).degree x := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
  rw [hreg x, htfcard] at hlocal
  obtain ⟨a, ha⟩ := hqEven
  refine ⟨a - (G.induce (G.neighborSet x)).edgeFinset.card, ?_⟩
  omega

/-- In a normalized part of size two at even degree, every vertex has either
zero or two triangle-free neighbors. -/
theorem binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x : c.supp) :
    (triangleFreeEdgeGraph G).degree x.1 = 0 ∨
      (triangleFreeEdgeGraph G).degree x.1 = 2 := by
  have hle := binarySquare_regular_triangleFree_degree_le_part
    G hfree hq hreg hcard c hc x
  have heven := binarySquare_regular_triangleFree_degree_even
    G hfree hqEven hreg x.1
  obtain ⟨a, ha⟩ := heven
  omega

/-- On an internal ambient edge of a normalized size-two component, the
triangle-free degree-two status propagates across the edge. -/
theorem binarySquare_regular_sizeTwoPart_triangleFree_degree_two_iff_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x y : c.supp) (hxy : G.Adj x.1 y.1) :
    (triangleFreeEdgeGraph G).degree x.1 = 2 ↔
      (triangleFreeEdgeGraph G).degree y.1 = 2 := by
  have forward (u v : c.supp) (huv : G.Adj u.1 v.1)
      (hu : (triangleFreeEdgeGraph G).degree u.1 = 2) :
      (triangleFreeEdgeGraph G).degree v.1 = 2 := by
    have hsub := triangleFreeNeighbors_subset_componentNeighborFinset G c u.2
    have htfcard : (triangleFreeNeighbors G u.1).card = 2 := by
      rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
        triangleFreeEdgeGraph_neighborFinset] at hu
      exact hu
    have hcompcard :
        (componentNeighborFinset G (secondOrderDefectGraph G) c u.1).card = 2 := by
      have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
        G hfree hq hreg hcard
        ((secondOrderDefectGraph G).connectedComponentMk u.1) c (x := u.1) (by rfl)
      rw [hc] at hmul
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
    have heq : triangleFreeNeighbors G u.1 =
        componentNeighborFinset G (secondOrderDefectGraph G) c u.1 := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [htfcard, hcompcard]
    have hvComp : v.1 ∈
        componentNeighborFinset G (secondOrderDefectGraph G) c u.1 := by
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset u.1 v.1).mpr huv,
          (SimpleGraph.ConnectedComponent.mem_supp_iff c v.1).mp v.2⟩
    have hvTf : v.1 ∈ triangleFreeNeighbors G u.1 := by rwa [heq]
    have hpos : 0 < (triangleFreeEdgeGraph G).degree v.1 := by
      have hadjTf : (triangleFreeEdgeGraph G).Adj u.1 v.1 :=
        (triangleFreeEdgeGraph_adj G u.1 v.1).mpr hvTf
      have : u.1 ∈ (triangleFreeEdgeGraph G).neighborFinset v.1 :=
        ((triangleFreeEdgeGraph G).mem_neighborFinset v.1 u.1).mpr hadjTf.symm
      rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨u.1, this⟩
    rcases binarySquare_regular_sizeTwoPart_triangleFree_degree_eq_zero_or_two
      G hfree hq hqEven hreg hcard c hc v with hv | hv
    · omega
    · exact hv
  exact ⟨forward x y hxy, forward y x hxy.symm⟩

/-- Every connected piece of the internal ambient graph of a normalized
size-two defect component is a spanning simple cycle, and C4-freeness excludes
cycle length four. -/
theorem binarySquare_regular_sizeTwoPart_exists_cycle_of_internalComponent
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
    (hc : c.supp.ncard = q * 2)
    (a : (G.induce c.supp).ConnectedComponent) :
    ∃ (x : c.supp) (p : (G.induce c.supp).Walk x x),
      p.IsCycle ∧ p.toSubgraph.verts = a.supp ∧
      p.toSubgraph.coe = (G.induce c.supp).induce p.toSubgraph.verts ∧
      p.length ≠ 4 ∧
      ∀ i : ℕ, i + 2 < p.length →
        ¬ ((secondOrderDefectGraph G).induce c.supp).Adj
          ⟨(p.getVert i).1, (p.getVert i).2⟩
          ⟨(p.getVert (i + 2)).1, (p.getVert (i + 2)).2⟩ := by
  have hdeg : ∀ x : c.supp, (G.induce c.supp).degree x = 2 :=
    fun x => binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree hq hreg hcard c hc x
  obtain ⟨x, p, hp, hpverts, hpgraph⟩ :=
    twoRegular_component_induce_eq_cycleSubgraph (G.induce c.supp) hdeg a
  refine ⟨x, p, hp, hpverts, hpgraph, ?_, ?_⟩
  · intro hlen
    have hC4induced : containsC4 c.supp (G.induce c.supp) :=
      containsC4_of_isCycle_length_four hp hlen
    apply hfree
    rcases hC4induced with ⟨f, hf, hadj⟩
    exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
      fun i j hij => hadj i j hij⟩
  · intro i hi
    have hadj₁ := p.adj_getVert_succ (show i < p.length by omega)
    have hadj₂ := p.adj_getVert_succ (show i + 1 < p.length by omega)
    have hne : (p.getVert i).1 ≠ (p.getVert (i + 2)).1 := by
      intro heq
      have heqSubtype : p.getVert i = p.getVert (i + 2) := Subtype.ext heq
      have := hp.getVert_injOn'
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega)
        heqSubtype
      omega
    exact not_secondOrderDefect_adj_of_commonNeighbor G hfree hne
      hadj₁ (by simpa using hadj₂.symm)

/-- The two distance-two pairs crossing the basepoint of a labeled internal
cycle are defect nonedges as well.  Together with the preceding theorem this
removes the full `±2` cyclic diagonals. -/
theorem not_secondOrderDefect_adj_cycle_wraparound_distanceTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {s : Set V} {x : s}
    {p : (G.induce s).Walk x x} (hp : p.IsCycle) :
    (¬ (secondOrderDefectGraph G).Adj
        (p.getVert (p.length - 2)).1 (p.getVert 0).1) ∧
      ¬ (secondOrderDefectGraph G).Adj
        (p.getVert (p.length - 1)).1 (p.getVert 1).1 := by
  have hlen : 3 ≤ p.length := hp.three_le_length
  have hadjPred := p.adj_getVert_succ
    (show p.length - 2 < p.length by omega)
  have hadjLast := p.adj_getVert_succ
    (show p.length - 1 < p.length by omega)
  have hadjLastZero : G.Adj
      (p.getVert (p.length - 1)).1 (p.getVert 0).1 := by
    have hlenpos : 1 ≤ p.length := by omega
    simpa [Nat.sub_add_cancel hlenpos, p.getVert_length] using hadjLast
  have hadjZeroOne : G.Adj (p.getVert 0).1 (p.getVert 1).1 := by
    simpa using p.adj_getVert_succ (show 0 < p.length by omega)
  have hadjPredLast : G.Adj
      (p.getVert (p.length - 2)).1 (p.getVert (p.length - 1)).1 := by
    have hind : p.length - 2 + 1 = p.length - 1 := by omega
    simpa [hind] using hadjPred
  have hnePredZero : (p.getVert (p.length - 2)).1 ≠ (p.getVert 0).1 := by
    intro heq
    have heqSubtype : p.getVert (p.length - 2) = p.getVert 0 := Subtype.ext heq
    have hi := hp.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) heqSubtype
    omega
  have hneLastOne : (p.getVert (p.length - 1)).1 ≠ (p.getVert 1).1 := by
    intro heq
    have heqSubtype : p.getVert (p.length - 1) = p.getVert 1 := Subtype.ext heq
    have hi := hp.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) heqSubtype
    omega
  constructor
  · exact not_secondOrderDefect_adj_of_commonNeighbor G hfree hnePredZero
      hadjPredLast hadjLastZero.symm
  · exact not_secondOrderDefect_adj_of_commonNeighbor G hfree hneLastOne
      hadjLastZero hadjZeroOne.symm

/-- **Size-two block capstone.**  On a normalized size-two defect component,
the internal ambient graph is 2-regular, the internal defect graph is
`(q-1)`-regular and connected by construction, and their integer adjacency
matrices commute. -/
theorem binarySquare_regular_sizeTwoPart_commuting_regular_blocks
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
    (hc : c.supp.ncard = q * 2) :
    (∀ x : c.supp, (G.induce c.supp).degree x = 2) ∧
    (∀ x : c.supp,
      ((secondOrderDefectGraph G).induce c.supp).degree x = q - 1) ∧
    (G.induce c.supp).adjMatrix ℤ *
        ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ =
      ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ *
        (G.induce c.supp).adjMatrix ℤ := by
  have hGdegree : ∀ x : c.supp, (G.induce c.supp).degree x = 2 :=
    fun x => binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree hq hreg hcard c hc x
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdegree : ∀ x : V, (secondOrderDefectGraph G).degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change (secondOrderDefectGraph G).degree x = (q - 3) + 2 at h
    omega
  have hDcomponent : ∀ x : c.supp,
      ((secondOrderDefectGraph G).induce c.supp).degree x = q - 1 := by
    intro x
    rw [degree_induce_connectedComponent_supp]
    exact hDdegree x.1
  exact ⟨hGdegree, hDcomponent,
    adjMatrix_comm_secondOrderDefect_induce_component_of_regular
      G hfree hreg c⟩

/-- The defect block is equitable over the ambient-cycle decomposition of a
normalized size-two part.  Its cycle quotient has row sum `q-1` and satisfies
detailed balance weighted by the cycle orders. -/
theorem binarySquare_regular_sizeTwoPart_cycleQuotient
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
    (hc : c.supp.ncard = q * 2)
    [DecidableEq (G.induce c.supp).ConnectedComponent] :
    (∀ a : (G.induce c.supp).ConnectedComponent,
      ∑ b, componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b =
        q - 1) ∧
    (∀ a b : (G.induce c.supp).ConnectedComponent,
      a.supp.ncard * componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b =
        b.supp.ncard * componentQuotientMatrix
          ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) b a) ∧
    (∑ a : (G.induce c.supp).ConnectedComponent, a.supp.ncard) = q * 2 := by
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  obtain ⟨hHdegree, hKdegree, _hcommZ⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree hq hreg hcard c hc
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simpa [H, K, hKdegree] using
      (sum_componentQuotientMatrix_row K H a)
  · intro a b
    exact componentQuotientMatrix_balance K H 2 hHdegree hcommReal a b
  · calc
      (∑ a : H.ConnectedComponent, a.supp.ncard) = Fintype.card c.supp :=
        sum_connectedComponent_supp_ncard H
      _ = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
      _ = q * 2 := hc

/-- The cycle quotient above is irreducible: positive quotient entries connect
every ordered pair of ambient cycles, because the defect block itself is
connected. -/
theorem binarySquare_regular_sizeTwoPart_cycleQuotient_irreducible
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
    (hc : c.supp.ncard = q * 2)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a b : (G.induce c.supp).ConnectedComponent) :
    Relation.ReflTransGen
      (fun u v => 0 < componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) u v)
      a b := by
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  obtain ⟨hHdegree, _hKdegree, _hcommZ⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree hq hreg hcard c hc
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  let x := componentRepresentative H a
  let y := componentRepresentative H b
  have hKconn : K.Connected := by
    exact c.connected_toSimpleGraph
  have hreach : K.Reachable x y := hKconn.preconnected x y
  have hwalk : Relation.ReflTransGen K.Adj x y :=
    (K.reachable_iff_reflTransGen x y).mp hreach
  have hlift : Relation.ReflTransGen
      (fun u v : H.ConnectedComponent =>
        0 < componentQuotientMatrix K H u v)
      (H.connectedComponentMk x) (H.connectedComponentMk y) :=
    hwalk.lift H.connectedComponentMk (fun u v huv =>
      componentQuotientMatrix_pos_of_adj K H 2 hHdegree hcommReal huv)
  have hxa : H.connectedComponentMk x = a :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff a x).mp
      (componentRepresentative_mem H a)
  have hyb : H.connectedComponentMk y = b :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff b y).mp
      (componentRepresentative_mem H b)
  simpa [H, K, x, y, hxa, hyb] using hlift

/-- A cycle of length at least five loses its two distance-two vertices from
the diagonal defect block, so its diagonal cycle-quotient entry is at most
`r-3`. -/
theorem binarySquare_regular_sizeTwoPart_cycleQuotient_diagonal_le
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
    (hc : c.supp.ncard = q * 2)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a : (G.induce c.supp).ConnectedComponent) (ha : 5 ≤ a.supp.ncard) :
    componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a a ≤
      a.supp.ncard - 3 := by
  let H := G.induce c.supp
  let K := (secondOrderDefectGraph G).induce c.supp
  obtain ⟨x, p, hp, hpverts, _hpgraph, _hlen4, hnonwrap⟩ :=
    binarySquare_regular_sizeTwoPart_exists_cycle_of_internalComponent
      G hfree hq hreg hcard c hc a
  have hplen : p.length = a.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = a.supp.ncard := congrArg Set.ncard hpverts
  let x0 : c.supp := p.getVert 0
  let u : c.supp := p.getVert 2
  let v : c.supp := p.getVert (p.length - 2)
  have hnotU : ¬ K.Adj x0 u := by
    exact hnonwrap 0 (by omega)
  have hwrap :=
    (not_secondOrderDefect_adj_cycle_wraparound_distanceTwo G hfree hp).1
  have hnotV : ¬ K.Adj x0 v := by
    intro hxv
    exact hwrap hxv.symm
  have hx0mem : x0 ∈ a.supp := by
    change p.getVert 0 ∈ a.supp
    rw [← hpverts]
    simpa only [Walk.mem_verts_toSubgraph] using p.getVert_mem_support 0
  have humem : u ∈ a.supp := by
    change p.getVert 2 ∈ a.supp
    rw [← hpverts]
    simpa only [Walk.mem_verts_toSubgraph] using p.getVert_mem_support 2
  have hvmem : v ∈ a.supp := by
    change p.getVert (p.length - 2) ∈ a.supp
    rw [← hpverts]
    simpa only [Walk.mem_verts_toSubgraph] using
      p.getVert_mem_support (p.length - 2)
  have hxu : x0 ≠ u := by
    intro heq
    have hi := hp.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) heq
    omega
  have hxv : x0 ≠ v := by
    intro heq
    have hi := hp.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) heq
    omega
  have huv : u ≠ v := by
    intro heq
    have hi := hp.getVert_injOn'
      (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) heq
    omega
  let S : Finset c.supp := a.supp.toFinite.toFinset
  let T : Finset c.supp := ((S.erase x0).erase u).erase v
  have hsub : componentNeighborFinset K H a x0 ⊆ T := by
    intro z hz
    have hzData := Finset.mem_filter.mp hz
    have hzS : z ∈ S := by
      simp only [S, Set.Finite.mem_toFinset]
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff a z).mpr hzData.2
    have hzx : z ≠ x0 := K.ne_of_adj
      ((K.mem_neighborFinset x0 z).mp hzData.1) |>.symm
    have hzu : z ≠ u := by
      intro hzu
      subst z
      exact hnotU ((K.mem_neighborFinset x0 u).mp hzData.1)
    have hzv : z ≠ v := by
      intro hzv
      subst z
      exact hnotV ((K.mem_neighborFinset x0 v).mp hzData.1)
    simp [T, hzS, hzx, hzu, hzv]
  have hTcard : T.card = a.supp.ncard - 3 := by
    have hxS : x0 ∈ S := by simpa [S] using hx0mem
    have huS : u ∈ S := by simpa [S] using humem
    have hvS : v ∈ S := by simpa [S] using hvmem
    have huErase : u ∈ S.erase x0 := Finset.mem_erase.mpr ⟨hxu.symm, huS⟩
    have hvErase : v ∈ (S.erase x0).erase u := by
      exact Finset.mem_erase.mpr
        ⟨huv.symm, Finset.mem_erase.mpr ⟨hxv.symm, hvS⟩⟩
    change (((S.erase x0).erase u).erase v).card = a.supp.ncard - 3
    rw [Finset.card_erase_of_mem hvErase,
      Finset.card_erase_of_mem huErase, Finset.card_erase_of_mem hxS]
    have hScard : S.card = a.supp.ncard := by
      exact (Set.ncard_eq_toFinset_card a.supp a.supp.toFinite).symm
    omega
  obtain ⟨hHdegree, _hKdegree, _hcommZ⟩ :=
    binarySquare_regular_sizeTwoPart_commuting_regular_blocks
      G hfree hq hreg hcard c hc
  have hcommReal : K.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * K.adjMatrix ℝ := by
    have hglobal := adjMatrix_comm_secondOrderDefect_of_regular_field
      (K := ℝ) G hfree hreg
    exact (induce_component_adjMatrix_comm_of_comm
      G (secondOrderDefectGraph G) hglobal c).symm
  rw [componentQuotientMatrix_apply_eq K H 2 hHdegree hcommReal a a hx0mem]
  exact (Finset.card_le_card hsub).trans_eq hTcard

/-- Consequently a length-`r` ambient cycle must send enough defect quotient
mass to the other cycles to compensate for its two forbidden distance-two
diagonals. -/
theorem binarySquare_regular_sizeTwoPart_cycleQuotient_cross_mass
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
    (hc : c.supp.ncard = q * 2)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (a : (G.induce c.supp).ConnectedComponent) (ha : 5 ≤ a.supp.ncard) :
    q + 2 ≤ a.supp.ncard +
      ∑ b ∈ (Finset.univ.erase a), componentQuotientMatrix
        ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b := by
  let Q := componentQuotientMatrix
    ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp)
  have hrow :=
    (binarySquare_regular_sizeTwoPart_cycleQuotient
      G hfree hq hreg hcard c hc).1 a
  have hdiag := binarySquare_regular_sizeTwoPart_cycleQuotient_diagonal_le
    G hfree hq hreg hcard c hc a ha
  have haUniv : a ∈ (Finset.univ :
      Finset (G.induce c.supp).ConnectedComponent) := Finset.mem_univ a
  have hsplit := Finset.sum_erase_add (Finset.univ)
    (fun b => Q a b) haUniv
  change (∑ b, Q a b) = q - 1 at hrow
  change Q a a ≤ a.supp.ncard - 3 at hdiag
  have hsumEq : (∑ b ∈ Finset.univ.erase a, Q a b) + Q a a = q - 1 := by
    calc
      (∑ b ∈ Finset.univ.erase a, Q a b) + Q a a = ∑ b, Q a b := hsplit
      _ = q - 1 := hrow
  have hle : q - 1 ≤
      (∑ b ∈ Finset.univ.erase a, Q a b) + (a.supp.ncard - 3) := by
    rw [← hsumEq]
    exact Nat.add_le_add_left hdiag _
  change q - 1 ≤
    (∑ b ∈ Finset.univ.erase a, componentQuotientMatrix
      ((secondOrderDefectGraph G).induce c.supp) (G.induce c.supp) a b) +
      (a.supp.ncard - 3) at hle
  omega

/-- **Uniform pair-complement theorem for a size-two part.**  Every ambient
vertex selects exactly two neighbors in `c`, and a distinct pair in `c` is
selected by some ambient vertex exactly when it is a nonedge of the defect
graph. -/
theorem binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
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
    (hc : c.supp.ncard = q * 2) (u v : c.supp) (huv : u ≠ v) :
    ((∃ x : V,
        componentNeighborFinset G (secondOrderDefectGraph G) c x =
          {u.1, v.1}) ↔
      ¬ (secondOrderDefectGraph G).Adj u.1 v.1) := by
  let D := secondOrderDefectGraph G
  have huvval : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  have htwo (x : V) : (componentNeighborFinset G D c x).card = 2 := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard (D.connectedComponentMk x) c (x := x) (by rfl)
    rw [hc] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  constructor
  · rintro ⟨x, hx⟩ hDuv
    have hxu : G.Adj x u.1 := by
      have hu : u.1 ∈ componentNeighborFinset G D c x := by
        rw [hx]
        simp [huvval]
      exact (G.mem_neighborFinset x u.1).mp (Finset.mem_filter.mp hu).1
    have hxv : G.Adj x v.1 := by
      have hv : v.1 ∈ componentNeighborFinset G D c x := by
        rw [hx]
        simp
      exact (G.mem_neighborFinset x v.1).mp (Finset.mem_filter.mp hv).1
    have hxmem : x ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset u.1 x).mpr hxu.symm,
          (G.mem_neighborFinset v.1 x).mpr hxv.symm⟩
    have hcommon := card_common_eq_if_secondOrderDefect
      G hfree u.1 v.1 huvval
    have hmemD : v.1 ∈ D.neighborFinset u.1 :=
      (D.mem_neighborFinset u.1 v.1).mpr hDuv
    rw [if_pos hmemD] at hcommon
    have hpos : 0 < (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card :=
      Finset.card_pos.mpr ⟨x, hxmem⟩
    omega
  · intro hDuv
    have hcommon := card_common_eq_if_secondOrderDefect
      G hfree u.1 v.1 huvval
    have hnotmemD : v.1 ∉ D.neighborFinset u.1 := by
      intro hmem
      exact hDuv ((D.mem_neighborFinset u.1 v.1).mp hmem)
    rw [if_neg hnotmemD] at hcommon
    obtain ⟨x, hx⟩ :
        ∃ x, x ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 :=
      Finset.card_pos.mp (by omega)
    refine ⟨x, ?_⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · apply Finset.mem_filter.mpr
        refine ⟨(G.mem_neighborFinset x u.1).mpr
          ((G.mem_neighborFinset u.1 x).mp (Finset.mem_inter.mp hx).1).symm, ?_⟩
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff c u.1).mp u.2
      · apply Finset.mem_filter.mpr
        refine ⟨(G.mem_neighborFinset x v.1).mpr
          ((G.mem_neighborFinset v.1 x).mp (Finset.mem_inter.mp hx).2).symm, ?_⟩
        exact (SimpleGraph.ConnectedComponent.mem_supp_iff c v.1).mp v.2
    · rw [htwo x]
      simp [huvval]

/-- The selector in the pair-complement theorem is unique.  Thus ambient
vertices and complement edges of the size-two defect block are related by an
exact pair design, not merely a surjection. -/
theorem binarySquare_regular_sizeTwoPart_existsUnique_pair_iff_not_defectAdj
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
    (hc : c.supp.ncard = q * 2) (u v : c.supp) (huv : u ≠ v) :
    ((∃! x : V,
        componentNeighborFinset G (secondOrderDefectGraph G) c x =
          {u.1, v.1}) ↔
      ¬ (secondOrderDefectGraph G).Adj u.1 v.1) := by
  let D := secondOrderDefectGraph G
  have huvval : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  constructor
  · rintro ⟨x, hx, _hunique⟩
    exact (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
      G hfree hq hreg hcard c hc u v huv).mp ⟨x, hx⟩
  · intro hnotD
    obtain ⟨x, hx⟩ :=
      (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
        G hfree hq hreg hcard c hc u v huv).mpr hnotD
    refine ⟨x, hx, ?_⟩
    intro y hy
    have selector_mem (z : V)
        (hz : componentNeighborFinset G D c z = {u.1, v.1}) :
        z ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 := by
      have hzu : G.Adj z u.1 := by
        have : u.1 ∈ componentNeighborFinset G D c z := by
          rw [hz]
          simp [huvval]
        exact (G.mem_neighborFinset z u.1).mp (Finset.mem_filter.mp this).1
      have hzv : G.Adj z v.1 := by
        have : v.1 ∈ componentNeighborFinset G D c z := by
          rw [hz]
          simp
        exact (G.mem_neighborFinset z v.1).mp (Finset.mem_filter.mp this).1
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset u.1 z).mpr hzu.symm,
          (G.mem_neighborFinset v.1 z).mpr hzv.symm⟩
    have hcommon := card_common_eq_if_secondOrderDefect
      G hfree u.1 v.1 huvval
    have hnotmemD : v.1 ∉ D.neighborFinset u.1 := by
      intro hmem
      exact hnotD ((D.mem_neighborFinset u.1 v.1).mp hmem)
    rw [if_neg hnotmemD] at hcommon
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcommon
    have hxmem := selector_mem x hx
    have hymem := selector_mem y hy
    rw [hz] at hxmem hymem
    have hxz : x = z := by simpa using hxmem
    have hyz : y = z := by simpa using hymem
    exact hyz.trans hxz.symm

/-- The two-neighbor selector map into a normalized size-two component is
injective on all ambient vertices. -/
theorem binarySquare_regular_sizeTwoPart_componentNeighborFinset_injective
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
    (hc : c.supp.ncard = q * 2) :
    Function.Injective
      (fun x : V => componentNeighborFinset G (secondOrderDefectGraph G) c x) := by
  let D := secondOrderDefectGraph G
  intro x y hxy
  have htwo : (componentNeighborFinset G D c x).card = 2 := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard (D.connectedComponentMk x) c (x := x) (by rfl)
    rw [hc] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  obtain ⟨u, v, huv, hpair⟩ := Finset.card_eq_two.mp htwo
  have huMem : u ∈ componentNeighborFinset G D c x := by
    rw [hpair]
    simp [huv]
  have hvMem : v ∈ componentNeighborFinset G D c x := by
    rw [hpair]
    simp
  have huSupp : u ∈ c.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c u).mpr
      (Finset.mem_filter.mp huMem).2
  have hvSupp : v ∈ c.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mpr
      (Finset.mem_filter.mp hvMem).2
  let u' : c.supp := ⟨u, huSupp⟩
  let v' : c.supp := ⟨v, hvSupp⟩
  have huv' : u' ≠ v' := by
    intro h
    exact huv (congrArg Subtype.val h)
  have hnotD : ¬ D.Adj u v :=
    (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
      G hfree hq hreg hcard c hc u' v' huv').mp ⟨x, hpair⟩
  obtain ⟨z, hz, hzunique⟩ :=
    (binarySquare_regular_sizeTwoPart_existsUnique_pair_iff_not_defectAdj
      G hfree hq hreg hcard c hc u' v' huv').mpr hnotD
  have hxz : x = z := hzunique x hpair
  have hyPair : componentNeighborFinset G D c y = {u, v} := by
    change componentNeighborFinset G D c x = componentNeighborFinset G D c y at hxy
    exact hxy.symm.trans hpair
  have hyz : y = z := hzunique y hyPair
  exact hxz.trans hyz.symm

/-- The range of the selector map into a normalized size-two component is
exactly the family of two-element pairs that are nonedges of the defect graph.
Together with selector injectivity, this is the explicit bijective-design
interface between ambient vertices and complement edges of `D[c]`. -/
theorem binarySquare_regular_sizeTwoPart_componentNeighborFinset_range
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
    (hc : c.supp.ncard = q * 2) :
    Set.range
        (fun x : V => componentNeighborFinset G (secondOrderDefectGraph G) c x) =
      {s : Finset V | ∃ u v : c.supp,
        u ≠ v ∧ ¬(secondOrderDefectGraph G).Adj u.1 v.1 ∧ s = {u.1, v.1}} := by
  let D := secondOrderDefectGraph G
  ext s
  constructor
  · rintro ⟨x, rfl⟩
    have htwo : (componentNeighborFinset G D c x).card = 2 := by
      have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
        G hfree hq hreg hcard (D.connectedComponentMk x) c (x := x) (by rfl)
      rw [hc] at hmul
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
    obtain ⟨u, v, huv, hpair⟩ := Finset.card_eq_two.mp htwo
    have huMem : u ∈ componentNeighborFinset G D c x := by
      rw [hpair]
      simp [huv]
    have hvMem : v ∈ componentNeighborFinset G D c x := by
      rw [hpair]
      simp
    have huSupp : u ∈ c.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c u).mpr
        (Finset.mem_filter.mp huMem).2
    have hvSupp : v ∈ c.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c v).mpr
        (Finset.mem_filter.mp hvMem).2
    let u' : c.supp := ⟨u, huSupp⟩
    let v' : c.supp := ⟨v, hvSupp⟩
    have huv' : u' ≠ v' := by
      intro h
      exact huv (congrArg Subtype.val h)
    have hnotD : ¬ D.Adj u v :=
      (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
        G hfree hq hreg hcard c hc u' v' huv').mp ⟨x, hpair⟩
    exact ⟨u', v', huv', hnotD, hpair⟩
  · rintro ⟨u, v, huv, hnotD, rfl⟩
    obtain ⟨x, hx⟩ :=
      (binarySquare_regular_sizeTwoPart_pair_iff_not_defectAdj
        G hfree hq hreg hcard c hc u v huv).mpr hnotD
    exact ⟨x, hx⟩

/-- Explicit equivalence form of the size-two selector design: ambient
vertices are in bijection with the non-defect pairs inside `c`, and the
underlying pair of the equivalence is the component-neighbor selector. -/
theorem binarySquare_regular_sizeTwoPart_selector_equiv_nondefectPairs
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
    (hc : c.supp.ncard = q * 2) :
    ∃ E : V ≃ {s : Finset V // ∃ u v : c.supp,
        u ≠ v ∧ ¬(secondOrderDefectGraph G).Adj u.1 v.1 ∧ s = {u.1, v.1}},
      ∀ x, (E x).1 =
        componentNeighborFinset G (secondOrderDefectGraph G) c x := by
  let target := {s : Finset V | ∃ u v : c.supp,
    u ≠ v ∧ ¬(secondOrderDefectGraph G).Adj u.1 v.1 ∧ s = {u.1, v.1}}
  have hrange := binarySquare_regular_sizeTwoPart_componentNeighborFinset_range
    G hfree hq hreg hcard c hc
  let f : V → target := fun x =>
    ⟨componentNeighborFinset G (secondOrderDefectGraph G) c x, by
      have hxrange : componentNeighborFinset G (secondOrderDefectGraph G) c x ∈
          Set.range (fun y : V =>
            componentNeighborFinset G (secondOrderDefectGraph G) c y) := ⟨x, rfl⟩
      rw [hrange] at hxrange
      simpa [target] using hxrange⟩
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply binarySquare_regular_sizeTwoPart_componentNeighborFinset_injective
      G hfree hq hreg hcard c hc
    exact congrArg Subtype.val hxy
  have hfsurj : Function.Surjective f := by
    intro s
    have hs : s.1 ∈ {t : Finset V | ∃ u v : c.supp,
        u ≠ v ∧ ¬(secondOrderDefectGraph G).Adj u.1 v.1 ∧ t = {u.1, v.1}} := by
      simpa [target] using s.2
    rw [← hrange] at hs
    obtain ⟨x, hx⟩ := hs
    refine ⟨x, Subtype.ext ?_⟩
    exact hx
  refine ⟨Equiv.ofBijective f ⟨hfinj, hfsurj⟩, ?_⟩
  intro x
  rfl

/-- Kneser-style representation furnished by a normalized size-two component:
under the selector equivalence, every defect edge is sent to a pair of
disjoint two-element non-defect pairs. -/
theorem binarySquare_regular_sizeTwoPart_exists_selectorEquiv_maps_defectAdj_to_disjoint
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
    (hc : c.supp.ncard = q * 2) :
    ∃ E : V ≃ {s : Finset V // ∃ u v : c.supp,
        u ≠ v ∧ ¬(secondOrderDefectGraph G).Adj u.1 v.1 ∧ s = {u.1, v.1}},
      (∀ x, (E x).1 =
        componentNeighborFinset G (secondOrderDefectGraph G) c x) ∧
      ∀ ⦃x y : V⦄, (secondOrderDefectGraph G).Adj x y →
        Disjoint (E x).1 (E y).1 := by
  obtain ⟨E, hE⟩ :=
    binarySquare_regular_sizeTwoPart_selector_equiv_nondefectPairs
      G hfree hq hreg hcard c hc
  refine ⟨E, hE, ?_⟩
  intro x y hxy
  rw [hE x, hE y]
  exact componentNeighborFinset_disjoint_of_secondOrderDefect_adj
    G hfree hxy c

/-- Fix a vertex of a target defect component `c`.  The component-neighbor
selectors coming from a source defect component of normalized size `m`
contain that vertex exactly `m` times.  When `c` has normalized size two, the
complement-edge interpretation of the selector bijection says that each
source component gives an `m`-regular spanning edge layer on `c`. -/
theorem binarySquare_regular_selector_incidence_from_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    {m : ℕ} (he : e.supp.ncard = q * m) (u : c.supp) :
    ((e.supp.toFinite.toFinset).filter fun x =>
      u.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x).card = m := by
  let D := secondOrderDefectGraph G
  let S : Finset V := e.supp.toFinite.toFinset
  have hfinset :
      S.filter (fun x => u.1 ∈ componentNeighborFinset G D c x) =
        componentNeighborFinset G D e u.1 := by
    ext x
    constructor
    · intro hx
      have hx' := Finset.mem_filter.mp hx
      have hxSupp : x ∈ e.supp := by simpa [S] using hx'.1
      have hxComp : D.connectedComponentMk x = e :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff e x).mp hxSupp
      have huSel := Finset.mem_filter.mp hx'.2
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset u.1 x).mpr
            ((G.mem_neighborFinset x u.1).mp huSel.1).symm,
          hxComp⟩
    · intro hx
      rw [componentNeighborFinset] at hx
      have hx' := Finset.mem_filter.mp hx
      have hxSupp : x ∈ e.supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff e x).mpr hx'.2
      apply Finset.mem_filter.mpr
      refine ⟨by simpa [S] using hxSupp, ?_⟩
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset x u.1).mpr
            ((G.mem_neighborFinset u.1 x).mp hx'.1).symm,
          (SimpleGraph.ConnectedComponent.mem_supp_iff c u.1).mp u.2⟩
  change (S.filter fun x => u.1 ∈ componentNeighborFinset G D c x).card = m
  rw [hfinset]
  have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    G hfree hq hreg hcard c e (x := u.1) u.2
  rw [he] at hmul
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul

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

/-- At every vertex of a unit defect component, the unique ambient neighbor
inside that component is exactly the unique triangle-free neighbor. -/
theorem binarySquare_regular_sizeQ_component_triangleFree_degree_eq_one
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
    (hc : c.supp.ncard = q) (x : V)
    (hx : (secondOrderDefectGraph G).connectedComponentMk x = c) :
    (triangleFreeEdgeGraph G).degree x = 1 := by
  let D := secondOrderDefectGraph G
  have heq : triangleFreeNeighbors G x = componentNeighborFinset G D c x := by
    ext y
    constructor
    · intro hy
      have hyData := (mem_triangleFreeNeighbors G x y).mp hy
      have hDxy : D.Adj x y := by
        change (secondOrderDefectGraph G).Adj x y
        rw [secondOrderDefectGraph, SimpleGraph.sup_adj]
        exact Or.inr ((triangleFreeEdgeGraph_adj G x y).mpr hy)
      have hyc : D.connectedComponentMk y = c :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hDxy).symm.trans hx
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset x y).mpr hyData.1, hyc⟩
    · intro hy
      have hyData : G.Adj x y ∧ D.connectedComponentMk y = c := by
        rw [componentNeighborFinset] at hy
        exact ⟨(G.mem_neighborFinset x y).mp (Finset.mem_filter.mp hy).1,
          (Finset.mem_filter.mp hy).2⟩
      have hxy : x ≠ y := G.ne_of_adj hyData.1
      have hzero := binarySquare_regular_sizeQ_component_commonNeighbors_card_zero
        G hfree hq hreg hcard c hc hx hyData.2 hxy
      exact (mem_triangleFreeNeighbors G x y).mpr ⟨hyData.1, hzero⟩
  rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
    triangleFreeEdgeGraph_neighborFinset, heq]
  exact binarySquare_regular_card_componentNeighbors_sizeQ_eq_one
    G hfree hq hreg hcard c hc x

/-- No unit defect component can occur at even regular degree. -/
theorem binarySquare_regular_no_sizeQ_defectComponent_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    c.supp.ncard ≠ q := by
  intro hc
  obtain ⟨x, hx⟩ := c.nonempty_supp
  have htf := binarySquare_regular_sizeQ_component_triangleFree_degree_eq_one
    G hfree hq hreg hcard c hc x hx
  have hlocal := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  have htfcard : (triangleFreeNeighbors G x).card = 1 := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset] at htf
    exact htf
  rw [hreg x, htfcard] at hlocal
  obtain ⟨m, hm⟩ := hqEven
  omega

/-- In the all-unit partition, the triangle-free edges at a vertex are
exactly its unique ambient edge inside its own defect component. -/
theorem binarySquare_regular_allUnit_triangleFree_degree_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = q) (x : V) :
    (triangleFreeEdgeGraph G).degree x = 1 := by
  let D := secondOrderDefectGraph G
  let c := D.connectedComponentMk x
  have heq : triangleFreeNeighbors G x = componentNeighborFinset G D c x := by
    ext y
    constructor
    · intro hy
      have hyData := (mem_triangleFreeNeighbors G x y).mp hy
      have hDxy : D.Adj x y := by
        change (secondOrderDefectGraph G).Adj x y
        rw [secondOrderDefectGraph, SimpleGraph.sup_adj]
        exact Or.inr ((triangleFreeEdgeGraph_adj G x y).mpr hy)
      have hyc : D.connectedComponentMk y = c :=
        (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hDxy).symm
      rw [componentNeighborFinset]
      exact Finset.mem_filter.mpr
        ⟨(G.mem_neighborFinset x y).mpr hyData.1, hyc⟩
    · intro hy
      have hyData : G.Adj x y ∧ D.connectedComponentMk y = c := by
        rw [componentNeighborFinset] at hy
        exact ⟨(G.mem_neighborFinset x y).mp (Finset.mem_filter.mp hy).1,
          (Finset.mem_filter.mp hy).2⟩
      have hxy : x ≠ y := G.ne_of_adj hyData.1
      have hzero := binarySquare_regular_sizeQ_component_commonNeighbors_card_zero
        G hfree hq hreg hcard c (hall c) (by rfl) hyData.2 hxy
      exact (mem_triangleFreeNeighbors G x y).mpr ⟨hyData.1, hzero⟩
  rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
    triangleFreeEdgeGraph_neighborFinset, heq]
  exact binarySquare_regular_card_componentNeighbors_sizeQ_eq_one
    G hfree hq hreg hcard c (hall c) x

/-- **All-unit parity terminal.**  An all-unit defect partition forces exactly
one triangle-free edge at each vertex.  All remaining incident edges occur in
pairs inside triangles, so the regular degree is odd.  In particular no such
partition exists at positive even degree. -/
theorem binarySquare_regular_not_allUnit_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = q) : False := by
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by
    rw [hcard]
    positivity)
  let x : V := Classical.choice hV
  have hlocal := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  have htf := binarySquare_regular_allUnit_triangleFree_degree_eq_one
    G hfree hq hreg hcard hall x
  have htfcard : (triangleFreeNeighbors G x).card = 1 := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset] at htf
    exact htf
  rw [hreg x, htfcard] at hlocal
  obtain ⟨m, hm⟩ := hqEven
  omega

/-- Hence the all-unit defect-component partition is impossible at every
binary prime-power degree in the square-order range. -/
theorem binarySquare_regular_not_allUnit_of_two_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hq : 3 ≤ 2 ^ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 2 ^ k) : False := by
  have hk : k ≠ 0 := by
    intro hk
    simp [hk] at hq
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hEven : Even (2 ^ (j + 1)) := by
    refine ⟨2 ^ j, ?_⟩
    rw [pow_succ]
    omega
  exact binarySquare_regular_not_allUnit_of_even
    G hfree hq hEven hreg hcard hall

/-- Consequently the spanning graph of edges which lie in triangles is
`(q-1)`-regular in the all-unit partition. -/
theorem binarySquare_regular_allUnit_triangularEdge_degree_eq_pred
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = q) (x : V) :
    (triangularEdgeGraph G).degree x = q - 1 := by
  have hlocal := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  have htf := binarySquare_regular_allUnit_triangleFree_degree_eq_one
    G hfree hq hreg hcard hall x
  have htri := two_mul_localTriangleEdges_eq_triangularEdgeGraph_degree
    G hfree x
  have htfcard : (triangleFreeNeighbors G x).card = 1 := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset] at htf
    exact htf
  rw [hreg x, htfcard, htri] at hlocal
  omega

/-- **All-unit mod-three terminal.**  If every normalized component part is
one, the triangular-edge graph is `(q-1)`-regular and locally linear.  Its
handshake identity therefore makes `q²(q-1)` divisible by six, contradicting
`q ≡ 2 (mod 3)`. -/
theorem binarySquare_regular_not_allUnit_of_mod_three_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hmod : q % 3 = 2)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = q) : False := by
  let H := triangularEdgeGraph G
  have hHreg : ∀ x : V, H.degree x = q - 1 :=
    binarySquare_regular_allUnit_triangularEdge_degree_eq_pred
      G hfree hq hreg hcard hall
  have hhand := H.sum_degrees_eq_twice_card_edges
  simp_rw [hHreg] at hhand
  have hhand' : q * q * (q - 1) = 2 * H.edgeFinset.card := by
    simpa [hcard, mul_assoc] using hhand
  have hlinear : H.LocallyLinear :=
    triangularEdgeGraph_locallyLinear_of_not_containsC4 G hfree
  have hedge : H.edgeFinset.card =
      3 * (H.cliqueFinset 3).card := hlinear.card_edgeFinset
  rw [hedge] at hhand'
  have hpred : (q - 1) % 3 = 1 := by omega
  have hleft : (q * q * (q - 1)) % 3 = 1 := by
    simp [Nat.mul_mod, hmod, hpred]
  have hright : (2 * (3 * (H.cliqueFinset 3).card)) % 3 = 0 := by
    simp [Nat.mul_mod]
  have := congrArg (fun n : ℕ => n % 3) hhand'
  rw [hleft, hright] at this
  omega

/-- For square degree `q = 2^k`, the all-unit defect-component partition is
impossible whenever the exponent is odd. -/
theorem binarySquare_regular_not_allUnit_of_two_pow_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {k : ℕ} (hk : Odd k)
    (hq : 3 ≤ 2 ^ k)
    (hreg : ∀ x, G.degree x = 2 ^ k)
    (hcard : Fintype.card V = (2 ^ k) * (2 ^ k))
    (hall : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 2 ^ k) : False := by
  have hb : ((2 : ℕ) ^ 2) ≡ 1 [MOD 3] := by decide
  obtain ⟨m, rfl⟩ := hk
  have h4 : ((2 : ℕ) ^ 2) ^ m % 3 = 1 := by
    have hpow := hb.pow m
    simpa [Nat.ModEq] using hpow
  have hmod : 2 ^ (2 * m + 1) % 3 = 2 := by
    calc
      2 ^ (2 * m + 1) % 3 = ((2 : ℕ) ^ 2) ^ m * 2 % 3 := by
        rw [pow_succ, pow_mul]
      _ = (((2 : ℕ) ^ 2) ^ m % 3) * (2 % 3) % 3 := by
        rw [Nat.mul_mod]
      _ = 2 := by rw [h4]
  exact binarySquare_regular_not_allUnit_of_mod_three_eq_two
    G hfree hq hmod hreg hcard hall

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

/-- At even degree every normalized component order is at least two, so twice
the number of defect components is at most `q`. -/
theorem binarySquare_regular_two_mul_card_defectComponents_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    2 * Fintype.card (secondOrderDefectGraph G).ConnectedComponent ≤ q := by
  obtain ⟨m, hmSize, hmSum⟩ :=
    binarySquare_regular_exists_defectComponent_partition
      G hfree hq hreg hcard
  calc
    2 * Fintype.card (secondOrderDefectGraph G).ConnectedComponent =
        ∑ _c : (secondOrderDefectGraph G).ConnectedComponent, 2 := by simp [mul_comm]
    _ ≤ ∑ c : (secondOrderDefectGraph G).ConnectedComponent, m c := by
      apply Finset.sum_le_sum
      intro c _
      have hmpos : 0 < m c := by
        have hcpos : 0 < c.supp.ncard := c.nonempty_supp.ncard_pos
        by_contra hm0
        push Not at hm0
        have : m c = 0 := by omega
        rw [hmSize c, this, mul_zero] at hcpos
        omega
      have hmne : m c ≠ 1 := by
        intro hm
        have hc : c.supp.ncard = q := by simpa [hm] using hmSize c
        exact binarySquare_regular_no_sizeQ_defectComponent_of_even
          G hfree hq hqEven hreg hcard c hc
      omega
    _ = q := hmSum

end Erdos85
