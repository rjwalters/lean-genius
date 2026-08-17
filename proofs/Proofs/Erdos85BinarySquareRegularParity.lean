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
      p.length ≠ 4 := by
  have hdeg : ∀ x : c.supp, (G.induce c.supp).degree x = 2 :=
    fun x => binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree hq hreg hcard c hc x
  obtain ⟨x, p, hp, hpverts, hpgraph⟩ :=
    twoRegular_component_induce_eq_cycleSubgraph (G.induce c.supp) hdeg a
  refine ⟨x, p, hp, hpverts, hpgraph, ?_⟩
  intro hlen
  have hC4induced : containsC4 c.supp (G.induce c.supp) :=
    containsC4_of_isCycle_length_four hp hlen
  apply hfree
  rcases hC4induced with ⟨f, hf, hadj⟩
  exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
    fun i j hij => hadj i j hij⟩

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
