import Proofs.Erdos85DifferenceArray
import Proofs.Erdos85ZeroRowDifference
import Proofs.Erdos85EqualCycleTerminal

/-!
# Graph-facing symmetric difference-array bound

This assembles the orientation-free zero-row packing into the odd-involution
argument.  It is the terminal graph wrapper yielding `r ≤ d+3` for a
uniform odd defect-cycle decomposition once the standard quotient excess and
diagonal-mass identities have been supplied.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The intrinsic zero-row support has cardinality equal to the corresponding
component-quotient entry. -/
theorem card_graphCycleBlockZeroSupport_eq_componentQuotient
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (u v : ZMod r → V) (hv : Function.Injective v)
    (huRange : Set.range u = c.supp)
    (hvRange : Set.range v = e.supp) :
    (graphCycleBlockZeroSupport G u v).card =
      componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
  let D := secondOrderDefectGraph G
  have hu0c : u 0 ∈ c.supp := by
    rw [← huRange]
    exact ⟨0, rfl⟩
  have hQ := componentQuotientMatrix_apply_eq G D 2
    (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
    (adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree hd heven hmin hcard) c e hu0c
  rw [hQ]
  have heq : componentNeighborFinset G D e (u 0) =
      (graphCycleBlockZeroSupport G u v).image v := by
    ext y
    constructor
    · intro hy
      have hydata : G.Adj (u 0) y ∧ y ∈ e.supp := by
        simpa [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
          and_comm] using hy
      have hyrange : y ∈ Set.range v := by simpa [hvRange] using hydata.2
      obtain ⟨z, rfl⟩ := hyrange
      apply Finset.mem_image.mpr
      refine ⟨z, ?_, rfl⟩
      simpa [graphCycleBlockZeroSupport, zeroRowSupport,
        SimpleGraph.adjMatrix_apply, hydata.1]
    · intro hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hze : v z ∈ e.supp := by
        rw [← hvRange]
        exact ⟨z, rfl⟩
      have hAdj : G.Adj (u 0) (v z) := by
        simpa [graphCycleBlockZeroSupport, zeroRowSupport,
          SimpleGraph.adjMatrix_apply] using hz
      have hzmk : D.connectedComponentMk (v z) = e :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff e (v z)).mp hze
      simp [componentNeighborFinset, hAdj, hzmk]
  rw [heq, Finset.card_image_iff.mpr]
  intro x hx y hy hxy
  exact hv hxy

/-- Equal component orders make the rational quotient symmetric. -/
theorem secondOrder_equalComponents_quotientRat_isSymm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r) :
    (componentQuotientMatrixRat G (secondOrderDefectGraph G)).IsSymm := by
  rw [Matrix.IsSymm.ext_iff]
  intro c e
  have hbal := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard c e
  rw [hsize c, hsize e] at hbal
  have hrpos : 0 < r := by
    rw [← hsize c]
    exact c.nonempty_supp.ncard_pos
  simp only [componentQuotientMatrixRat]
  exact_mod_cast (Nat.eq_of_mul_eq_mul_left hrpos hbal).symm

/-- Equal-order quotient square equation over the rationals. -/
theorem secondOrder_equalComponents_quotientRat_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r) :
    let I := (secondOrderDefectGraph G).ConnectedComponent
    let Q := componentQuotientMatrixRat G (secondOrderDefectGraph G)
    Q * Q = ((d - 3 : ℕ) : ℚ) • (1 : Matrix I I ℚ) +
      (r : ℚ) • Matrix.of (fun _ _ ↦ 1) := by
  dsimp only
  apply Matrix.ext
  intro c e
  have hsq := secondOrder_componentQuotientMatrix_sq_apply
    G hfree hd heven hmin hcard c e
  rw [hsize e] at hsq
  simp only [Matrix.mul_apply] at hsq
  simp only [Matrix.mul_apply, componentQuotientMatrixRat,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
    smul_eq_mul, mul_one]
  exact_mod_cast hsq

/-- In the nonsquare branch, the equal-component quotient has natural trace
`d`; this is the exact diagonal-mass input for the difference array. -/
theorem secondOrder_equalComponents_quotient_trace_eq_degree_of_nonsquare
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r)
    (hcomp : 1 < Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent)
    (hnonsquare : ¬ IsSquare (d - 3)) :
    ∑ c, componentQuotientMatrix G (secondOrderDefectGraph G) c c = d := by
  let I := (secondOrderDefectGraph G).ConnectedComponent
  let Q := componentQuotientMatrixRat G (secondOrderDefectGraph G)
  have hsymm := secondOrder_equalComponents_quotientRat_isSymm
    G hfree hd heven hmin hcard hsize
  have hrow : ∀ i, ∑ j, Q i j = d := by
    intro i
    exact secondOrder_triangleComponents_quotientRat_row_sum
      G hfree hd heven hmin hcard i
  have hcol : ∀ j, ∑ i, Q i j = d := by
    intro j
    calc
      ∑ i, Q i j = ∑ i, Q j i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrFun (congrFun hsymm j) i
      _ = d := hrow j
  have hsq := secondOrder_equalComponents_quotientRat_sq
    G hfree hd heven hmin hcard hsize
  letI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; omega)
  letI : Nonempty (secondOrderDefectGraph G).ConnectedComponent :=
    ⟨(secondOrderDefectGraph G).connectedComponentMk
      (Classical.choice (inferInstance : Nonempty V))⟩
  have htrace := Matrix.trace_eq_degree_of_sq_rankOne_of_nonsquare
    Q hcomp hrow hcol (r : ℚ) (by simpa only [Q, I] using hsq) hnonsquare
  rw [Matrix.trace] at htrace
  have htrace' : (∑ c,
      (componentQuotientMatrix G (secondOrderDefectGraph G) c c : ℚ)) = d := by
    simpa only [Q, Matrix.diag, componentQuotientMatrixRat] using htrace
  exact_mod_cast htrace'

/-- In the nonsquare equal-cycle branch, the total ordered-difference mass
of all diagonal graph blocks is exactly `d`. -/
theorem secondOrder_equalComponents_diagonalDifferenceMass_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (hevenD : Even d) (hmin : d ≤ G.minDegree)
    (hcardV : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hcomp : 1 < Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent)
    (hnonsquare : ¬ IsSquare (d - 3)) :
    ∑ c, (orderedDifferenceSet
      (graphCycleBlockZeroSupport G (u c) (u c))).card = d := by
  let D := secondOrderDefectGraph G
  let A : D.ConnectedComponent → Finset (ZMod r) :=
    fun c ↦ graphCycleBlockZeroSupport G (u c) (u c)
  let q : D.ConnectedComponent → ℕ :=
    fun c ↦ componentQuotientMatrix G D c c
  have hsize : ∀ c : D.ConnectedComponent, c.supp.ncard = r := by
    intro c
    rw [← huRange c, Set.ncard_range_of_injective (hu c),
      Nat.card_eq_fintype_card, ZMod.card]
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd hevenD hmin hcardV
  have hcard : ∀ c, (A c).card = q c := by
    intro c
    exact card_graphCycleBlockZeroSupport_eq_componentQuotient
      G hfree hd hevenD hmin hcardV c c (u c) (u c) (hu c)
        (huRange c) (huRange c)
  have hsidon : ∀ c, IsOrderedSidon (A c) := by
    intro c
    have hOrient := graph_equalOddCycleBlock_orientation hr3 hrOdd G D
      (u c) (u c) (hu c) (hu c) hcomm (huD c) (huD c)
    exact isOrderedSidon_zeroRowSupport_of_c4Free_orientation
      G hfree (u c) (u c) (hu c) (hu c) hOrient
  have heven : ∀ c, Even (q c) := by
    intro c
    apply secondOrder_minimumComponent_diagonal_even
      G hfree hd hevenD hmin hcardV c
    intro e
    rw [hsize c, hsize e]
  have hle : ∀ c, q c ≤ 2 := by
    intro c
    exact secondOrder_equalOddCycleComponent_diagonal_le_two
      G hfree hd hevenD hmin hcardV hr3 hrOdd c (u c)
        (hu c) (huRange c) (huD c)
  have htrace : ∑ c, q c = d := by
    exact secondOrder_equalComponents_quotient_trace_eq_degree_of_nonsquare
      G hfree hd hevenD hmin hcardV hsize hcomp hnonsquare
  exact sum_diagonal_orderedDifference_card_eq_of_trace
    A q hcard hsidon heven hle htrace

/-- The local quotient square identity supplies exactly the quadratic excess
required by every zero-row difference packing. -/
theorem secondOrder_equalComponents_zeroRowSupport_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (hevenD : Even d) (hmin : d ≤ G.minDegree)
    (hcardV : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r)
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp) :
    ∀ c, ∑ e,
      (graphCycleBlockZeroSupport G (u c) (u e)).card *
        ((graphCycleBlockZeroSupport G (u c) (u e)).card - 1) = r - 3 := by
  let D := secondOrderDefectGraph G
  have hsize : ∀ c : D.ConnectedComponent, c.supp.ncard = r := by
    intro c
    rw [← huRange c, Set.ncard_range_of_injective (hu c),
      Nat.card_eq_fintype_card, ZMod.card]
  intro c
  have hqcard : ∀ e : D.ConnectedComponent,
      (graphCycleBlockZeroSupport G (u c) (u e)).card =
        componentQuotientMatrix G D c e := by
    intro e
    exact card_graphCycleBlockZeroSupport_eq_componentQuotient
      G hfree hd hevenD hmin hcardV c e (u c) (u e) (hu e)
        (huRange c) (huRange e)
  simp_rw [hqcard]
  have hsym : ∀ e : D.ConnectedComponent,
      componentQuotientMatrix G D c e =
        componentQuotientMatrix G D e c := by
    intro e
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree hd hevenD hmin hcardV c e
    rw [hsize c, hsize e] at hbal
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < r) hbal
  have hlocal := secondOrder_componentQuotientMatrix_local_excess
    G hfree hd hevenD hmin hcardV c
  have hlocal' :
      (∑ e, (componentQuotientMatrix G D c e : ℤ) *
        ((componentQuotientMatrix G D c e : ℤ) - 1)) =
          (r : ℤ) - 3 := by
    rw [← hsize c]
    rw [← hlocal]
    apply Finset.sum_congr rfl
    intro e he
    rw [hsym e]
    ring
  have hcast :
      ((↑(∑ e, componentQuotientMatrix G D c e *
        (componentQuotientMatrix G D c e - 1)) : ℤ)) =
      ∑ e, (componentQuotientMatrix G D c e : ℤ) *
        ((componentQuotientMatrix G D c e : ℤ) - 1) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hq : componentQuotientMatrix G D c e = 0
    · simp [hq]
    · rw [Nat.cast_mul, Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hq)]
      norm_num
  have hrCast : ((r - 3 : ℕ) : ℤ) = (r : ℤ) - 3 := by
    rw [Nat.cast_sub hr3]
    norm_num
  apply Int.ofNat_inj.mp
  rw [hcast, hrCast]
  exact hlocal'

theorem secondOrder_equalOddCycle_length_le_degree_add_three
    {V I : Type*} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (u : I → ZMod r → V)
    (hu : ∀ i, Function.Injective (u i))
    (huD : ∀ i x, (secondOrderDefectGraph G).neighborFinset (u i x) =
      {u i (x - 1), u i (x + 1)})
    (hsep : ∀ {i j : I}, i ≠ j → ∀ x y, u i x ≠ u j y)
    (hcomm : G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ)
    (hexcess : ∀ i, ∑ j,
      (graphCycleBlockZeroSupport G (u i) (u j)).card *
        ((graphCycleBlockZeroSupport G (u i) (u j)).card - 1) = r - 3)
    (hodd : Odd (Fintype.card I))
    (hdiag : ∑ i, (orderedDifferenceSet
      (graphCycleBlockZeroSupport G (u i) (u i))).card ≤ d) :
    r ≤ d + 3 := by
  let A : I → I → Finset (ZMod r) :=
    fun i j ↦ graphCycleBlockZeroSupport G (u i) (u j)
  have hsymm : ∀ i j,
      orderedDifferenceSet (A i j) = orderedDifferenceSet (A j i) := by
    intro i j
    exact orderedDifferenceSet_graphCycleBlockZeroSupport_symm
      hr3 hrOdd G (secondOrderDefectGraph G) (u i) (u j)
        (hu i) (hu j) hcomm (huD i) (huD j)
  have hleave : ∀ i, unusedOrderedDifferences (A i) = {1, -1} := by
    intro i
    exact unusedOrderedDifferences_graphCycleBlockZeroSupport_eq_one_negOne
      G hfree hd heven hmin hcard hr3 hrOdd (u i) u (hu i) (huD i)
        hu huD hsep hcomm (hexcess i)
  have hdisj : ∀ i, ∀ {j k : I}, j ≠ k →
      Disjoint (orderedDifferenceSet (A i j))
        (orderedDifferenceSet (A i k)) := by
    intro i j k hjk
    have hjOrient := graph_equalOddCycleBlock_orientation hr3 hrOdd G
      (secondOrderDefectGraph G) (u i) (u j) (hu i) (hu j)
        hcomm (huD i) (huD j)
    have hkOrient := graph_equalOddCycleBlock_orientation hr3 hrOdd G
      (secondOrderDefectGraph G) (u i) (u k) (hu i) (hu k)
        hcomm (huD i) (huD k)
    simpa only [A, graphCycleBlockZeroSupport] using
      (orderedDifferenceSet_zeroRowSupport_disjoint_of_c4Free_orientations
        G hfree (u i) (u j) (u k) (hu i) (hsep hjk)
          hjOrient hkOrient)
  apply cycleLength_le_degree_add_three_of_symmetric_difference_array
    hr3 A hsymm hleave hdisj hodd
  simpa only [A] using hdiag

/-- Fully assembled nonsquare equal-cycle bound.  All quotient excess and
diagonal-mass hypotheses of the preceding theorem are discharged from the
second-order boundary identities. -/
theorem secondOrder_equalOddCycle_length_le_degree_add_three_of_nonsquare
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (hevenD : Even d) (hmin : d ≤ G.minDegree)
    (hcardV : Fintype.card V = d * (d - 1) + 3)
    (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hcomp : 1 < Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent)
    (hodd : Odd (Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent))
    (hnonsquare : ¬ IsSquare (d - 3)) :
    r ≤ d + 3 := by
  let D := secondOrderDefectGraph G
  have hsep : ∀ {c e : D.ConnectedComponent}, c ≠ e →
      ∀ x y, u c x ≠ u e y := by
    intro c e hce x y hxy
    apply hce
    have hcx : D.connectedComponentMk (u c x) = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c (u c x)).mp (by
        rw [← huRange c]
        exact ⟨x, rfl⟩)
    have hey : D.connectedComponentMk (u e y) = e :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff e (u e y)).mp (by
        rw [← huRange e]
        exact ⟨y, rfl⟩)
    rw [← hcx, ← hey, hxy]
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd hevenD hmin hcardV
  have hexcess := secondOrder_equalComponents_zeroRowSupport_excess
    G hfree hd hevenD hmin hcardV hr3 u hu huRange
  have hdiagEq := secondOrder_equalComponents_diagonalDifferenceMass_eq_degree
    G hfree hd hevenD hmin hcardV hr3 hrOdd u hu huRange huD
      hcomp hnonsquare
  exact secondOrder_equalOddCycle_length_le_degree_add_three
    G hfree hd hevenD hmin hcardV hr3 hrOdd u hu huD hsep hcomm
      hexcess hodd (by simpa using hdiagEq.le)

end

end Erdos85
