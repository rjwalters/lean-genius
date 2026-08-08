import Proofs.Erdos85AbstractTraceEscape
import Proofs.Erdos85OneTwentyThreeTraceEscape
import Proofs.Erdos85SymmetricRestrictionSemisimple
import Proofs.Erdos85OneTwentyThreeArithmetic
import Proofs.Erdos85ExteriorCharpolyDivisibility
import Proofs.Erdos85OneTwentyThreeSemisimplePackage
import Proofs.Erdos85OwnerFiberProjectedSquare
import Proofs.Erdos85BoundaryQuotientDivisibility
import Proofs.Erdos85MixedDiagonalDichotomy
import Proofs.Erdos85OrientedFiveMass

/-!
# Scalar-123 residual terminal

The operator theorem below is the final contradiction engine.  The graph
wrapper transports the saturated owner-fiber hard sector into this engine.
-/

open Polynomial
open SimpleGraph

namespace Erdos85

noncomputable section

/-- Integral indicator vector of a finite vertex set. -/
def vertexFinsetIndicator {V : Type*} [DecidableEq V]
    (S : Finset V) : V → ℤ := fun x => if x ∈ S then 1 else 0

/-- Multiplying a finite-set indicator by an adjacency matrix counts the
neighbors lying in that set.  This is the bridge from the residual cell
degree formulas to the second-order matrix identity. -/
theorem adjMatrix_mulVec_vertexFinsetIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (x : V) :
    (G.adjMatrix ℤ).mulVec (vertexFinsetIndicator S) x =
      ((S ∩ G.neighborFinset x).card : ℤ) := by
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  rw [Finset.sum_congr rfl (fun y hy => by
    simp only [vertexFinsetIndicator]
    rfl)]
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have heq : (G.neighborFinset x).filter (fun y => y ∈ S) =
      S ∩ G.neighborFinset x := by
    ext y
    simp [and_comm]
  rw [heq]

/-- The all-ones matrix sends a finite-set indicator to its cardinality. -/
theorem onesMatrix_mulVec_vertexFinsetIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) :
    (FriendshipTheoremOQ01.onesMatrix V).mulVec (vertexFinsetIndicator S) =
      fun _ => (S.card : ℤ) := by
  funext x
  simp only [FriendshipTheoremOQ01.onesMatrix, Matrix.mulVec,
    dotProduct, one_mul]
  simp [vertexFinsetIndicator]

/-- A child vertex has exactly its child degree many ambient neighbors in
the minimum-layer image. -/
theorem minimumLayerImage_inter_neighborFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) {s : ℕ}
    (hregChild : ∀ x : minimumLayerVertex D c₀,
      (minimumLayerGraph G D c₀).degree x = s)
    (x : minimumLayerVertex D c₀) :
    (minimumLayerImageFinset D c₀ ∩ G.neighborFinset x.2.1).card = s := by
  classical
  let H := minimumLayerGraph G D c₀
  let ι : minimumLayerVertex D c₀ ↪ V :=
    ⟨minimumLayerVertexValue,
      minimumLayerVertexValue_injective (D := D) (c₀ := c₀)⟩
  have hinter : minimumLayerImageFinset D c₀ ∩ G.neighborFinset x.2.1 =
      (H.neighborFinset x).map ι := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzU, hzN⟩ := Finset.mem_inter.mp hz
      obtain ⟨q, _hq, hqz⟩ := Finset.mem_image.mp hzU
      subst z
      exact Finset.mem_map.mpr
        ⟨q, (H.mem_neighborFinset x q).mpr
          ((G.mem_neighborFinset x.2.1 q.2.1).mp hzN), rfl⟩
    · intro hz
      obtain ⟨q, hqN, hqz⟩ := Finset.mem_map.mp hz
      subst z
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩,
          (G.mem_neighborFinset x.2.1 q.2.1).mpr
            ((H.mem_neighborFinset x q).mp hqN)⟩
  rw [hinter, Finset.card_map, H.card_neighborFinset_eq_degree,
    hregChild x]

/-- The three-cell `(U,R,O)` adjacency quotient forced by a residual child
of degree `s` at ambient degree sixteen. -/
def degreeSixteenResidualQuotient (s : ℕ) : Matrix (Fin 3) (Fin 3) ℤ :=
  let p := s * (s - 1) + 3
  !![(s : ℤ), (16 - s : ℕ), 0;
     1, (p - s : ℕ), (16 - (1 + (p - s)) : ℕ);
     0, (p : ℤ), (16 - p : ℕ)]

set_option maxHeartbeats 800000 in
/-- All three surviving residual quotients have the same characteristic
polynomial, exposing the common nonprincipal factor `X² - 13`. -/
theorem degreeSixteenResidualQuotient_charpoly
    {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4) :
    (degreeSixteenResidualQuotient s).charpoly =
      (X - C (16 : ℤ)) * (X ^ 2 - C (13 : ℤ)) := by
  rcases hs with rfl | rfl | rfl <;>
    rw [show (degreeSixteenResidualQuotient _).charpoly =
      (Matrix.charmatrix (degreeSixteenResidualQuotient _)).det from rfl,
      Matrix.det_fin_three] <;>
    simp [degreeSixteenResidualQuotient, Matrix.charmatrix_apply_eq,
      Matrix.charmatrix_apply_ne] <;> ring

/-- **Operator-level scalar-123 terminal.**  Semisimplicity peels the
designated eigenvalue `2`; trace `-135` forces the residual trace nonzero,
while the arithmetic hypothesis and abstract trace escape force it zero. -/
theorem false_of_oneTwentyThree_semisimple_residual
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (S T : E →ₗ[ℚ] E) (hcomm : S * T = T * S)
    (hsq : S * S = (123 : ℚ) • (1 : E →ₗ[ℚ] E) - T)
    (htrace : LinearMap.trace ℚ E S = -(135 : ℚ))
    (hsemi : Module.End.IsSemisimple T)
    (harith : ∀ f : ℚ[X], f.Monic → Irreducible f → f ∣ T.charpoly →
      f ≠ X - C (2 : ℚ) → ¬ IsSquare (f.eval 123)) : False := by
  obtain ⟨r, hr2, hcop, hann, hrdvd⟩ :=
    exists_coprime_residual_annihilator_of_isSemisimple T hsemi 2
  have hne := residual_trace_ne_zero_of_sq_oneTwentyThree_of_trace_neg135
    S T hcomm r hcop hann hsq htrace
  have hzero := abstract_residual_trace_eq_zero
    S T hcomm hsq (LinearMap.aeval_self_charpoly T) hr2 hrdvd harith
  exact hne hzero

/-- **Graph-facing d=124 saturated terminal.**  A saturated `(124,12)`
minimum layer cannot exist: its canonical 112-fiber hard sector produces
the contradictory scalar-123 residual traces. -/
theorem no_minimumLayer_saturated_124_hardSector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 124 ≤ G.minDegree)
    (hcard : Fintype.card V = 124 * (124 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 12)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        12 * (12 - 1) + 3) : False := by
  classical
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let A := (G.comap (fun z : X => z.1)).adjMatrix ℚ
  let P := (D.comap (fun z : X => z.1)).adjMatrix ℚ
  have hhard := exists_minimumLayer_saturated_124_hardSector_square
    G hfree hmin hcard c₀ hregChild hcardChild
  obtain ⟨owner, huniform, hcommAE, hcommPE, htrace, hsq⟩ := hhard
  let E := normalizedOwnerProjection (K := ℚ) owner 112
  let Q : Matrix X X ℚ := 1 - E
  have hQ : Q * Q = Q := by
    simpa [Q, E, IsIdempotentElem] using
      (complement_normalizedOwnerProjection_isIdempotent
        (K := ℚ) owner 112 (by norm_num) huniform)
  have hcommAQ : A * Q = Q * A := by
    simp only [Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [hcommAE]
  have hcommPQ : P * Q = Q * P := by
    simp only [Q, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [hcommPE]
  have hPsymm : P.IsSymm := SimpleGraph.isSymm_adjMatrix _
  have hpkg := range_restrict_oneTwentyThree_semisimple_package
    A P Q hPsymm hQ hcommAQ hcommPQ htrace hsq
  dsimp only at hpkg
  obtain ⟨htraceR, hsqR, hcommR, hsemiR⟩ := hpkg
  apply false_of_oneTwentyThree_semisimple_residual _ _
    hcommR hsqR htraceR hsemiR
  intro f hfmonic hfirr hfdvd hfne
  obtain ⟨c, hc3, hcmax, hfcycle⟩ :=
    exteriorHardSector_irreducible_dvd_cycleChebyshev
      G hfree (d := 124) (by norm_num) (by exact ⟨62, by norm_num⟩)
        hmin hcard c₀ Q hQ hcommPQ f hfirr hfdvd
  have hcmax' : c.supp.ncard ≤ 15255 := by
    norm_num at hcard
    rwa [hcard] at hcmax
  exact oneTwentyThree_cycleFactor_eval_nonsquare_except_two
    c.supp.ncard hc3 hcmax' f hfmonic hfirr hfcycle hfne

/-- **Unconditional sharp minimum-layer descent.**  The scalar-123
terminal removes the final `(d,s)=(124,12)` saturated residual from
`secondOrder_minimumLayer_gap_or_degree_oneTwentyFour`. -/
theorem secondOrder_minimumLayer_strict_gap
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hd4 : d ≠ 4) (hd12 : d ≠ 12)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 ∧
      Even s ∧ s < d ∧ s * (s - 1) + 4 ≤ d := by
  obtain ⟨s, hreg, hcardChild, hsEven, hsd, hbranch⟩ :=
    secondOrder_minimumLayer_gap_or_degree_oneTwentyFour
      G hfree hd heven hmin hcard hd4 hd12 c₀ hc₀min
  refine ⟨s, hreg, hcardChild, hsEven, hsd, ?_⟩
  rcases hbranch with hresidual | hgap
  · obtain ⟨rfl, rfl, hc₀three, hcount⟩ := hresidual
    exact False.elim (no_minimumLayer_saturated_124_hardSector
      G hfree hmin hcard c₀ hreg hcardChild)
  · exact hgap

/-- At ambient degree sixteen, unconditional sharp descent leaves only the
three even child degrees `0`, `2`, and `4`. -/
theorem secondOrder_degree_sixteen_minimumLayer_degree_zero_two_or_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard) :
    ∃ s : ℕ,
      (s = 0 ∨ s = 2 ∨ s = 4) ∧
      (∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s) ∧
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3 := by
  obtain ⟨s, hreg, hcardChild, hsEven, hsd, hgap⟩ :=
    secondOrder_minimumLayer_strict_gap G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard (by norm_num) (by norm_num)
        c₀ hc₀min
  obtain ⟨k, hk⟩ := hsEven
  have hcases : s = 0 ∨ s = 2 ∨ s = 4 := by
    interval_cases s <;> norm_num at hgap <;> omega
  exact ⟨s, hcases, hreg, hcardChild⟩

/-- Exact cardinality of the exterior vertices missed by every disjoint
child-to-complement incidence row. -/
theorem minimumLayer_unused_exterior_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    ((Finset.univ \ U) \ Finset.univ.biUnion E).card =
      (d * (d - 1) + 3 - (s * (s - 1) + 3)) -
        (s * (s - 1) + 3) * (d - s) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨a, rfl⟩ : ∃ a : ℕ, d = a + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hcardE : ∀ x : minimumLayerVertex D c₀, (E x).card = d - s := by
    intro x
    exact card_minimumLayerExternalNeighborFinset G D c₀
      hregParent hregChild x
  have hcardChildD : Fintype.card (minimumLayerVertex D c₀) =
      s * (s - 1) + 3 := by
    simpa [D] using hcardChild
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hunionCard : (Finset.univ.biUnion E).card =
      (s * (s - 1) + 3) * (d - s) := by
    rw [Finset.card_biUnion hpair]
    rw [Finset.sum_congr rfl (fun x _ => hcardE x)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcardChildD]
    norm_num
  have hunionSub : Finset.univ.biUnion E ⊆ Finset.univ \ U :=
    minimumLayer_externalBiUnion_subset_complement G D c₀
  rw [Finset.card_sdiff_of_subset hunionSub, hunionCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ U),
    Finset.card_univ, card_minimumLayerImageFinset, hcard, hcardChild]

/-- In the tight d=16, s=4 extension, exactly 48 exterior vertices are
orphans—missed by every child external-neighborhood row. -/
theorem degree_sixteen_fourLayer_unused_exterior_card_eq_fortyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    ((Finset.univ \ U) \ Finset.univ.biUnion E).card = 48 := by
  have h := minimumLayer_unused_exterior_card G hfree (d := 16) (s := 4)
    (by norm_num) (by norm_num) hmin hcard c₀ hregChild (by
      norm_num
      exact hcardChild)
  norm_num at h ⊢
  exact h

/-- Every orphan exterior vertex is serviced exactly once by each child
row: its neighborhood meets that row's external-neighbor set in one point. -/
theorem minimumLayer_orphan_service_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀))
    (u : minimumLayerVertex (secondOrderDefectGraph G) c₀) :
    (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀ u ∩
      G.neighborFinset z).card = 1 := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hzNoChildAdj : ∀ v : minimumLayerVertex D c₀, ¬ G.Adj z v.2.1 := by
    intro v hzv
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨v, Finset.mem_univ _, ?_⟩
    exact Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset v.2.1 z).mpr hzv.symm, hzOutside⟩
  have hzNotD : ¬ D.Adj u.2.1 z := by
    intro hD
    have hcomp : D.connectedComponentMk z = u.1.1 :=
      (ConnectedComponent.connectedComponentMk_eq_of_adj hD.symm).trans
        ((ConnectedComponent.mem_supp_iff u.1.1 u.2.1).mp u.2.2)
    have hzSupp : z ∈ u.1.1.supp :=
      (ConnectedComponent.mem_supp_iff u.1.1 z).mpr hcomp
    apply hzOutside
    exact Finset.mem_image.mpr
      ⟨⟨u.1, ⟨z, hzSupp⟩⟩, Finset.mem_univ _, rfl⟩
  have huz : u.2.1 ≠ z := by
    intro huz
    apply hzOutside
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, huz⟩
  have hcommon := card_common_eq_if_secondOrderDefect G hfree u.2.1 z huz
  have hzNotMem : z ∉ D.neighborFinset u.2.1 := by
    simpa [D.mem_neighborFinset] using hzNotD
  rw [if_neg hzNotMem] at hcommon
  have hnonempty : (G.neighborFinset u.2.1 ∩ G.neighborFinset z).Nonempty :=
    Finset.card_pos.mp (by omega)
  let q := hnonempty.choose
  have hqmem := hnonempty.choose_spec
  have ⟨hqu, hqz⟩ := Finset.mem_inter.mp hqmem
  have hqOutside : q ∉ U := by
    intro hqU
    obtain ⟨v, _hv, hvq⟩ := Finset.mem_image.mp hqU
    apply hzNoChildAdj v
    have hzq : G.Adj z q := (G.mem_neighborFinset z q).mp hqz
    change v.2.1 = q at hvq
    rwa [hvq]
  have hserviceNonempty : (E u ∩ G.neighborFinset z).Nonempty := by
    exact ⟨q, Finset.mem_inter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hqu, hqOutside⟩, hqz⟩⟩
  have hsub : E u ∩ G.neighborFinset z ⊆
      G.neighborFinset u.2.1 ∩ G.neighborFinset z := by
    intro y hy
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_sdiff.mp (Finset.mem_inter.mp hy).1).1,
        (Finset.mem_inter.mp hy).2⟩
  have hle := Finset.card_le_card hsub
  have hpos := Finset.card_pos.mpr hserviceNonempty
  change (E u ∩ G.neighborFinset z).card = 1
  omega

/-- The rowwise service law summed over the disjoint exterior rows: every
orphan has exactly `s(s-1)+3` neighbors in the used exterior, one for each
vertex of the minimum-layer child. -/
theorem minimumLayer_orphan_used_exterior_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    (Finset.univ.biUnion
        (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀) ∩ G.neighborFinset z).card =
      s * (s - 1) + 3 := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hpairInter :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u => E u ∩ G.neighborFinset z) := by
    intro u hu v hv huv
    exact Finset.disjoint_of_subset_left (Finset.inter_subset_left)
      (Finset.disjoint_of_subset_right (Finset.inter_subset_left)
        (hpair hu hv huv))
  have heq : Finset.univ.biUnion E ∩ G.neighborFinset z =
      Finset.univ.biUnion (fun u => E u ∩ G.neighborFinset z) := by
    ext y
    simp
  rw [heq, Finset.card_biUnion hpairInter]
  have hservice : ∀ u : minimumLayerVertex D c₀,
      (E u ∩ G.neighborFinset z).card = 1 := by
    intro u
    exact minimumLayer_orphan_service_card_eq_one
      G hfree hd heven hmin hcard c₀ hregChild hcardChild
        z hzOutside hzUnused u
  simp_rw [hservice]
  simpa [D] using hcardChild

/-- At ambient degree sixteen, the exact one-service-per-child-row law
leaves `16 - |U|` nonservice neighbors at every orphan, uniformly in the
minimum-layer child degree. -/
theorem degree_sixteen_minimumLayer_orphan_unserviced_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ}
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
      E u ∩ G.neighborFinset z)
    (G.neighborFinset z \ S).card = 16 - (s * (s - 1) + 3) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
    E u ∩ G.neighborFinset z)
  have hbelow : Fintype.card V < (16 + 1) * (16 - 1) + 1 := by
    rw [hcard]
    norm_num
  have hregParent : ∀ v : V, G.degree v = 16 :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by norm_num) hmin hbelow
  have hpairE := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  have hpairS :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u => E u ∩ G.neighborFinset z) := by
    intro u hu v hv huv
    change Disjoint (E u ∩ G.neighborFinset z)
      (E v ∩ G.neighborFinset z)
    rw [Finset.disjoint_left]
    intro q hqu hqv
    exact (Finset.disjoint_left.mp (hpairE hu hv huv))
      (Finset.mem_inter.mp hqu).1 (Finset.mem_inter.mp hqv).1
  have hservice : ∀ u : minimumLayerVertex D c₀,
      (E u ∩ G.neighborFinset z).card = 1 := by
    intro u
    exact minimumLayer_orphan_service_card_eq_one
      G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild hcardChild z hzOutside hzUnused u
  have hcardS : S.card = s * (s - 1) + 3 := by
    change (Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
      E u ∩ G.neighborFinset z)).card = s * (s - 1) + 3
    rw [Finset.card_biUnion hpairS]
    rw [Finset.sum_congr rfl (fun u _ => hservice u)]
    simp [hcardChild, D]
  have hSsub : S ⊆ G.neighborFinset z := by
    intro q hq
    obtain ⟨u, hu, hq⟩ := Finset.mem_biUnion.mp hq
    exact (Finset.mem_inter.mp hq).2
  rw [Finset.card_sdiff_of_subset hSsub, hcardS,
    G.card_neighborFinset_eq_degree, hregParent z]

/-- Concrete residual degrees for the three surviving degree-sixteen
children: `13`, `11`, and `1` at child degrees `0`, `2`, and `4`. -/
theorem degree_sixteen_minimumLayer_orphan_unserviced_neighbor_card_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ}
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
      E u ∩ G.neighborFinset z)
    (G.neighborFinset z \ S).card =
      if s = 0 then 13 else if s = 2 then 11 else 1 := by
  rcases hs with rfl | rfl | rfl <;>
    simpa using degree_sixteen_minimumLayer_orphan_unserviced_neighbor_card
      G hfree hmin hcard c₀ hregChild hcardChild z hzOutside hzUnused

/-- In the d=16, s=4 branch, the fifteen exact service points consume all
but one neighbor of each orphan exterior vertex. -/
theorem degree_sixteen_fourLayer_orphan_unserviced_neighbor_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hzOutside : z ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀)
    (hzUnused : z ∉ Finset.univ.biUnion
      (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
      E u ∩ G.neighborFinset z)
    (G.neighborFinset z \ S).card = 1 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
    E u ∩ G.neighborFinset z)
  have hbelow : Fintype.card V < (16 + 1) * (16 - 1) + 1 := by
    rw [hcard]
    norm_num
  have hregParent : ∀ v : V, G.degree v = 16 :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by norm_num) hmin hbelow
  have hpairE := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild (by norm_num; exact hcardChild)
  have hpairS :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u => E u ∩ G.neighborFinset z) := by
    intro u hu v hv huv
    change Disjoint (E u ∩ G.neighborFinset z)
      (E v ∩ G.neighborFinset z)
    rw [Finset.disjoint_left]
    intro q hqu hqv
    exact (Finset.disjoint_left.mp (hpairE hu hv huv))
      (Finset.mem_inter.mp hqu).1 (Finset.mem_inter.mp hqv).1
  have hservice : ∀ u : minimumLayerVertex D c₀,
      (E u ∩ G.neighborFinset z).card = 1 := by
    intro u
    exact minimumLayer_orphan_service_card_eq_one
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) z hzOutside hzUnused u
  have hcardS : S.card = 15 := by
    change (Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
      E u ∩ G.neighborFinset z)).card = 15
    rw [Finset.card_biUnion hpairS]
    rw [Finset.sum_congr rfl (fun u _ => hservice u)]
    simp [hcardChild, D]
  have hSsub : S ⊆ G.neighborFinset z := by
    intro q hq
    obtain ⟨u, hu, hq⟩ := Finset.mem_biUnion.mp hq
    exact (Finset.mem_inter.mp hq).2
  rw [Finset.card_sdiff_of_subset hSsub, hcardS,
    G.card_neighborFinset_eq_degree, hregParent z]

/-- The nonservice neighbors are exactly the neighbors remaining inside the
orphan set.  Hence the orphan-induced residual degree is
`16 - (s(s-1)+3)` for every degree-sixteen child. -/
theorem degree_sixteen_minimumLayer_orphan_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ}
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion
          (minimumLayerExternalNeighborFinset G
            (secondOrderDefectGraph G) c₀)) :
    (((Finset.univ \
        minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
          Finset.univ.biUnion
            (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) ∩
        G.neighborFinset z).card = 16 - (s * (s - 1) + 3) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
    E u ∩ G.neighborFinset z)
  have hzO : z ∈ O := hz
  have hzOutside : z ∉ U := (Finset.mem_sdiff.mp
    (Finset.mem_sdiff.mp hzO).1).2
  have hzUnused : z ∉ Finset.univ.biUnion E :=
    (Finset.mem_sdiff.mp hzO).2
  have hzNoChildAdj : ∀ v : minimumLayerVertex D c₀,
      ¬G.Adj z v.2.1 := by
    intro v hzv
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨v, Finset.mem_univ _, ?_⟩
    exact Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset v.2.1 z).mpr hzv.symm, hzOutside⟩
  have heq : O ∩ G.neighborFinset z = G.neighborFinset z \ S := by
    ext y
    constructor
    · intro hy
      have hyO := (Finset.mem_inter.mp hy).1
      have hyN := (Finset.mem_inter.mp hy).2
      refine Finset.mem_sdiff.mpr ⟨hyN, ?_⟩
      intro hyS
      obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.mp hyS
      exact (Finset.mem_sdiff.mp hyO).2
        (Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_univ _, (Finset.mem_inter.mp hyu).1⟩)
    · intro hy
      have hyN := (Finset.mem_sdiff.mp hy).1
      have hyNotS := (Finset.mem_sdiff.mp hy).2
      have hyOutside : y ∉ U := by
        intro hyU
        obtain ⟨v, _hv, hvy⟩ := Finset.mem_image.mp hyU
        apply hzNoChildAdj v
        change v.2.1 = y at hvy
        rw [hvy]
        exact (G.mem_neighborFinset z y).mp hyN
      have hyUnused : y ∉ Finset.univ.biUnion E := by
        intro hyUsed
        obtain ⟨u, hu, hyE⟩ := Finset.mem_biUnion.mp hyUsed
        apply hyNotS
        exact Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hyE, hyN⟩⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyOutside⟩, hyUnused⟩,
          hyN⟩
  rw [heq]
  exact degree_sixteen_minimumLayer_orphan_unserviced_neighbor_card
    G hfree hmin hcard c₀ hregChild hcardChild z hzOutside hzUnused

/-- Encoder-facing graph form of the degree-sixteen orphan calculation.
The induced orphan graph has the exact order and regular degree forced by
the child degree, and the handshake identity fixes twice its edge count. -/
theorem degree_sixteen_minimumLayer_orphan_induced_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ}
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    let H := G.induce (O : Set V)
    O.card =
        (16 * (16 - 1) + 3 - (s * (s - 1) + 3)) -
          (s * (s - 1) + 3) * (16 - s) ∧
      (∀ z : (O : Set V), H.degree z = 16 - (s * (s - 1) + 3)) ∧
      2 * H.edgeFinset.card =
        O.card * (16 - (s * (s - 1) + 3)) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let H := G.induce (O : Set V)
  have hcardO : O.card =
      (16 * (16 - 1) + 3 - (s * (s - 1) + 3)) -
        (s * (s - 1) + 3) * (16 - s) :=
    minimumLayer_unused_exterior_card G hfree (d := 16) (s := s)
      (by norm_num) (by norm_num) hmin hcard c₀ hregChild hcardChild
  have hdegreeCard : ∀ z : (O : Set V), H.degree z =
      (O ∩ G.neighborFinset z.1).card := by
    intro z
    rw [← H.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      exact Finset.mem_inter.mpr
        ⟨y.2, (G.mem_neighborFinset z.1 y.1).mpr
          ((H.mem_neighborFinset z y).mp hy)⟩
    · intro y _ y' _ hyy
      exact Subtype.ext hyy
    · intro y hy
      let y' : (O : Set V) := ⟨y, (Finset.mem_inter.mp hy).1⟩
      refine ⟨y', ?_, rfl⟩
      exact (H.mem_neighborFinset z y').mpr
        ((G.mem_neighborFinset z.1 y).mp (Finset.mem_inter.mp hy).2)
  have hregular : ∀ z : (O : Set V),
      H.degree z = 16 - (s * (s - 1) + 3) := by
    intro z
    rw [hdegreeCard]
    exact degree_sixteen_minimumLayer_orphan_neighbor_card
      G hfree hmin hcard c₀ hregChild hcardChild z.1 z.2
  refine ⟨hcardO, hregular, ?_⟩
  calc
    2 * H.edgeFinset.card = ∑ z : (O : Set V), H.degree z :=
      H.sum_degrees_eq_twice_card_edges.symm
    _ = ∑ _z : (O : Set V), (16 - (s * (s - 1) + 3)) := by
      apply Finset.sum_congr rfl
      intro z _hz
      exact hregular z
    _ = O.card * (16 - (s * (s - 1) + 3)) := by simp

/-- In the `s = 0` branch the orphan graph is 13-regular on 192 vertices
and has 1248 edges. -/
theorem degree_sixteen_zeroLayer_orphan_induced_parameters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 0)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 3) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let H := G.induce (O : Set V)
    O.card = 192 ∧ (∀ z : (O : Set V), H.degree z = 13) ∧
      H.edgeFinset.card = 1248 := by
  obtain ⟨hO, hreg, hedges⟩ :=
    degree_sixteen_minimumLayer_orphan_induced_regular
      G hfree (s := 0) hmin hcard c₀ hregChild (by norm_num; exact hcardChild)
  dsimp only at hO hreg hedges ⊢
  refine ⟨by norm_num at hO ⊢; exact hO, by simpa using hreg, ?_⟩
  norm_num [hO] at hedges ⊢
  omega

/-- In the `s = 2` branch the orphan graph is 11-regular on 168 vertices
and has 924 edges. -/
theorem degree_sixteen_twoLayer_orphan_induced_parameters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let H := G.induce (O : Set V)
    O.card = 168 ∧ (∀ z : (O : Set V), H.degree z = 11) ∧
      H.edgeFinset.card = 924 := by
  obtain ⟨hO, hreg, hedges⟩ :=
    degree_sixteen_minimumLayer_orphan_induced_regular
      G hfree (s := 2) hmin hcard c₀ hregChild (by norm_num; exact hcardChild)
  dsimp only at hO hreg hedges ⊢
  refine ⟨by norm_num at hO ⊢; exact hO, by simpa using hreg, ?_⟩
  norm_num [hO] at hedges ⊢
  omega

/-- The 48 orphan vertices in the tight d=16, s=4 branch induce a
one-regular graph: every orphan's unique non-service neighbor is another
orphan. -/
theorem degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion
          (minimumLayerExternalNeighborFinset G (secondOrderDefectGraph G) c₀)) :
    (((Finset.univ \
        minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
          Finset.univ.biUnion
            (minimumLayerExternalNeighborFinset G
              (secondOrderDefectGraph G) c₀)) ∩
        G.neighborFinset z).card = 1 := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let S := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
    E u ∩ G.neighborFinset z)
  have hzO : z ∈ O := hz
  have hzOutside : z ∉ U := (Finset.mem_sdiff.mp
    (Finset.mem_sdiff.mp hzO).1).2
  have hzUnused : z ∉ Finset.univ.biUnion E :=
    (Finset.mem_sdiff.mp hzO).2
  have hzNoChildAdj : ∀ v : minimumLayerVertex D c₀, ¬ G.Adj z v.2.1 := by
    intro v hzv
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨v, Finset.mem_univ _, ?_⟩
    exact Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset v.2.1 z).mpr hzv.symm, hzOutside⟩
  have heq : O ∩ G.neighborFinset z = G.neighborFinset z \ S := by
    ext y
    constructor
    · intro hy
      have hyO := (Finset.mem_inter.mp hy).1
      have hyN := (Finset.mem_inter.mp hy).2
      refine Finset.mem_sdiff.mpr ⟨hyN, ?_⟩
      intro hyS
      obtain ⟨u, hu, hyu⟩ := Finset.mem_biUnion.mp hyS
      exact (Finset.mem_sdiff.mp hyO).2
        (Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_univ _, (Finset.mem_inter.mp hyu).1⟩)
    · intro hy
      have hyN := (Finset.mem_sdiff.mp hy).1
      have hyNotS := (Finset.mem_sdiff.mp hy).2
      have hyOutside : y ∉ U := by
        intro hyU
        obtain ⟨v, _hv, hvy⟩ := Finset.mem_image.mp hyU
        apply hzNoChildAdj v
        change v.2.1 = y at hvy
        rw [hvy]
        exact (G.mem_neighborFinset z y).mp hyN
      have hyUnused : y ∉ Finset.univ.biUnion E := by
        intro hyUsed
        obtain ⟨u, hu, hyE⟩ := Finset.mem_biUnion.mp hyUsed
        apply hyNotS
        exact Finset.mem_biUnion.mpr
          ⟨u, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hyE, hyN⟩⟩
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyOutside⟩, hyUnused⟩,
          hyN⟩
  rw [heq]
  exact degree_sixteen_fourLayer_orphan_unserviced_neighbor_card_eq_one
    G hfree hmin hcard c₀ hregChild hcardChild z hzOutside hzUnused

/-- Graph form of the orphan matching: the induced orphan graph is
one-regular on 48 vertices and therefore has exactly 24 edges. -/
theorem degree_sixteen_fourLayer_orphan_induced_oneRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    let H := G.induce (O : Set V)
    (∀ z : (O : Set V), H.degree z = 1) ∧ H.edgeFinset.card = 24 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let H := G.induce (O : Set V)
  have hcardO : O.card = 48 := by
    exact degree_sixteen_fourLayer_unused_exterior_card_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  have hdegreeCard : ∀ z : (O : Set V), H.degree z =
      (O ∩ G.neighborFinset z.1).card := by
    intro z
    rw [← H.card_neighborFinset_eq_degree]
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      have hzy : G.Adj z.1 y.1 := (H.mem_neighborFinset z y).mp hy
      exact Finset.mem_inter.mpr
        ⟨y.2, (G.mem_neighborFinset z.1 y.1).mpr hzy⟩
    · intro y hy₁ y' hy₂ hyy
      exact Subtype.ext hyy
    · intro y hy
      let y' : (O : Set V) := ⟨y, (Finset.mem_inter.mp hy).1⟩
      refine ⟨y', ?_, rfl⟩
      apply (H.mem_neighborFinset z y').mpr
      exact (G.mem_neighborFinset z.1 y).mp (Finset.mem_inter.mp hy).2
  have hdegreeOne : ∀ z : (O : Set V), H.degree z = 1 := by
    intro z
    rw [hdegreeCard]
    exact degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild z.1 z.2
  refine ⟨hdegreeOne, ?_⟩
  have hsum : ∑ z : (O : Set V), H.degree z = 48 := by
    simp_rw [hdegreeOne]
    simp [hcardO]
  have hedges : 48 = 2 * H.edgeFinset.card := by
    calc
      48 = ∑ z : (O : Set V), H.degree z := hsum.symm
      _ = 2 * H.edgeFinset.card := H.sum_degrees_eq_twice_card_edges
  apply Nat.mul_left_cancel (n := 2) (by norm_num)
  calc
    2 * H.edgeFinset.card = 48 := hedges.symm
    _ = 2 * 24 := by norm_num

/-- Two distinct orphans can be co-serviced in at most one child row.
More precisely, common service points belonging to two child rows force the
rows to coincide.  This is the `λ ≤ 1` packing law behind the d=16 terminal. -/
theorem degree_sixteen_fourLayer_shared_service_row_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V} (hzz' : z ≠ z')
    {u v : minimumLayerVertex (secondOrderDefectGraph G) c₀}
    {y y' : V}
    (hyu : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ u)
    (hyz : G.Adj z y) (hyz' : G.Adj z' y)
    (hy'v : y' ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v)
    (hy'z : G.Adj z y') (hy'z' : G.Adj z' y') :
    u = v := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hcommon := common_le_one_of_not_containsC4 hfree z z' hzz'
  have hyCommon : y ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y).mpr hyz,
        (G.mem_neighborFinset z' y).mpr hyz'⟩
  have hy'Common : y' ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y').mpr hy'z,
        (G.mem_neighborFinset z' y').mpr hy'z'⟩
  have hyy' : y = y' :=
    Finset.card_le_one.mp hcommon y hyCommon y' hy'Common
  by_contra huv
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild (by norm_num; exact hcardChild)
  have hdisj : Disjoint (E u) (E v) :=
    hpair (Finset.mem_univ u) (Finset.mem_univ v) huv
  exact (Finset.disjoint_left.mp hdisj) hyu (hyy' ▸ hy'v)

/-- If two distinct orphans share no service point, then they are adjacent in
the second-order defect graph.  The only possible common neighbors of two
orphans are service points: a common orphan neighbor would violate the
one-regularity of the induced orphan graph. -/
theorem degree_sixteen_fourLayer_uncovered_orphans_defect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : z ≠ z')
    (huncovered : ∀ u : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      ∀ y ∈ minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ u,
        ¬(G.Adj z y ∧ G.Adj z' y)) :
    (secondOrderDefectGraph G).Adj z z' := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  have hzO : z ∈ O := hz
  have hz'O : z' ∈ O := hz'
  have hzUnused : z ∉ Finset.univ.biUnion E :=
    (Finset.mem_sdiff.mp hzO).2
  have hzNoChildAdj : ∀ v : minimumLayerVertex D c₀,
      ¬G.Adj z v.2.1 := by
    intro v hzv
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨v, Finset.mem_univ _, ?_⟩
    exact Finset.mem_sdiff.mpr
      ⟨(G.mem_neighborFinset v.2.1 z).mpr hzv.symm,
        (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hzO).1).2⟩
  have hcommonEmpty :
      G.neighborFinset z ∩ G.neighborFinset z' = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨y, hy⟩
    have hyz : G.Adj z y :=
      (G.mem_neighborFinset z y).mp (Finset.mem_inter.mp hy).1
    have hyz' : G.Adj z' y :=
      (G.mem_neighborFinset z' y).mp (Finset.mem_inter.mp hy).2
    have hyOutside : y ∉ U := by
      intro hyU
      obtain ⟨v, _hv, hvy⟩ := Finset.mem_image.mp hyU
      apply hzNoChildAdj v
      change v.2.1 = y at hvy
      rwa [hvy]
    have hyUnused : y ∉ Finset.univ.biUnion E := by
      intro hyUsed
      obtain ⟨u, _hu, hyE⟩ := Finset.mem_biUnion.mp hyUsed
      exact huncovered u y hyE ⟨hyz, hyz'⟩
    have hyO : y ∈ O := Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyOutside⟩, hyUnused⟩
    have hone := degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild y hyO
    have hzMem : z ∈ O ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr
        ⟨hzO, (G.mem_neighborFinset y z).mpr hyz.symm⟩
    have hz'Mem : z' ∈ O ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr
        ⟨hz'O, (G.mem_neighborFinset y z').mpr hyz'.symm⟩
    have hone' : (O ∩ G.neighborFinset y).card ≤ 1 := by
      rw [hone]
    exact hzz' (Finset.card_le_one.mp hone' z hzMem z' hz'Mem)
  have hcommonCard :
      (G.neighborFinset z ∩ G.neighborFinset z').card = 0 := by
    rw [hcommonEmpty]
    simp
  have hformula := card_common_eq_if_secondOrderDefect G hfree z z' hzz'
  by_contra hnotD
  have hnotMem : z' ∉ D.neighborFinset z := by
    simpa [D.mem_neighborFinset] using hnotD
  rw [if_neg hnotMem] at hformula
  omega

/-- Every orphan has at most two uncovered orphan partners.  All such
partners are defect neighbors, while the exact-boundary defect graph has
degree two. -/
theorem degree_sixteen_fourLayer_uncovered_orphan_card_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    ((O.erase z).filter (fun z' =>
      ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
        ¬(G.Adj z y ∧ G.Adj z' y))).card ≤ 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  let C := (O.erase z).filter (fun z' =>
    ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
      ¬(G.Adj z y ∧ G.Adj z' y))
  have hsub : C ⊆ D.neighborFinset z := by
    intro z' hz'C
    have hz'Filter := Finset.mem_filter.mp hz'C
    have hz'O : z' ∈ O := Finset.mem_of_mem_erase hz'Filter.1
    have hzz' : z ≠ z' := Ne.symm (Finset.ne_of_mem_erase hz'Filter.1)
    apply (D.mem_neighborFinset z z').mpr
    exact degree_sixteen_fourLayer_uncovered_orphans_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hz'O hzz'
        hz'Filter.2
  have hle := Finset.card_le_card hsub
  have hdeg : D.degree z = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree (by norm_num)
      (by norm_num) hmin hcard z
  rw [D.card_neighborFinset_eq_degree, hdeg] at hle
  exact hle

/-- Consequently, each orphan has at least 45 covered partners among the
other 47 orphans.  `Covered` here means the complement of the row-wise
uncovered predicate; a following lemma can unpack it into a shared service
point. -/
theorem degree_sixteen_fourLayer_covered_orphan_card_ge_fortyFive
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    let P := O.erase z
    let C := P.filter (fun z' =>
      ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
        ¬(G.Adj z y ∧ G.Adj z' y))
    45 ≤ (P \ C).card := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  let P := O.erase z
  let C := P.filter (fun z' =>
    ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
      ¬(G.Adj z y ∧ G.Adj z' y))
  have hcardO : O.card = 48 :=
    degree_sixteen_fourLayer_unused_exterior_card_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  have hcardP : P.card = 47 := by
    rw [Finset.card_erase_of_mem hz, hcardO]
  have hcardC : C.card ≤ 2 :=
    degree_sixteen_fourLayer_uncovered_orphan_card_le_two
      G hfree hmin hcard c₀ hregChild hcardChild z hz
  have hCsub : C ⊆ P := Finset.filter_subset _ _
  rw [Finset.card_sdiff_of_subset hCsub, hcardP]
  omega

/-- Every used exterior vertex has the residual orphan degree left after its
child owner and its one neighbor in each child-nonadjacent exterior row. -/
theorem degree_sixteen_minimumLayer_used_exterior_orphan_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    (O ∩ G.neighborFinset y).card =
      16 - (1 + (s * (s - 1) + 3 - s)) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  let O := (Finset.univ \ U) \ R
  let N := G.neighborFinset y
  have hbelow : Fintype.card V < (16 + 1) * (16 - 1) + 1 := by
    rw [hcard]
    norm_num
  have hregParent : ∀ x : V, G.degree x = 16 :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by norm_num) hmin hbelow
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  have howner : ∀ {u : minimumLayerVertex D c₀}, y ∈ E u → u = v := by
    intro u hyu
    by_contra huv
    exact (Finset.disjoint_left.mp
      (hpair (Finset.mem_univ u) (Finset.mem_univ v) huv)) hyu hyv
  have hUN : (U ∩ N).card = 1 := by
    have heq : U ∩ N = {v.2.1} := by
      ext x
      constructor
      · intro hx
        obtain ⟨u, _hu, hux⟩ := Finset.mem_image.mp
          (Finset.mem_inter.mp hx).1
        have hxy : G.Adj y x :=
          (G.mem_neighborFinset y x).mp (Finset.mem_inter.mp hx).2
        have hyu : y ∈ E u := by
          apply Finset.mem_sdiff.mpr
          refine ⟨?_, (Finset.mem_sdiff.mp hyv).2⟩
          change u.2.1 = x at hux
          exact (G.mem_neighborFinset u.2.1 y).mpr (by simpa [hux] using hxy.symm)
        have huv := howner hyu
        subst u
        change v.2.1 = x at hux
        simpa [hux]
      · intro hx
        have hxv : x = v.2.1 := Finset.mem_singleton.mp hx
        subst x
        exact Finset.mem_inter.mpr
          ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩,
            (G.mem_neighborFinset y v.2.1).mpr
              ((G.mem_neighborFinset v.2.1 y).mp
                (Finset.mem_sdiff.mp hyv).1).symm⟩
    rw [heq]
    simp
  have hpairBlocks :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u => E u ∩ N) := by
    intro u hu w hw huw
    change Disjoint (E u ∩ N) (E w ∩ N)
    rw [Finset.disjoint_left]
    intro q hqu hqw
    exact (Finset.disjoint_left.mp (hpair hu hw huw))
      (Finset.mem_inter.mp hqu).1 (Finset.mem_inter.mp hqw).1
  have hblock : ∀ u : minimumLayerVertex D c₀,
      (E u ∩ N).card = if H.Adj u v then 0 else 1 := by
    intro u
    rw [Finset.inter_comm]
    exact minimumLayer_externalBlock_card_of_owned
      G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild hcardChild u v hyv
  have hnonAdjCount :
      (Finset.univ.filter (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card =
        s * (s - 1) + 3 - s := by
    have hadjFilter :
        Finset.univ.filter (fun u : minimumLayerVertex D c₀ => H.Adj u v) =
          H.neighborFinset v := by
      ext u
      simp [H.adj_comm]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (minimumLayerVertex D c₀)))
      (fun u => H.Adj u v)
    rw [hadjFilter, H.card_neighborFinset_eq_degree, hregChild v,
      Finset.card_univ, hcardChild] at hsplit
    omega
  have hRN : (R ∩ N).card = s * (s - 1) + 3 - s := by
    have heq : R ∩ N = Finset.univ.biUnion (fun u => E u ∩ N) := by
      ext q
      simp [R]
    rw [heq, Finset.card_biUnion hpairBlocks]
    simp_rw [hblock]
    have hbool :
        (∑ u : minimumLayerVertex D c₀, if ¬H.Adj u v then 1 else 0) =
          (Finset.univ.filter
            (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card := by
      simpa only [Nat.cast_id] using
        (Finset.sum_boole (R := ℕ)
          (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v) Finset.univ)
    calc
      (∑ u : minimumLayerVertex D c₀, if H.Adj u v then 0 else 1) =
          (∑ u : minimumLayerVertex D c₀,
            if ¬H.Adj u v then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro u hu
              by_cases huv : H.Adj u v <;> simp [huv]
      _ = (Finset.univ.filter
          (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card := hbool
      _ = s * (s - 1) + 3 - s := hnonAdjCount
  have hURdisj : Disjoint U R := by
    rw [Finset.disjoint_left]
    intro q hqU hqR
    have hRsub := minimumLayer_externalBiUnion_subset_complement G D c₀ hqR
    exact (Finset.mem_sdiff.mp hRsub).2 hqU
  have hURN : ((U ∪ R) ∩ N).card =
      1 + (s * (s - 1) + 3 - s) := by
    have heq : (U ∪ R) ∩ N = (U ∩ N) ∪ (R ∩ N) := by
      ext q
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    rw [heq, Finset.card_union_of_disjoint]
    · rw [hUN, hRN]
    · exact Finset.disjoint_of_subset_left (Finset.inter_subset_left)
        (Finset.disjoint_of_subset_right (Finset.inter_subset_left) hURdisj)
  have hONeq : O ∩ N = N \ (U ∪ R) := by
    ext q
    simp [O, N]
    tauto
  rw [hONeq, Finset.card_sdiff]
  have hNcard : N.card = 16 := by
    rw [G.card_neighborFinset_eq_degree, hregParent y]
  rw [hNcard, hURN]

/-- The first adjacency image of the orphan indicator, written on the three
residual cells.  This packages the exact quotient column for `O`. -/
theorem degree_sixteen_minimumLayer_adjMatrix_mulVec_orphanIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (x : V) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let O := (Finset.univ \ U) \ R
    (G.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) x =
      if x ∈ U then 0
      else if x ∈ R then 16 - (1 + (s * (s - 1) + 3 - s))
      else 16 - (s * (s - 1) + 3) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  let O := (Finset.univ \ U) \ R
  rw [adjMatrix_mulVec_vertexFinsetIndicator]
  by_cases hxU : x ∈ U
  · rw [if_pos hxU]
    have hempty : O ∩ G.neighborFinset x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro y hy
      obtain ⟨u, _hu, hux⟩ := Finset.mem_image.mp hxU
      have hyO := (Finset.mem_inter.mp hy).1
      have hxy := (G.mem_neighborFinset x y).mp (Finset.mem_inter.mp hy).2
      have hyE : y ∈ E u := by
        apply Finset.mem_sdiff.mpr
        change u.2.1 = x at hux
        refine ⟨(G.mem_neighborFinset u.2.1 y).mpr (by simpa [hux] using hxy), ?_⟩
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hyO).1).2
      exact (Finset.mem_sdiff.mp hyO).2
        (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hyE⟩)
    change ((O ∩ G.neighborFinset x).card : ℤ) = 0
    rw [hempty]
    simp
  · rw [if_neg hxU]
    by_cases hxR : x ∈ R
    · rw [if_pos hxR]
      obtain ⟨v, _hv, hxv⟩ := Finset.mem_biUnion.mp hxR
      norm_cast
      exact degree_sixteen_minimumLayer_used_exterior_orphan_degree
        G hfree (s := s) hmin hcard c₀ hregChild hcardChild v hxv
    · rw [if_neg hxR]
      have hxO : x ∈ O := Finset.mem_sdiff.mpr
        ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxU⟩, hxR⟩
      norm_cast
      exact degree_sixteen_minimumLayer_orphan_neighbor_card
        G hfree hmin hcard c₀ hregChild hcardChild x hxO

/-- Compatibility form for the `s=4` branch: every used exterior vertex
has exactly four orphan neighbors. -/
theorem degree_sixteen_fourLayer_used_exterior_orphan_degree_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    (O ∩ G.neighborFinset y).card = 4 := by
  simpa using degree_sixteen_minimumLayer_used_exterior_orphan_degree
    G hfree (s := 4) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild) v hyv

/-- Correct row-by-row used-exterior split at `d=16`: an owned point
has one neighbor in every child-nonadjacent exterior row, including exactly
one in its own row, and none in a child-adjacent row. -/
theorem degree_sixteen_minimumLayer_used_exterior_row_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (u v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ u ∩ G.neighborFinset y).card =
      if (minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj u v
        then 0 else 1 := by
  rw [Finset.inter_comm]
  exact minimumLayer_externalBlock_card_of_owned
    G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild u v hyv

/-- Compatibility wrapper for the `s=4` residual branch. -/
theorem degree_sixteen_fourLayer_used_exterior_row_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (u v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ u ∩ G.neighborFinset y).card =
      if (minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj u v
        then 0 else 1 := by
  simpa using degree_sixteen_minimumLayer_used_exterior_row_neighbor_card
    G hfree (s := 4) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild) u v hyv

/-- Summing the row block law: an exterior point has one used-exterior
neighbor for each child vertex not adjacent to its owner. -/
theorem degree_sixteen_minimumLayer_used_exterior_neighbor_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    (Finset.univ.biUnion
        (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀) ∩ G.neighborFinset y).card =
      s * (s - 1) + 3 - s := by
  classical
  let D := secondOrderDefectGraph G
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  have hpairInter :
      (↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u => E u ∩ G.neighborFinset y) := by
    intro u hu w hw huw
    exact Finset.disjoint_of_subset_left (Finset.inter_subset_left)
      (Finset.disjoint_of_subset_right (Finset.inter_subset_left)
        (hpair hu hw huw))
  have heq : Finset.univ.biUnion E ∩ G.neighborFinset y =
      Finset.univ.biUnion (fun u => E u ∩ G.neighborFinset y) := by
    ext q
    simp
  rw [heq, Finset.card_biUnion hpairInter]
  have hrow : ∀ u : minimumLayerVertex D c₀,
      (E u ∩ G.neighborFinset y).card = if H.Adj u v then 0 else 1 := by
    intro u
    exact degree_sixteen_minimumLayer_used_exterior_row_neighbor_card
      G hfree hmin hcard c₀ hregChild hcardChild u v hyv
  simp_rw [hrow]
  have hadjFilter :
      Finset.univ.filter (fun u : minimumLayerVertex D c₀ => H.Adj u v) =
        H.neighborFinset v := by
    ext u
    simp [H.adj_comm]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (minimumLayerVertex D c₀)))
    (fun u => H.Adj u v)
  rw [hadjFilter, H.card_neighborFinset_eq_degree, hregChild v,
    Finset.card_univ, hcardChild] at hsplit
  have hnonadj :
      (Finset.univ.filter (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card =
        s * (s - 1) + 3 - s := by omega
  have hbool :
      (∑ u : minimumLayerVertex D c₀, if ¬H.Adj u v then 1 else 0) =
        (Finset.univ.filter (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card := by
    simpa only [Nat.cast_id] using
      (Finset.sum_boole (R := ℕ)
        (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v) Finset.univ)
  rw [← hnonadj, ← hbool]
  apply Finset.sum_congr rfl
  intro u _hu
  by_cases huv : H.Adj u v <;> simp [huv]

/-- The first adjacency image of the used-exterior indicator, i.e. the
`R`-column of the three-cell quotient. -/
theorem degree_sixteen_minimumLayer_adjMatrix_mulVec_usedIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (x : V) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    (G.adjMatrix ℤ).mulVec (vertexFinsetIndicator R) x =
      if x ∈ U then 16 - s
      else if x ∈ R then s * (s - 1) + 3 - s
      else s * (s - 1) + 3 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  rw [adjMatrix_mulVec_vertexFinsetIndicator]
  by_cases hxU : x ∈ U
  · rw [if_pos hxU]
    obtain ⟨u, _hu, hux⟩ := Finset.mem_image.mp hxU
    have heq : R ∩ G.neighborFinset x = E u := by
      ext y
      constructor
      · intro hy
        have hyR := (Finset.mem_inter.mp hy).1
        have hxy := (Finset.mem_inter.mp hy).2
        have hyOutside := minimumLayer_externalBiUnion_subset_complement
          G D c₀ hyR
        apply Finset.mem_sdiff.mpr
        change u.2.1 = x at hux
        exact ⟨(G.mem_neighborFinset u.2.1 y).mpr
          (by simpa [hux] using (G.mem_neighborFinset x y).mp hxy),
          (Finset.mem_sdiff.mp hyOutside).2⟩
      · intro hy
        have hy' := Finset.mem_sdiff.mp hy
        refine Finset.mem_inter.mpr ⟨?_, ?_⟩
        · exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hy⟩
        · change u.2.1 = x at hux
          exact (G.mem_neighborFinset x y).mpr
            (by simpa [hux] using (G.mem_neighborFinset u.2.1 y).mp hy'.1)
    rw [heq]
    norm_cast
    have hbelow : Fintype.card V < (16 + 1) * (16 - 1) + 1 := by
      rw [hcard]
      norm_num
    have hregParent : ∀ z : V, G.degree z = 16 :=
      regular_of_minDegree_card_lt_nextMooreLayer
        G hfree (by norm_num) hmin hbelow
    exact card_minimumLayerExternalNeighborFinset
      G D c₀ hregParent hregChild u
  · rw [if_neg hxU]
    by_cases hxR : x ∈ R
    · rw [if_pos hxR]
      obtain ⟨v, _hv, hxv⟩ := Finset.mem_biUnion.mp hxR
      norm_cast
      exact degree_sixteen_minimumLayer_used_exterior_neighbor_card
        G hfree hmin hcard c₀ hregChild hcardChild v hxv
    · rw [if_neg hxR]
      norm_cast
      exact minimumLayer_orphan_used_exterior_neighbor_card
        G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
          c₀ hregChild hcardChild x hxU hxR

/-- On the three surviving child degrees, the orphan indicator satisfies the
common quotient polynomial: `A² 1_O = |O| 1 + 13 1_O`. -/
theorem degree_sixteen_minimumLayer_adjMatrix_sq_mulVec_orphanIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let O := (Finset.univ \ U) \ R
    (G.adjMatrix ℤ * G.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) =
      fun x => (O.card : ℤ) + 13 * vertexFinsetIndicator O x := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  let r : ℤ := 16 - (1 + (s * (s - 1) + 3 - s) : ℕ)
  let a : ℤ := 16 - (s * (s - 1) + 3 : ℕ)
  have hr : r = (16 - (1 + (s * (s - 1) + 3 - s)) : ℕ) := by
    rcases hs with rfl | rfl | rfl <;> norm_num [r]
  have ha : a = (16 - (s * (s - 1) + 3) : ℕ) := by
    rcases hs with rfl | rfl | rfl <;> norm_num [a]
  have hAO : (G.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) =
      r • vertexFinsetIndicator R + a • vertexFinsetIndicator O := by
    funext x
    have hprof := degree_sixteen_minimumLayer_adjMatrix_mulVec_orphanIndicator
      G hfree hmin hcard c₀ hregChild hcardChild x
    change (G.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) x =
      (if x ∈ U then 0 else if x ∈ R then
        (16 - (1 + (s * (s - 1) + 3 - s)) : ℕ)
        else (16 - (s * (s - 1) + 3) : ℕ)) at hprof
    rw [hprof]
    by_cases hxU : x ∈ U
    · have hxR : x ∉ R := by
        intro hxR
        have hcomp := minimumLayer_externalBiUnion_subset_complement G D c₀ hxR
        exact (Finset.mem_sdiff.mp hcomp).2 hxU
      have hxO : x ∉ O := by simp [O, hxU]
      simp [vertexFinsetIndicator, hxU, hxR, hxO]
    · by_cases hxR : x ∈ R
      · have hxO : x ∉ O := by simp [O, hxR]
        simp [vertexFinsetIndicator, hxU, hxR, hxO, hr]
      · have hxO : x ∈ O := by simp [O, hxU, hxR]
        simp [vertexFinsetIndicator, hxU, hxR, hxO, ha]
  rw [← Matrix.mulVec_mulVec, hAO, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [degree_sixteen_minimumLayer_adjMatrix_mulVec_usedIndicator
      G hfree hmin hcard c₀ hregChild hcardChild x,
    degree_sixteen_minimumLayer_adjMatrix_mulVec_orphanIndicator
      G hfree hmin hcard c₀ hregChild hcardChild x]
  have hcardO := minimumLayer_unused_exterior_card
    G hfree (d := 16) (s := s) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild hcardChild
  change O.card = _ at hcardO
  rw [hcardO]
  by_cases hxU : x ∈ U
  · have hxR : x ∉ R := by
      intro hxR
      exact (Finset.mem_sdiff.mp
        (minimumLayer_externalBiUnion_subset_complement G D c₀ hxR)).2 hxU
    have hxO : x ∉ O := by simp [O, hxU]
    have hxU' : x ∈ minimumLayerImageFinset (secondOrderDefectGraph G) c₀ := hxU
    rcases hs with rfl | rfl | rfl <;>
      norm_num [r, a, vertexFinsetIndicator, hxU, hxR, hxO, hxU']
  · by_cases hxR : x ∈ R
    · have hxO : x ∉ O := by simp [O, hxR]
      have hxU' : x ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀ := hxU
      have hxR' : ∃ u : minimumLayerVertex (secondOrderDefectGraph G) c₀,
          x ∈ minimumLayerExternalNeighborFinset G
            (secondOrderDefectGraph G) c₀ u := by
        obtain ⟨u, _hu, hxu⟩ := Finset.mem_biUnion.mp hxR
        exact ⟨u, hxu⟩
      rcases hs with rfl | rfl | rfl <;>
        norm_num [r, a, vertexFinsetIndicator, hxU, hxR, hxO, hxU', hxR']
    · have hxO : x ∈ O := by simp [O, hxU, hxR]
      have hxU' : x ∉ minimumLayerImageFinset (secondOrderDefectGraph G) c₀ := hxU
      have hxR' : ¬∃ u : minimumLayerVertex (secondOrderDefectGraph G) c₀,
          x ∈ minimumLayerExternalNeighborFinset G
            (secondOrderDefectGraph G) c₀ u := by
        intro hex
        obtain ⟨u, hxu⟩ := hex
        exact hxR (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, hxu⟩)
      rcases hs with rfl | rfl | rfl <;>
        norm_num [r, a, vertexFinsetIndicator, hxU, hxR, hxO, hxU', hxR']

/-- The orphan indicator is a top (`2`) eigenvector of the second-order
defect graph in every surviving degree-sixteen residual branch. -/
theorem degree_sixteen_minimumLayer_defect_mulVec_orphanIndicator
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let O := (Finset.univ \ U) \ R
    (D.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) =
      (2 : ℤ) • vertexFinsetIndicator O := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
  have hD : D.adjMatrix ℤ =
      (15 : ℤ) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V -
          (G.adjMatrix ℤ * G.adjMatrix ℤ) := by
    ext x y
    have hxy := congrArg (fun M : Matrix V V ℤ => M x y) hsq
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply] at hxy ⊢
    norm_num at hxy ⊢
    linear_combination hxy
  have hpoly :=
    degree_sixteen_minimumLayer_adjMatrix_sq_mulVec_orphanIndicator
      G hfree hs hmin hcard c₀ hregChild hcardChild
  change (G.adjMatrix ℤ * G.adjMatrix ℤ).mulVec
      (vertexFinsetIndicator O) = _ at hpoly
  rw [hD, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, onesMatrix_mulVec_vertexFinsetIndicator, hpoly]
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Graph-facing closure consequence: both defect neighbors of every orphan
remain in the orphan cell, uniformly for `s = 0,2,4`. -/
theorem degree_sixteen_minimumLayer_orphan_defect_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    {z q : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzq : (secondOrderDefectGraph G).Adj z q) :
    q ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  have hmul := congrFun
    (degree_sixteen_minimumLayer_defect_mulVec_orphanIndicator
      G hfree hs hmin hcard c₀ hregChild hcardChild) z
  change (D.adjMatrix ℤ).mulVec (vertexFinsetIndicator O) z = _ at hmul
  rw [adjMatrix_mulVec_vertexFinsetIndicator] at hmul
  have hcardInter : (O ∩ D.neighborFinset z).card = 2 := by
    simp [vertexFinsetIndicator, hz] at hmul
    exact_mod_cast hmul
  have hcardN : (D.neighborFinset z).card = 2 := by
    rw [D.card_neighborFinset_eq_degree]
    exact secondOrderDefectGraph_degree_eq_two
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard z
  have heq : O ∩ D.neighborFinset z = D.neighborFinset z := by
    apply Finset.eq_of_subset_of_card_le (Finset.inter_subset_right)
    rw [hcardInter, hcardN]
  have hqN : q ∈ D.neighborFinset z := (D.mem_neighborFinset z q).mpr hzq
  have hqInter : q ∈ O ∩ D.neighborFinset z := by simpa [heq] using hqN
  exact (Finset.mem_inter.mp hqInter).1

/-- The minimum-layer image is closed under the defect graph simply because
it is the union of complete minimum-order connected components. -/
theorem minimumLayerImage_defect_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) {z q : V}
    (hz : z ∈ minimumLayerImageFinset D c₀) (hzq : D.Adj z q) :
    q ∈ minimumLayerImageFinset D c₀ := by
  classical
  obtain ⟨u, _hu, huz⟩ := Finset.mem_image.mp hz
  change u.2.1 = z at huz
  subst z
  have hcomp : D.connectedComponentMk q = u.1.1 :=
    (ConnectedComponent.connectedComponentMk_eq_of_adj hzq.symm).trans
      ((ConnectedComponent.mem_supp_iff u.1.1 u.2.1).mp u.2.2)
  have hqSupp : q ∈ u.1.1.supp :=
    (ConnectedComponent.mem_supp_iff u.1.1 q).mpr hcomp
  exact Finset.mem_image.mpr
    ⟨⟨u.1, ⟨q, hqSupp⟩⟩, Finset.mem_univ _, rfl⟩

/-- The used exterior is the third defect-closed cell: it is the complement
of the already closed minimum layer and orphan cells. -/
theorem degree_sixteen_minimumLayer_used_exterior_defect_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    {z q : V}
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀))
    (hzq : (secondOrderDefectGraph G).Adj z q) :
    q ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  have hzNotU : z ∉ U := by
    have hzComp := minimumLayer_externalBiUnion_subset_complement G D c₀ hz
    exact (Finset.mem_sdiff.mp hzComp).2
  have hzNotO : z ∉ O := by
    intro hzO
    exact (Finset.mem_sdiff.mp hzO).2 hz
  have hqNotU : q ∉ U := by
    intro hqU
    exact hzNotU (minimumLayerImage_defect_closed D c₀ hqU hzq.symm)
  have hqNotO : q ∉ O := by
    intro hqO
    exact hzNotO (degree_sixteen_minimumLayer_orphan_defect_closed
      G hfree hs hmin hcard c₀ hregChild hcardChild hqO hzq.symm)
  by_contra hqNotR
  exact hqNotO (Finset.mem_sdiff.mpr
    ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hqNotU⟩, hqNotR⟩)

/-- In particular, every used exterior row is internally one-regular. -/
theorem degree_sixteen_fourLayer_used_exterior_sameRow_neighbor_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (v : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyv : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ v) :
    (minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ v ∩ G.neighborFinset y).card = 1 := by
  rw [degree_sixteen_fourLayer_used_exterior_row_neighbor_card
    G hfree hmin hcard c₀ hregChild hcardChild v v hyv]
  simp

/-- A service point through a fixed orphan lies in a four-orphan block, so
after deleting the fixed orphan it supplies exactly three covered partners. -/
theorem degree_sixteen_fourLayer_service_partner_block_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z y : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (u : minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (hyu : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ u)
    (hzy : G.Adj z y) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    ((O ∩ G.neighborFinset y).erase z).card = 3 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  have hfour : (O ∩ G.neighborFinset y).card = 4 :=
    degree_sixteen_fourLayer_used_exterior_orphan_degree_eq_four
      G hfree hmin hcard c₀ hregChild hcardChild u hyu
  have hzMem : z ∈ O ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr
      ⟨hz, (G.mem_neighborFinset y z).mpr hzy.symm⟩
  rw [Finset.card_erase_of_mem hzMem, hfour]

/-- The fifteen service rows through a fixed orphan yield fifteen pairwise
disjoint three-partner blocks, hence cover exactly 45 other orphans. -/
theorem degree_sixteen_fourLayer_exists_service_partner_packing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ U) \ Finset.univ.biUnion E
    ∃ service : minimumLayerVertex D c₀ → V,
      (∀ u, service u ∈ E u ∧ G.Adj z (service u)) ∧
      ((↑(Finset.univ : Finset (minimumLayerVertex D c₀)) : Set _).PairwiseDisjoint
        (fun u =>
          (O ∩ G.neighborFinset (service u)).erase z)) ∧
      (Finset.univ.biUnion (fun u =>
        (O ∩ G.neighborFinset (service u)).erase z)).card = 45 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  have hzOutside : z ∉ U :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzUnused : z ∉ Finset.univ.biUnion E :=
    (Finset.mem_sdiff.mp hz).2
  have hex : ∀ u : minimumLayerVertex D c₀,
      ∃ y, y ∈ E u ∧ G.Adj z y := by
    intro u
    have hone := minimumLayer_orphan_service_card_eq_one
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild)
        z hzOutside hzUnused u
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hone
    have hymem : y ∈ E u ∩ G.neighborFinset z := by
      rw [hy]
      exact Finset.mem_singleton_self y
    exact ⟨y, (Finset.mem_inter.mp hymem).1,
      (G.mem_neighborFinset z y).mp (Finset.mem_inter.mp hymem).2⟩
  choose service hservice using hex
  refine ⟨service, hservice, ?_, ?_⟩
  · intro u hu v hv huv
    change Disjoint
      ((O ∩ G.neighborFinset (service u)).erase z)
      ((O ∩ G.neighborFinset (service v)).erase z)
    rw [Finset.disjoint_left]
    intro q hqu hqv
    have hqu' := Finset.mem_erase.mp hqu
    have hqv' := Finset.mem_erase.mp hqv
    have hzq : z ≠ q := Ne.symm hqu'.1
    have hrow := degree_sixteen_fourLayer_shared_service_row_unique
      G hfree hmin hcard c₀ hregChild hcardChild hzq
        (hservice u).1 (hservice u).2
        ((G.mem_neighborFinset (service u) q).mp
          (Finset.mem_inter.mp hqu'.2).2).symm
        (hservice v).1 (hservice v).2
        ((G.mem_neighborFinset (service v) q).mp
          (Finset.mem_inter.mp hqv'.2).2).symm
    exact huv hrow
  · rw [Finset.card_biUnion]
    · have hthree : ∀ u : minimumLayerVertex D c₀,
          ((O ∩ G.neighborFinset (service u)).erase z).card = 3 := by
        intro u
        exact degree_sixteen_fourLayer_service_partner_block_card_eq_three
          G hfree hmin hcard c₀ hregChild hcardChild hz u
            (hservice u).1 (hservice u).2
      rw [Finset.sum_congr rfl (fun u _ => hthree u)]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change Fintype.card
        (minimumLayerVertex (secondOrderDefectGraph G) c₀) * 3 = 45
      rw [hcardChild]
    · intro u hu v hv huv
      change Disjoint
        ((O ∩ G.neighborFinset (service u)).erase z)
        ((O ∩ G.neighborFinset (service v)).erase z)
      rw [Finset.disjoint_left]
      intro q hqu hqv
      have hqu' := Finset.mem_erase.mp hqu
      have hqv' := Finset.mem_erase.mp hqv
      have hzq : z ≠ q := Ne.symm hqu'.1
      have hrow := degree_sixteen_fourLayer_shared_service_row_unique
        G hfree hmin hcard c₀ hregChild hcardChild hzq
          (hservice u).1 (hservice u).2
          ((G.mem_neighborFinset (service u) q).mp
            (Finset.mem_inter.mp hqu'.2).2).symm
          (hservice v).1 (hservice v).2
          ((G.mem_neighborFinset (service v) q).mp
            (Finset.mem_inter.mp hqv'.2).2).symm
      exact huv hrow

/-- The abstract uncovered set has exactly two elements.  The complementary
covered set is precisely the explicit union of the fifteen disjoint
three-partner service blocks. -/
theorem degree_sixteen_fourLayer_uncovered_orphan_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    ((O.erase z).filter (fun z' =>
      ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
        ¬(G.Adj z y ∧ G.Adj z' y))).card = 2 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  let P := O.erase z
  let C := P.filter (fun z' =>
    ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
      ¬(G.Adj z y ∧ G.Adj z' y))
  obtain ⟨service, hservice, hpair, hcardK⟩ :=
    degree_sixteen_fourLayer_exists_service_partner_packing
      G hfree hmin hcard c₀ hregChild hcardChild z hz
  let K := Finset.univ.biUnion (fun u : minimumLayerVertex D c₀ =>
    (O ∩ G.neighborFinset (service u)).erase z)
  have hKP : K = P \ C := by
    ext q
    constructor
    · intro hqK
      obtain ⟨u, _hu, hqBlock⟩ := Finset.mem_biUnion.mp hqK
      have hqErase := Finset.mem_erase.mp hqBlock
      have hqO := (Finset.mem_inter.mp hqErase.2).1
      have hqAdj : G.Adj q (service u) :=
        (G.mem_neighborFinset (service u) q).mp
          (Finset.mem_inter.mp hqErase.2).2 |>.symm
      have hqP : q ∈ P := Finset.mem_erase.mpr ⟨hqErase.1, hqO⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨hqP, ?_⟩
      intro hqC
      have hpred := (Finset.mem_filter.mp hqC).2
      exact hpred u (service u) (hservice u).1
        ⟨(hservice u).2, hqAdj⟩
    · intro hqPC
      have hqP := (Finset.mem_sdiff.mp hqPC).1
      have hqNotC := (Finset.mem_sdiff.mp hqPC).2
      have hnotPred : ¬(∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
          ¬(G.Adj z y ∧ G.Adj q y)) := by
        intro hp
        exact hqNotC (Finset.mem_filter.mpr ⟨hqP, hp⟩)
      push_neg at hnotPred
      obtain ⟨u, y, hyE, hzy, hqy⟩ := hnotPred
      have hone := minimumLayer_orphan_service_card_eq_one
        G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
          c₀ hregChild (by norm_num; exact hcardChild) z
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
          (Finset.mem_sdiff.mp hz).2 u
      have hyMem : y ∈ E u ∩ G.neighborFinset z :=
        Finset.mem_inter.mpr
          ⟨hyE, (G.mem_neighborFinset z y).mpr hzy⟩
      have hsMem : service u ∈ E u ∩ G.neighborFinset z :=
        Finset.mem_inter.mpr
          ⟨(hservice u).1,
            (G.mem_neighborFinset z (service u)).mpr (hservice u).2⟩
      have hle : (E u ∩ G.neighborFinset z).card ≤ 1 := by rw [hone]
      have hys : y = service u :=
        Finset.card_le_one.mp hle y hyMem (service u) hsMem
      apply Finset.mem_biUnion.mpr
      refine ⟨u, Finset.mem_univ _, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
      · exact (Finset.ne_of_mem_erase hqP)
      · exact Finset.mem_inter.mpr
          ⟨Finset.mem_of_mem_erase hqP,
            (G.mem_neighborFinset (service u) q).mpr (by simpa [← hys] using hqy.symm)⟩
  have hcardO : O.card = 48 :=
    degree_sixteen_fourLayer_unused_exterior_card_eq_fortyEight
      G hfree hmin hcard c₀ hregChild hcardChild
  have hcardP : P.card = 47 := by
    rw [Finset.card_erase_of_mem hz, hcardO]
  have hCsub : C ⊆ P := Finset.filter_subset _ _
  have hcardPC : (P \ C).card = 45 := by
    rw [← hKP]
    exact hcardK
  rw [Finset.card_sdiff_of_subset hCsub, hcardP] at hcardPC
  have hcancel := Nat.sub_add_cancel (Finset.card_le_card hCsub)
  rw [hcardP, hcardPC] at hcancel
  change C.card = 2
  apply Nat.add_left_cancel (n := 45)
  calc
    45 + C.card = 47 := hcancel
    _ = 45 + 2 := by norm_num

/-- The orphan set is closed under the second-order defect graph: both defect
neighbors of every orphan are its two uncovered orphan partners. -/
theorem degree_sixteen_fourLayer_orphans_defect_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    ∀ z ∈ O, D.neighborFinset z ⊆ O := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  intro z hz
  let C := (O.erase z).filter (fun z' =>
    ∀ u : minimumLayerVertex D c₀, ∀ y ∈ E u,
      ¬(G.Adj z y ∧ G.Adj z' y))
  have hCcard : C.card = 2 :=
    degree_sixteen_fourLayer_uncovered_orphan_card_eq_two
      G hfree hmin hcard c₀ hregChild hcardChild z hz
  have hCsubD : C ⊆ D.neighborFinset z := by
    intro z' hz'C
    have hz'Filter := Finset.mem_filter.mp hz'C
    have hz'O : z' ∈ O := Finset.mem_of_mem_erase hz'Filter.1
    have hzz' : z ≠ z' := Ne.symm (Finset.ne_of_mem_erase hz'Filter.1)
    apply (D.mem_neighborFinset z z').mpr
    exact degree_sixteen_fourLayer_uncovered_orphans_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hz'O hzz'
        hz'Filter.2
  have hDcard : (D.neighborFinset z).card = 2 := by
    rw [D.card_neighborFinset_eq_degree,
      secondOrderDefectGraph_degree_eq_two G hfree (by norm_num)
        (by norm_num) hmin hcard z]
  have hCD : C = D.neighborFinset z :=
    Finset.eq_of_subset_of_card_le hCsubD (by rw [hCcard, hDcard])
  intro z' hz'D
  rw [← hCD] at hz'D
  exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hz'D).1

/-- Component form of uniform orphan defect closure: the entire defect
component of every orphan remains in the orphan cell. -/
theorem degree_sixteen_minimumLayer_orphan_component_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2 ∨ s = 4)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    ∀ z ∈ O, (D.connectedComponentMk z).supp ⊆ (O : Set V) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion E
  have hclosed : ∀ z ∈ O, D.neighborFinset z ⊆ O := by
    intro z hz q hzq
    exact degree_sixteen_minimumLayer_orphan_defect_closed
      G hfree hs hmin hcard c₀ hregChild hcardChild hz
        ((D.mem_neighborFinset z q).mp hzq)
  have hwalk : ∀ (a b : V) (p : D.Walk a b), a ∈ O → b ∈ O := by
    intro a b p
    induction p with
    | nil => exact fun ha => ha
    | cons hadj q ih =>
        intro ha
        have hv : _ ∈ O := hclosed _ ha
          ((D.mem_neighborFinset _ _).mpr hadj)
        exact ih hv
  intro z hz q hq
  have heq : D.connectedComponentMk q = D.connectedComponentMk z :=
    (ConnectedComponent.mem_supp_iff (D.connectedComponentMk z) q).mp hq
  have hr : D.Reachable z q := ConnectedComponent.eq.mp heq.symm
  obtain ⟨p⟩ := hr
  exact hwalk z q p hz

/-- Compatibility wrapper for the `s=4` component closure theorem. -/
theorem degree_sixteen_fourLayer_orphan_component_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion E
    ∀ z ∈ O, (D.connectedComponentMk z).supp ⊆ (O : Set V) := by
  simpa using degree_sixteen_minimumLayer_orphan_component_subset
    G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild)

/-- The two smaller residual children pin the chosen defect-component order:
the empty child has one triangle, while the two-regular five-vertex child has
one defect component of order five. -/
theorem degree_sixteen_smallLayer_component_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3) :
    (s = 0 → c₀.supp.ncard = 3) ∧ (s = 2 → c₀.supp.ncard = 5) := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨r, hr3, hre, _⟩ :=
    secondOrderDefect_component_resolvent_chebyshev
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₀ 0
  have hw3 : 3 ≤ c₀.supp.ncard := by rw [← hre]; exact hr3
  have hkpos : 0 < (Finset.univ.filter
      (fun c : D.ConnectedComponent => c.supp.ncard = c₀.supp.ncard)).card := by
    apply Finset.card_pos.mpr
    exact ⟨c₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hlayer := card_minimumLayerVertex D c₀
  rw [hcardChild] at hlayer
  constructor
  · intro hs0
    subst s
    norm_num at hlayer
    nlinarith
  · intro hs2
    subst s
    norm_num at hlayer
    have hw5 : c₀.supp.ncard ≤ 5 := by nlinarith
    interval_cases c₀.supp.ncard <;> norm_num at hlayer ⊢ <;> omega

/-- In the two-regular residual branch the unique minimum defect component
is the five-vertex child itself, so its component-quotient diagonal is the
child degree two. -/
theorem degree_sixteen_twoLayer_minimumComponent_diagonal_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c₀ c₀ = 2 := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  have hbase := (degree_sixteen_smallLayer_component_card
    G hfree (s := 2) (by norm_num) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild)).2 rfl
  let C : Finset V := c₀.supp.toFinite.toFinset
  have hCU : C ⊆ U := by
    intro z hz
    have hzc : z ∈ c₀.supp := by simpa [C] using hz
    let c : minimumLayerComponent D c₀ := ⟨c₀, rfl⟩
    let x : minimumLayerVertex D c₀ := ⟨c, ⟨z, hzc⟩⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
  have hcardC : C.card = 5 := by
    rw [show C.card = c₀.supp.ncard by
      simpa [C] using
        (Set.ncard_eq_toFinset_card c₀.supp c₀.supp.toFinite).symm,
      hbase]
  have hcardU : U.card = 5 := by
    rw [card_minimumLayerImageFinset]
    exact hcardChild
  have hCUeq : C = U :=
    Finset.eq_of_subset_of_card_le hCU (by rw [hcardU, hcardC])
  let z := componentRepresentative D c₀
  have hzc : z ∈ c₀.supp := componentRepresentative_mem D c₀
  let c : minimumLayerComponent D c₀ := ⟨c₀, rfl⟩
  let x : minimumLayerVertex D c₀ := ⟨c, ⟨z, hzc⟩⟩
  have hinter : componentNeighborFinset G D c₀ z =
      U ∩ G.neighborFinset z := by
    ext q
    simp only [componentNeighborFinset, Finset.mem_filter,
      Finset.mem_inter]
    have hqU : q ∈ U ↔ q ∈ c₀.supp := by
      rw [← hCUeq]
      simp [C]
    rw [hqU, ConnectedComponent.mem_supp_iff]
    tauto
  have hQ := componentQuotientMatrix_apply_eq G D 2
    (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard)
    (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard) c₀ c₀ hzc
  rw [hQ, hinter]
  exact minimumLayerImage_inter_neighborFinset_card G D c₀ hregChild x

/-- **Order-five mass squeeze in the two-layer branch.**  The unique
minimum component has order five, is canonically forward-oriented (all odd
cycle blocks are), and contributes diagonal mass two.  The mixed order-five
theorem makes the total selected mass divisible by five, while the global
nonsquare trace bounds it by sixteen.  Hence only `5`, `10`, or `15` remain. -/
theorem degree_sixteen_twoLayer_orientedFiveMass_eq_five_ten_or_fifteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) :
    orientedAnchorMass G u (forwardOriented G u) 5 = 5 ∨
      orientedAnchorMass G u (forwardOriented G u) 5 = 10 ∨
      orientedAnchorMass G u (forwardOriented G u) 5 = 15 := by
  classical
  let D := secondOrderDefectGraph G
  have hbase := (degree_sixteen_smallLayer_component_card
    G hfree (s := 2) (by norm_num) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild)).2 rfl
  have hcOdd : Odd c₀.supp.ncard := by rw [hbase]; norm_num
  have hcFwd : forwardOriented G u c₀ := by
    intro x y
    exact graph_equalOddCycle_diagBlock_adj_shift_iff
      (hℓ3 c₀) hcOdd G D (u c₀) (hu c₀)
        (adjMatrix_comm_secondOrderDefect_of_even
          G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard)
        (huD c₀) x y
  have hcMem : c₀ ∈ Finset.univ.filter (fun c : D.ConnectedComponent =>
      5 ∣ c.supp.ncard ∧ forwardOriented G u c) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by rw [hbase], hcFwd⟩
  have hbridge := orientedAnchorMass_eq_sum_diagonalQuotient
    G hfree (d := 16) (p := 5) (by norm_num) (by norm_num) hmin hcard
      u hu huRange (forwardOriented G u)
  have hcdiag := degree_sixteen_twoLayer_minimumComponent_diagonal_eq_two
    G hfree hmin hcard c₀ hregChild hcardChild
  have hmassLower : 2 ≤ orientedAnchorMass G u (forwardOriented G u) 5 := by
    rw [hbridge]
    rw [← hcdiag]
    exact Finset.single_le_sum
      (f := fun c : D.ConnectedComponent =>
        componentQuotientMatrix G D c c)
      (fun _ _ => Nat.zero_le _) hcMem
  have hmassUpper : orientedAnchorMass G u (forwardOriented G u) 5 ≤ 16 := by
    rw [hbridge]
    calc
      (∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent =>
          5 ∣ c.supp.ncard ∧ forwardOriented G u c),
          componentQuotientMatrix G D c c) ≤
          ∑ c : D.ConnectedComponent, componentQuotientMatrix G D c c := by
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
      _ = 16 := secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
        G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard (by norm_num)
  have hdvd := five_dvd_orientedAnchorMass_forwardOriented
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
      u hℓ3 hbij huD
  omega

/-- The order-five mass squeeze forces at least three selected
five-divisible forward components.  Since the minimum `C₅` is one of them,
at least two additional selected components occur outside the base layer. -/
theorem degree_sixteen_twoLayer_three_le_forwardFive_component_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)}) :
    3 ≤ (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent =>
        5 ∣ c.supp.ncard ∧ forwardOriented G u c)).card := by
  have hmass :=
    degree_sixteen_twoLayer_orientedFiveMass_eq_five_ten_or_fifteen
      G hfree hmin hcard c₀ hregChild hcardChild u hu huRange hℓ3 hbij huD
  have hmassLower : 5 ≤ orientedAnchorMass G u (forwardOriented G u) 5 := by
    rcases hmass with h5 | h10 | h15 <;> omega
  have hmassUpper :=
    orientedAnchorMass_forwardOriented_le_two_mul_component_card
      G hfree (d := 16) (p := 5) (by norm_num) (by norm_num) hmin hcard
        u hu huRange
  omega

/-- Sharp orphan-cycle lower bounds in the two small residual branches.
Since `c₀` is minimum and the orphan is outside the minimum layer, its full
component is strictly larger than the base length `3` or `5`. -/
theorem degree_sixteen_smallLayer_orphan_component_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    (s = 0 → 4 ≤ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) ∧
      (s = 2 → 6 ≤
        ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  have hbase := degree_sixteen_smallLayer_component_card
    G hfree hs hmin hcard c₀ hregChild hcardChild
  have hne : (D.connectedComponentMk z).supp.ncard ≠ c₀.supp.ncard := by
    intro heq
    let c : minimumLayerComponent D c₀ := ⟨D.connectedComponentMk z, heq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨c, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    have hzU : z ∈ U := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 hzU
  have hle : c₀.supp.ncard ≤ (D.connectedComponentMk z).supp.ncard :=
    hc₀min (D.connectedComponentMk z)
  constructor
  · intro hs0
    have hb : c₀.supp.ncard = 3 := hbase.1 hs0
    change 4 ≤ (D.connectedComponentMk z).supp.ncard
    omega
  · intro hs2
    have hb : c₀.supp.ncard = 5 := hbase.2 hs2
    change 6 ≤ (D.connectedComponentMk z).supp.ncard
    omega

/-- The same sharp cycle floors hold in the used-exterior cell, which is
also disjoint from the minimum layer and defect-closed. -/
theorem degree_sixteen_smallLayer_used_component_card_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    (s = 0 → 4 ≤ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) ∧
      (s = 2 → 6 ≤
        ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  have hbase := degree_sixteen_smallLayer_component_card
    G hfree hs hmin hcard c₀ hregChild hcardChild
  have hne : (D.connectedComponentMk z).supp.ncard ≠ c₀.supp.ncard := by
    intro heq
    let c : minimumLayerComponent D c₀ := ⟨D.connectedComponentMk z, heq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨c, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    have hzU : z ∈ U := Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    have hzComp := minimumLayer_externalBiUnion_subset_complement G D c₀ hz
    exact (Finset.mem_sdiff.mp hzComp).2 hzU
  have hle : c₀.supp.ncard ≤ (D.connectedComponentMk z).supp.ncard :=
    hc₀min (D.connectedComponentMk z)
  constructor
  · intro hs0
    have hb : c₀.supp.ncard = 3 := hbase.1 hs0
    change 4 ≤ (D.connectedComponentMk z).supp.ncard
    omega
  · intro hs2
    have hb : c₀.supp.ncard = 5 := hbase.2 hs2
    change 6 ≤ (D.connectedComponentMk z).supp.ncard
    omega

/-- In the two small residual branches, every used-exterior defect cycle has
order divisible by the base cycle order: by three for `s = 0`, and by five
for `s = 2`.  The minimum layer consists of the single base component in
these cases, while every used point has an original-graph neighbor in that
layer.  The boundary quotient divisibility theorem then applies across the
resulting positive component edge. -/
theorem degree_sixteen_smallLayer_used_component_card_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {s : ℕ} (hs : s = 0 ∨ s = 2)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    (s = 0 → 3 ∣ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) ∧
      (s = 2 → 5 ∣
        ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let e := D.connectedComponentMk z
  have hbase := degree_sixteen_smallLayer_component_card
    G hfree hs hmin hcard c₀ hregChild hcardChild
  have hbaseEq : c₀.supp.ncard = s * (s - 1) + 3 := by
    rcases hs with hs0 | hs2
    · subst s
      simpa using hbase.1 rfl
    · subst s
      simpa using hbase.2 rfl
  let C : Finset V := c₀.supp.toFinite.toFinset
  have hCU : C ⊆ U := by
    intro x hx
    have hxc : x ∈ c₀.supp := by simpa [C] using hx
    let c : minimumLayerComponent D c₀ := ⟨c₀, rfl⟩
    let u : minimumLayerVertex D c₀ := ⟨c, ⟨x, hxc⟩⟩
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have hcardC : C.card = c₀.supp.ncard := by
    simpa [C] using (Set.ncard_eq_toFinset_card c₀.supp c₀.supp.toFinite).symm
  have hcardU : U.card = c₀.supp.ncard := by
    rw [card_minimumLayerImageFinset, hcardChild, ← hbaseEq]
  have hCUeq : C = U := by
    apply Finset.eq_of_subset_of_card_le hCU
    rw [hcardU, hcardC]
  obtain ⟨u, _hu, hzu⟩ := Finset.mem_biUnion.mp hz
  have huz : G.Adj u.2.1 z :=
    (G.mem_neighborFinset u.2.1 z).mp (Finset.mem_sdiff.mp hzu).1
  have huU : u.2.1 ∈ U :=
    Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  have huC : u.2.1 ∈ c₀.supp := by
    have : u.2.1 ∈ C := by simpa [hCUeq] using huU
    simpa [C] using this
  have huMk : D.connectedComponentMk u.2.1 = c₀ :=
    (ConnectedComponent.mem_supp_iff c₀ u.2.1).mp huC
  have hzE : z ∈ e.supp := ConnectedComponent.connectedComponentMk_mem
  have hQpos : 0 < componentQuotientMatrix G D e c₀ := by
    rw [componentQuotientMatrix_apply_eq G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard) e c₀ hzE]
    apply Finset.card_pos.mpr
    refine ⟨u.2.1, ?_⟩
    simp [componentNeighborFinset, huz.symm, huMk]
  have hQpos' : 0 < componentQuotientMatrix G D c₀ e := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c₀ e
    by_contra hzero
    have hzero' : componentQuotientMatrix G D c₀ e = 0 := by omega
    rw [hzero', mul_zero] at hbal
    have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
    have : 0 < e.supp.ncard * componentQuotientMatrix G D e c₀ :=
      Nat.mul_pos hepos hQpos
    exact (Nat.ne_of_gt this) hbal.symm
  have hlower := degree_sixteen_smallLayer_used_component_card_lower
    G hfree hs hmin hcard c₀ hc₀min hregChild hcardChild z hz
  have hlt : c₀.supp.ncard < e.supp.ncard := by
    rcases hs with hs0 | hs2
    · subst s
      rw [hbase.1 rfl]
      exact hlower.1 rfl
    · subst s
      rw [hbase.2 rfl]
      exact hlower.2 rfl
  have hdvd :=
    (secondOrder_componentQuotientMatrix_entries_of_size_lt
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        c₀ e hlt hQpos').2.1
  constructor
  · intro hs0
    rw [hbase.1 hs0] at hdvd
    exact hdvd
  · intro hs2
    rw [hbase.2 hs2] at hdvd
    exact hdvd

/-- Uniform cut-divisibility form: in every surviving `d = 16` residual
branch, the chosen minimum defect-cycle order divides the order of every
used-exterior defect component.  A used point is adjacent to its child-row
owner, hence its component has a positive quotient edge to that owner's
minimum component.  Minimality and disjointness from the layer make this a
strict short-to-long edge, where boundary quotient divisibility applies. -/
theorem degree_sixteen_minimumLayer_used_component_base_card_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    c₀.supp.ncard ∣
      ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard := by
  classical
  let D := secondOrderDefectGraph G
  let e := D.connectedComponentMk z
  obtain ⟨u, _hu, hzu⟩ := Finset.mem_biUnion.mp hz
  let c : D.ConnectedComponent := u.1.1
  have hcSize : c.supp.ncard = c₀.supp.ncard := u.1.2
  have huz : G.Adj u.2.1 z :=
    (G.mem_neighborFinset u.2.1 z).mp (Finset.mem_sdiff.mp hzu).1
  have huc : u.2.1 ∈ c.supp := u.2.2
  have hzE : z ∈ e.supp := ConnectedComponent.connectedComponentMk_mem
  have hQpos : 0 < componentQuotientMatrix G D e c := by
    rw [componentQuotientMatrix_apply_eq G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard) e c hzE]
    apply Finset.card_pos.mpr
    refine ⟨u.2.1, ?_⟩
    have huMk : D.connectedComponentMk u.2.1 = c :=
      (ConnectedComponent.mem_supp_iff c u.2.1).mp huc
    simp [componentNeighborFinset, huz.symm, huMk]
  have hQpos' : 0 < componentQuotientMatrix G D c e := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c e
    by_contra hzero
    have hzero' : componentQuotientMatrix G D c e = 0 := by omega
    rw [hzero', mul_zero] at hbal
    have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
    have hpos : 0 < e.supp.ncard * componentQuotientMatrix G D e c :=
      Nat.mul_pos hepos hQpos
    exact (Nat.ne_of_gt hpos) hbal.symm
  have hzOutside : z ∉ minimumLayerImageFinset D c₀ :=
    (Finset.mem_sdiff.mp
      (minimumLayer_externalBiUnion_subset_complement G D c₀ hz)).2
  have hne : e.supp.ncard ≠ c₀.supp.ncard := by
    intro heq
    let ce : minimumLayerComponent D c₀ := ⟨e, heq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨ce, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    exact hzOutside (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  have hlt : c.supp.ncard < e.supp.ncard := by
    rw [hcSize]
    have hle := hc₀min e
    omega
  have hdvd :=
    (secondOrder_componentQuotientMatrix_entries_of_size_lt
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        c e hlt hQpos').2.1
  rwa [hcSize] at hdvd

/-- Exact quotient form of the used-component cut law.  Every used-exterior
defect component `e` is attached to one minimum-layer component `c`; every
vertex of `e` has exactly one neighbor in `c`, while detailed balance gives
`|c| Q(c,e) = |e|`. -/
theorem degree_sixteen_minimumLayer_used_component_quotient_entries
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let e := D.connectedComponentMk z
    ∃ c : D.ConnectedComponent,
      c.supp.ncard = c₀.supp.ncard ∧
      componentQuotientMatrix G D e c = 1 ∧
      c.supp.ncard * componentQuotientMatrix G D c e = e.supp.ncard := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let e := D.connectedComponentMk z
  obtain ⟨u, _hu, hzu⟩ := Finset.mem_biUnion.mp hz
  let c : D.ConnectedComponent := u.1.1
  have hcSize : c.supp.ncard = c₀.supp.ncard := u.1.2
  have huz : G.Adj u.2.1 z :=
    (G.mem_neighborFinset u.2.1 z).mp (Finset.mem_sdiff.mp hzu).1
  have huc : u.2.1 ∈ c.supp := u.2.2
  have hzE : z ∈ e.supp := ConnectedComponent.connectedComponentMk_mem
  have hQpos : 0 < componentQuotientMatrix G D e c := by
    rw [componentQuotientMatrix_apply_eq G D 2
      (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard)
      (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
        (by norm_num) (by norm_num) hmin hcard) e c hzE]
    apply Finset.card_pos.mpr
    refine ⟨u.2.1, ?_⟩
    have huMk : D.connectedComponentMk u.2.1 = c :=
      (ConnectedComponent.mem_supp_iff c u.2.1).mp huc
    simp [componentNeighborFinset, huz.symm, huMk]
  have hQpos' : 0 < componentQuotientMatrix G D c e := by
    have hbal := secondOrder_componentQuotientMatrix_balance
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c e
    by_contra hzero
    have hzero' : componentQuotientMatrix G D c e = 0 := by omega
    rw [hzero', mul_zero] at hbal
    have hepos : 0 < e.supp.ncard := e.nonempty_supp.ncard_pos
    have hpos : 0 < e.supp.ncard * componentQuotientMatrix G D e c :=
      Nat.mul_pos hepos hQpos
    exact (Nat.ne_of_gt hpos) hbal.symm
  have hzOutside : z ∉ minimumLayerImageFinset D c₀ :=
    (Finset.mem_sdiff.mp
      (minimumLayer_externalBiUnion_subset_complement G D c₀ hz)).2
  have hne : e.supp.ncard ≠ c₀.supp.ncard := by
    intro heq
    let ce : minimumLayerComponent D c₀ := ⟨e, heq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨ce, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    exact hzOutside (Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩)
  have hlt : c.supp.ncard < e.supp.ncard := by
    rw [hcSize]
    have hle := hc₀min e
    omega
  obtain ⟨hone, _hdvd, hratio⟩ :=
    secondOrder_componentQuotientMatrix_entries_of_size_lt
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        c e hlt hQpos'
  exact ⟨c, hcSize, hone, hratio⟩

/-- In the two-layer branch, every used component of order `5k` meets each
minimum-layer vertex in exactly `k` neighbors: the quotient entries satisfy
`Q(e,c)=1` and `5 Q(c,e)=|e|` for its (necessarily order-five) owner
component. -/
theorem degree_sixteen_twoLayer_used_component_quotient_entries
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 2)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 5)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    let D := secondOrderDefectGraph G
    let e := D.connectedComponentMk z
    componentQuotientMatrix G D e c₀ = 1 ∧
      5 * componentQuotientMatrix G D c₀ e = e.supp.ncard := by
  classical
  dsimp only
  have hbase := (degree_sixteen_smallLayer_component_card
    G hfree (s := 2) (by norm_num) hmin hcard c₀ hregChild
      (by norm_num; exact hcardChild)).2 rfl
  obtain ⟨c, hc, hone, hratio⟩ :=
    degree_sixteen_minimumLayer_used_component_quotient_entries
      G hfree hmin hcard c₀ hc₀min z hz
  have hcount : (Finset.univ.filter (fun a :
      (secondOrderDefectGraph G).ConnectedComponent =>
        a.supp.ncard = c₀.supp.ncard)).card = 1 := by
    have hlayer := card_minimumLayerVertex (secondOrderDefectGraph G) c₀
    rw [hcardChild, hbase] at hlayer
    have hcountFive : (Finset.univ.filter (fun a :
        (secondOrderDefectGraph G).ConnectedComponent =>
          a.supp.ncard = 5)).card = 1 := by
      omega
    simpa [hbase] using hcountFive
  have hcMem : c ∈ Finset.univ.filter (fun a :
      (secondOrderDefectGraph G).ConnectedComponent =>
        a.supp.ncard = c₀.supp.ncard) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc⟩
  have hc₀Mem : c₀ ∈ Finset.univ.filter (fun a :
      (secondOrderDefectGraph G).ConnectedComponent =>
        a.supp.ncard = c₀.supp.ncard) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hcc₀ : c = c₀ :=
    Finset.card_le_one.mp (by rw [hcount]) c hcMem c₀ hc₀Mem
  subst c
  refine ⟨hone, ?_⟩
  simpa [hbase] using hratio

/-- In the four-layer branch, every used-exterior defect cycle has order a
multiple of three. -/
theorem degree_sixteen_fourLayer_used_component_card_dvd_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈ Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀)) :
    3 ∣ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard := by
  have hbase : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  have hdvd := degree_sixteen_minimumLayer_used_component_base_card_dvd
    G hfree hmin hcard c₀ hc₀min z hz
  rwa [hbase] at hdvd

/-- Every orphan defect component has length at least four.  The inherited
d=4 child forces the global minimum component length to be three, and every
length-three component belongs to the minimum layer, disjoint from `O`. -/
theorem degree_sixteen_fourLayer_orphan_component_card_ge_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    4 ≤ ((secondOrderDefectGraph G).connectedComponentMk z).supp.ncard := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  have hc₀three : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  obtain ⟨r, hr3, hre, _⟩ :=
    secondOrderDefect_component_resolvent_chebyshev
      G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
        (D.connectedComponentMk z) 0
  have hthree : 3 ≤ (D.connectedComponentMk z).supp.ncard := by
    rw [← hre]
    exact hr3
  have hneThree : (D.connectedComponentMk z).supp.ncard ≠ 3 := by
    intro heq
    have hcompEq : (D.connectedComponentMk z).supp.ncard = c₀.supp.ncard := by
      rw [heq, hc₀three]
    let c : minimumLayerComponent D c₀ :=
      ⟨D.connectedComponentMk z, hcompEq⟩
    let x : minimumLayerVertex D c₀ :=
      ⟨c, ⟨z, ConnectedComponent.connectedComponentMk_mem⟩⟩
    have hzU : z ∈ U := by
      exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2 hzU
  change 4 ≤ (D.connectedComponentMk z).supp.ncard
  omega

/-- The 180 used exterior vertices are also closed under the defect graph.
The whole exterior is component-closed, and no defect edge can cross from
the already closed orphan set into its used-exterior complement. -/
theorem degree_sixteen_fourLayer_used_exterior_defect_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let E := minimumLayerExternalNeighborFinset G D c₀
    let R := Finset.univ.biUnion E
    ∀ y ∈ R, D.neighborFinset y ⊆ R := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  let O := (Finset.univ \ U) \ R
  have hRexterior : R ⊆ Finset.univ \ U :=
    minimumLayer_externalBiUnion_subset_complement G D c₀
  have hOclosed : ∀ z ∈ O, D.neighborFinset z ⊆ O :=
    degree_sixteen_fourLayer_orphans_defect_closed
      G hfree hmin hcard c₀ hregChild hcardChild
  intro y hyR q hqy
  have hyExt := hRexterior hyR
  let yExt : minimumLayerExteriorVertex D c₀ :=
    ⟨y, (Finset.mem_sdiff.mp hyExt).2⟩
  have hyqAdj : D.Adj y q := (D.mem_neighborFinset y q).mp hqy
  have hqOutside : q ∉ U :=
    minimumLayerExterior_closed_under_reachable D c₀ yExt hyqAdj.reachable
  have hqNotO : q ∉ O := by
    intro hqO
    have hyO : y ∈ O := hOclosed q hqO
      ((D.mem_neighborFinset q y).mpr hyqAdj.symm)
    exact (Finset.mem_sdiff.mp hyO).2 hyR
  have hqExt : q ∈ Finset.univ \ U :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hqOutside⟩
  by_contra hqNotR
  exact hqNotO (Finset.mem_sdiff.mpr ⟨hqExt, hqNotR⟩)

/-- Along an actual edge of `G`, second-order defect adjacency is exactly
triangle-free adjacency: the antipodal half of the defect union consists of
nonedges. -/
theorem secondOrderDefect_adj_iff_triangleFree_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {x y : V} (hxy : G.Adj x y) :
    (secondOrderDefectGraph G).Adj x y ↔
      (triangleFreeEdgeGraph G).Adj x y := by
  constructor
  · intro hD
    change (antipodalGraph G).Adj x y ∨
      (triangleFreeEdgeGraph G).Adj x y at hD
    rcases hD with hanti | htri
    · exact ((mem_antipodalNeighbors G x y).mp hanti).2.1 hxy |>.elim
    · exact htri
  · intro htri
    change (antipodalGraph G).Adj x y ∨
      (triangleFreeEdgeGraph G).Adj x y
    exact Or.inr htri

/-- Restricting a commuting graph pair to a vertex set closed under the
second graph preserves adjacency-matrix commutation.  Closure kills every
summand indexed outside the restricted set on both sides. -/
theorem comap_adjMatrix_comm_of_right_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (S : Finset V)
    (hclosed : ∀ x ∈ S, D.neighborFinset x ⊆ S)
    (hcomm : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ) :
    (G.comap (fun x : ↥S => x.1)).adjMatrix ℤ *
        (D.comap (fun x : ↥S => x.1)).adjMatrix ℤ =
      (D.comap (fun x : ↥S => x.1)).adjMatrix ℤ *
        (G.comap (fun x : ↥S => x.1)).adjMatrix ℤ := by
  classical
  ext x y
  have hxy := congrArg (fun M : Matrix V V ℤ => M x.1 y.1) hcomm
  simp only [Matrix.mul_apply] at hxy ⊢
  have hleft :
      (∑ z : V, G.adjMatrix ℤ x.1 z * D.adjMatrix ℤ z y.1) =
        ∑ z : ↥S,
          G.adjMatrix ℤ x.1 z.1 * D.adjMatrix ℤ z.1 y.1 := by
    calc
      (∑ z : V, G.adjMatrix ℤ x.1 z * D.adjMatrix ℤ z y.1) =
          ∑ z ∈ S, G.adjMatrix ℤ x.1 z * D.adjMatrix ℤ z y.1 := by
            symm
            apply Finset.sum_subset (Finset.subset_univ S)
            intro z hzUniv hzNotS
            by_cases hzy : D.Adj z y.1
            · have hzS := hclosed y.1 y.2
                ((D.mem_neighborFinset y.1 z).mpr hzy.symm)
              exact (hzNotS hzS).elim
            · simp [SimpleGraph.adjMatrix_apply, hzy]
      _ = ∑ z : ↥S,
          G.adjMatrix ℤ x.1 z.1 * D.adjMatrix ℤ z.1 y.1 := by
            rw [Finset.sum_subtype S (fun _ => Iff.rfl)]
  have hright :
      (∑ z : V, D.adjMatrix ℤ x.1 z * G.adjMatrix ℤ z y.1) =
        ∑ z : ↥S,
          D.adjMatrix ℤ x.1 z.1 * G.adjMatrix ℤ z.1 y.1 := by
    calc
      (∑ z : V, D.adjMatrix ℤ x.1 z * G.adjMatrix ℤ z y.1) =
          ∑ z ∈ S, D.adjMatrix ℤ x.1 z * G.adjMatrix ℤ z y.1 := by
            symm
            apply Finset.sum_subset (Finset.subset_univ S)
            intro z hzUniv hzNotS
            by_cases hxz : D.Adj x.1 z
            · exact (hzNotS (hclosed x.1 x.2
                ((D.mem_neighborFinset x.1 z).mpr hxz))).elim
            · simp [SimpleGraph.adjMatrix_apply, hxz]
      _ = ∑ z : ↥S,
          D.adjMatrix ℤ x.1 z.1 * G.adjMatrix ℤ z.1 y.1 := by
            rw [Finset.sum_subtype S (fun _ => Iff.rfl)]
  rw [hleft, hright] at hxy
  simpa only [SimpleGraph.adjMatrix_apply, SimpleGraph.comap_adj] using hxy

/-- A one-regular graph commuting with another graph acts on the latter by
graph automorphisms: matching partners of adjacent vertices are adjacent. -/
theorem oneRegular_matching_maps_adj_of_adjMatrix_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (M D : SimpleGraph V) [DecidableRel M.Adj] [DecidableRel D.Adj]
    (hdegree : ∀ x, M.degree x = 1)
    (hcomm : M.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * M.adjMatrix ℤ)
    {x x' y y' : V} (hxx' : M.Adj x x') (hyy' : M.Adj y y')
    (hxy : D.Adj x y) :
    D.Adj x' y' := by
  classical
  have neighbor_eq_singleton {a b : V} (hab : M.Adj a b) :
      M.neighborFinset b = {a} := by
    have haMem : a ∈ M.neighborFinset b :=
      (M.mem_neighborFinset b a).mpr hab.symm
    have hcard : (M.neighborFinset b).card = 1 := by
      rw [M.card_neighborFinset_eq_degree, hdegree b]
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard
    have haq : a = q := by simpa [hq] using haMem
    simpa [haq] using hq
  have hxN := neighbor_eq_singleton hxx'
  have hyN := neighbor_eq_singleton hyy'.symm
  have hentry := congrFun (congrFun hcomm x') y
  rw [M.adjMatrix_mul_apply, M.mul_adjMatrix_apply, hxN, hyN] at hentry
  simp only [Finset.sum_singleton] at hentry
  by_contra hnot
  simp [SimpleGraph.adjMatrix_apply, hxy, hnot] at hentry

/-- Degree in the graph pulled back to a finset subtype is the number of
ambient neighbors that remain in that finset. -/
theorem finset_comap_degree_eq_inter_neighborFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (z : ↥S) :
    (G.comap (fun x : ↥S => x.1)).degree z =
      (S ∩ G.neighborFinset z.1).card := by
  classical
  rw [← (G.comap (fun x : ↥S => x.1)).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    have hzy : G.Adj z.1 y.1 :=
      ((G.comap (fun x : ↥S => x.1)).mem_neighborFinset z y).mp hy
    exact Finset.mem_inter.mpr
      ⟨y.2, (G.mem_neighborFinset z.1 y.1).mpr hzy⟩
  · intro y hy y' hy' hyy'
    exact Subtype.ext hyy'
  · intro y hy
    let y' : ↥S := ⟨y, (Finset.mem_inter.mp hy).1⟩
    refine ⟨y', ?_, rfl⟩
    exact ((G.comap (fun x : ↥S => x.1)).mem_neighborFinset z y').mpr
      ((G.mem_neighborFinset z.1 y).mp (Finset.mem_inter.mp hy).2)

/-- On the 48 orphan vertices, the perfect-matching adjacency operator
commutes with the restricted defect two-factor. -/
theorem degree_sixteen_fourLayer_orphan_adjMatrix_comm_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    (G.comap (fun z : ↥O => z.1)).adjMatrix ℤ *
        (D.comap (fun z : ↥O => z.1)).adjMatrix ℤ =
      (D.comap (fun z : ↥O => z.1)).adjMatrix ℤ *
        (G.comap (fun z : ↥O => z.1)).adjMatrix ℤ := by
  classical
  dsimp only
  apply comap_adjMatrix_comm_of_right_closed
  · exact degree_sixteen_fourLayer_orphans_defect_closed
      G hfree hmin hcard c₀ hregChild hcardChild
  · exact adjMatrix_comm_secondOrderDefect_of_even
      G hfree (by norm_num) (by norm_num) hmin hcard

/-- The orphan matching transports every defect edge to a defect edge.
Equivalently, its fixed-point-free involution is an automorphism of the
orphan defect 2-factor, giving the component stay-or-pair dichotomy. -/
theorem degree_sixteen_fourLayer_orphan_matching_maps_defect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15) :
    let D := secondOrderDefectGraph G
    let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
      Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let M := G.comap (fun z : ↥O => z.1)
    let DO := D.comap (fun z : ↥O => z.1)
    ∀ {x x' y y' : ↥O}, M.Adj x x' → M.Adj y y' → DO.Adj x y →
      DO.Adj x' y' := by
  classical
  dsimp only
  intro x x' y y' hxx' hyy' hxy
  apply oneRegular_matching_maps_adj_of_adjMatrix_comm
    (G.comap (fun z : ↥((Finset.univ \
      minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) => z.1))
    ((secondOrderDefectGraph G).comap (fun z : ↥((Finset.univ \
      minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) => z.1))
  · intro z
    rw [finset_comap_degree_eq_inter_neighborFinset_card]
    exact degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild z.1 z.2
  · exact degree_sixteen_fourLayer_orphan_adjMatrix_comm_defect
      G hfree hmin hcard c₀ hregChild hcardChild
  · exact hxx'
  · exact hyy'
  · exact hxy

/-- The diagonal component quotient on an orphan defect cycle records
exactly whether the orphan perfect matching preserves that component.  If
the unique matching partner stays in the same defect component the diagonal
entry is one; if it is sent to a paired component the entry is zero. -/
theorem degree_sixteen_fourLayer_orphan_diagonalQuotient_eq_ite_matching_stays
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z') :
    let D := secondOrderDefectGraph G
    let c := D.connectedComponentMk z
    componentQuotientMatrix G D c c =
      if D.connectedComponentMk z' = c then 1 else 0 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  let c := D.connectedComponentMk z
  have hzc : z ∈ c.supp := ConnectedComponent.connectedComponentMk_mem
  have hQ := componentQuotientMatrix_apply_eq G D 2
    (secondOrderDefectGraph_degree_eq_two G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard)
    (adjMatrix_comm_secondOrderDefect_of_even_real G hfree (d := 16)
      (by norm_num) (by norm_num) hmin hcard) c c hzc
  rw [hQ]
  have hone : (O ∩ G.neighborFinset z).card = 1 :=
    degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild z hz
  have hz'Mem : z' ∈ O ∩ G.neighborFinset z :=
    Finset.mem_inter.mpr
      ⟨hz', (G.mem_neighborFinset z z').mpr hzz'⟩
  have hmatch : O ∩ G.neighborFinset z = {z'} := by
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
    have hz'w : z' = w := by simpa [hw] using hz'Mem
    simpa [hz'w] using hw
  by_cases hstay : D.connectedComponentMk z' = c
  · rw [if_pos hstay]
    have hcomponent : componentNeighborFinset G D c z = {z'} := by
      ext q
      constructor
      · intro hq
        have hqData := Finset.mem_filter.mp hq
        have hqSupp : q ∈ c.supp :=
          (ConnectedComponent.mem_supp_iff c q).mpr hqData.2
        have hqO := degree_sixteen_minimumLayer_orphan_component_subset
          G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
            (by norm_num; exact hcardChild) z hz hqSupp
        have hqMatch : q ∈ O ∩ G.neighborFinset z :=
          Finset.mem_inter.mpr ⟨hqO, hqData.1⟩
        simpa [hmatch] using hqMatch
      · intro hq
        have hqz' : q = z' := by simpa using hq
        subst q
        exact Finset.mem_filter.mpr
          ⟨(G.mem_neighborFinset z z').mpr hzz', hstay⟩
    rw [hcomponent]
    simp
  · rw [if_neg hstay, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    have hqSupp : q ∈ c.supp :=
      (ConnectedComponent.mem_supp_iff c q).mpr hqData.2
    have hqO := degree_sixteen_minimumLayer_orphan_component_subset
      G hfree (s := 4) (by norm_num) hmin hcard c₀ hregChild
        (by norm_num; exact hcardChild) z hz hqSupp
    have hqMatch : q ∈ O ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hqO, hqData.1⟩
    have hqz' : q = z' := by simpa [hmatch] using hqMatch
    apply hstay
    simpa [hqz'] using hqData.2

/-- **The `U/R/O` component-diagonal ledger at degree sixteen.**  Splitting
the nonsquare component-quotient trace by the three defect-closed residual
cells gives total diagonal mass exactly sixteen.  Representatives suffice
because each cell is a union of complete defect components. -/
theorem degree_sixteen_minimumLayer_component_diagonal_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent) :
    let D := secondOrderDefectGraph G
    let U := minimumLayerImageFinset D c₀
    let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
    let O := (Finset.univ \ U) \ R
    ((∑ c : D.ConnectedComponent,
        if componentRepresentative D c ∈ U then
          componentQuotientMatrix G D c c else 0) +
      (∑ c : D.ConnectedComponent,
        if componentRepresentative D c ∈ R then
          componentQuotientMatrix G D c c else 0)) +
      (∑ c : D.ConnectedComponent,
        if componentRepresentative D c ∈ O then
          componentQuotientMatrix G D c c else 0) = 16 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let R := Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  let O := (Finset.univ \ U) \ R
  have hRsub : R ⊆ Finset.univ \ U :=
    minimumLayer_externalBiUnion_subset_complement G D c₀
  let q : D.ConnectedComponent → ℕ :=
    fun c => componentQuotientMatrix G D c c
  have hsplit :
      ((∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ U then
            componentQuotientMatrix G D c c else 0) +
        (∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ R then
            componentQuotientMatrix G D c c else 0)) +
        (∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ O then
            componentQuotientMatrix G D c c else 0) =
        ∑ c : D.ConnectedComponent, componentQuotientMatrix G D c c := by
    change
      ((∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ U then q c else 0) +
        (∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ R then q c else 0)) +
        (∑ c : D.ConnectedComponent,
          if componentRepresentative D c ∈ O then q c else 0) =
        ∑ c : D.ConnectedComponent, q c
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _hc
    by_cases hxU : componentRepresentative D c ∈ U
    · have hxNotR : componentRepresentative D c ∉ R := by
        intro hxR
        exact (Finset.mem_sdiff.mp (hRsub hxR)).2 hxU
      have hxNotO : componentRepresentative D c ∉ O := by
        intro hxO
        exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxO).1).2 hxU
      simp [hxU, hxNotR, hxNotO]
    · by_cases hxR : componentRepresentative D c ∈ R
      · have hxNotO : componentRepresentative D c ∉ O :=
          fun hxO => (Finset.mem_sdiff.mp hxO).2 hxR
        simp [hxU, hxR, hxNotO]
      · have hxO : componentRepresentative D c ∈ O := Finset.mem_sdiff.mpr
          ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxU⟩, hxR⟩
        simp [hxU, hxR, hxO]
  rw [hsplit]
  exact secondOrder_componentQuotient_trace_eq_degree_of_nonsquare
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard (by norm_num)

/-- Each of the five minimum-layer defect triangles in the four-layer
branch contributes either zero or two to the component-diagonal ledger. -/
theorem degree_sixteen_fourLayer_minimumComponent_diagonal_eq_zero_or_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₀min : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ≤ e.supp.ncard)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = c₀.supp.ncard) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c c = 0 ∨
      componentQuotientMatrix G (secondOrderDefectGraph G) c c = 2 := by
  have hc₀three : c₀.supp.ncard = 3 :=
    minimumLayer_child_common_length_eq_three
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) (by norm_num) (by norm_num)
  have hcOdd : Odd c.supp.ncard := by
    rw [hc, hc₀three]
    norm_num
  have heven := oddComponent_diagonalQuotient_even
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard c hcOdd
  have hle := secondOrder_minimumLayer_diag_le_two
    G hfree (d := 16) (by norm_num) (by norm_num) hmin hcard
      c₀ hc₀min c hc
  rcases heven with ⟨k, hk⟩
  interval_cases hq : componentQuotientMatrix G
    (secondOrderDefectGraph G) c c
  · exact Or.inl rfl
  · omega
  · exact Or.inr rfl

/-- **Orphan matching color classification.**  If `z-z'` is the unique
orphan matching edge at `z`, then it is a defect edge exactly when it is
triangle-free.  Every other defect edge at `z` is antipodal. -/
theorem degree_sixteen_fourLayer_orphan_matching_color
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z') :
    ((triangleFreeEdgeGraph G).Adj z z' ↔
      (secondOrderDefectGraph G).Adj z z') ∧
    (∀ q, (secondOrderDefectGraph G).Adj z q → q ≠ z' →
      (antipodalGraph G).Adj z q) := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let O := (Finset.univ \ U) \ Finset.univ.biUnion E
  have hzO : z ∈ O := hz
  have hz'O : z' ∈ O := hz'
  refine ⟨(secondOrderDefect_adj_iff_triangleFree_of_adj G hzz').symm, ?_⟩
  intro q hzqD hqz'
  have hclosed := degree_sixteen_fourLayer_orphans_defect_closed
    G hfree hmin hcard c₀ hregChild hcardChild
  have hqO : q ∈ O := hclosed z hzO
    ((D.mem_neighborFinset z q).mpr hzqD)
  have hnG : ¬G.Adj z q := by
    intro hzqG
    have hone := degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild z hzO
    have hz'Mem : z' ∈ O ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr
        ⟨hz'O, (G.mem_neighborFinset z z').mpr hzz'⟩
    have hqMem : q ∈ O ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr
        ⟨hqO, (G.mem_neighborFinset z q).mpr hzqG⟩
    have hle : (O ∩ G.neighborFinset z).card ≤ 1 := by rw [hone]
    exact hqz' (Finset.card_le_one.mp hle q hqMem z' hz'Mem)
  change (antipodalGraph G).Adj z q ∨
    (triangleFreeEdgeGraph G).Adj z q at hzqD
  rcases hzqD with hanti | htri
  · exact hanti
  · exact (hnG ((mem_triangleFreeNeighbors G z q).mp htri).1).elim

/-- No orphan matching edge is a defect edge.  Otherwise that edge is
triangle-free while the other defect edge at the same orphan is antipodal,
contradicting exact-boundary monochromaticity of incident defect edges. -/
theorem degree_sixteen_fourLayer_orphan_matching_not_defect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z') :
    ¬(secondOrderDefectGraph G).Adj z z' := by
  classical
  let D := secondOrderDefectGraph G
  intro hzz'D
  have hz'Mem : z' ∈ D.neighborFinset z :=
    (D.mem_neighborFinset z z').mpr hzz'D
  have hcardD : (D.neighborFinset z).card = 2 := by
    rw [D.card_neighborFinset_eq_degree]
    exact secondOrderDefectGraph_degree_eq_two
      G hfree (by norm_num) (by norm_num) hmin hcard z
  have hcardErase : ((D.neighborFinset z).erase z').card = 1 := by
    rw [Finset.card_erase_of_mem hz'Mem, hcardD]
  obtain ⟨q, hqErase⟩ := Finset.card_eq_one.mp hcardErase
  have hqMemErase : q ∈ (D.neighborFinset z).erase z' := by simp [hqErase]
  have hqD : D.Adj z q :=
    (D.mem_neighborFinset z q).mp (Finset.mem_of_mem_erase hqMemErase)
  have hqne : q ≠ z' := (Finset.mem_erase.mp hqMemErase).1
  have hcolor := degree_sixteen_fourLayer_orphan_matching_color
    G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz'
  have hzqAnti : (antipodalGraph G).Adj z q := hcolor.2 q hqD hqne
  rcases secondOrderDefectGraph_incident_edges_monochromatic
      G hfree (by norm_num) (by norm_num) hmin hcard hzz'D hqD with
    hbothAnti | hbothTF
  · exact ((mem_antipodalNeighbors G z z').mp hbothAnti.1).2.1 hzz'
  · exact ((mem_antipodalNeighbors G z q).mp hzqAnti).2.1
      ((mem_triangleFreeNeighbors G z q).mp hbothTF.2).1

/-- Every orphan matching edge occupies exactly one service-block slot:
its endpoints have a common service point in a unique child row, and that
point is unique as well. -/
theorem degree_sixteen_fourLayer_orphan_matching_unique_service
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z') :
    ∃ u : minimumLayerVertex (secondOrderDefectGraph G) c₀, ∃ y : V,
      y ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ u ∧
      G.Adj z y ∧ G.Adj z' y ∧
      ∀ v : minimumLayerVertex (secondOrderDefectGraph G) c₀, ∀ y' : V,
        y' ∈ minimumLayerExternalNeighborFinset G
            (secondOrderDefectGraph G) c₀ v →
        G.Adj z y' → G.Adj z' y' → v = u ∧ y' = y := by
  classical
  have hne : z ≠ z' := G.ne_of_adj hzz'
  have hex : ∃ u : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      ∃ y ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ u,
        G.Adj z y ∧ G.Adj z' y := by
    by_contra hnot
    push_neg at hnot
    have huncovered : ∀ u : minimumLayerVertex
        (secondOrderDefectGraph G) c₀,
        ∀ y ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ u,
          ¬(G.Adj z y ∧ G.Adj z' y) := by
      intro u y hy hpair
      exact hnot u y hy hpair.1 hpair.2
    have hD := degree_sixteen_fourLayer_uncovered_orphans_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hz' hne huncovered
    exact degree_sixteen_fourLayer_orphan_matching_not_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz' hD
  obtain ⟨u, y, hyE, hzy, hz'y⟩ := hex
  refine ⟨u, y, hyE, hzy, hz'y, ?_⟩
  intro v y' hy'E hzy' hz'y'
  have huv := degree_sixteen_fourLayer_shared_service_row_unique
    G hfree hmin hcard c₀ hregChild hcardChild hne
      hyE hzy hz'y hy'E hzy' hz'y'
  have hcommon := common_le_one_of_not_containsC4 hfree z z' hne
  have hyMem : y ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y).mpr hzy,
        (G.mem_neighborFinset z' y).mpr hz'y⟩
  have hy'Mem : y' ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y').mpr hzy',
        (G.mem_neighborFinset z' y').mpr hz'y'⟩
  exact ⟨huv.symm,
    Finset.card_le_one.mp hcommon y' hy'Mem y hyMem⟩

/-- Every defect edge inside the orphan subsystem is antipodal.  Its other
possible color would make it an orphan matching edge, which the preceding
theorem excludes from the defect graph. -/
theorem degree_sixteen_fourLayer_orphan_defect_adj_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z q : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzqD : (secondOrderDefectGraph G).Adj z q) :
    (antipodalGraph G).Adj z q := by
  classical
  let D := secondOrderDefectGraph G
  let O := (Finset.univ \ minimumLayerImageFinset D c₀) \
    Finset.univ.biUnion (minimumLayerExternalNeighborFinset G D c₀)
  have hq : q ∈ O :=
    degree_sixteen_fourLayer_orphans_defect_closed
      G hfree hmin hcard c₀ hregChild hcardChild z hz
        ((D.mem_neighborFinset z q).mpr hzqD)
  change (antipodalGraph G).Adj z q ∨
    (triangleFreeEdgeGraph G).Adj z q at hzqD
  rcases hzqD with hanti | htri
  · exact hanti
  · have hzqG : G.Adj z q :=
      ((mem_triangleFreeNeighbors G z q).mp htri).1
    exact (degree_sixteen_fourLayer_orphan_matching_not_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hq hzqG
        (Or.inr htri)).elim

/-- **Exact collision/leave law.**  For distinct orphans, being an edge of
the defect 2-factor is equivalent to sharing no service point in any row.
Thus the 15 parallel classes cover every non-defect pair exactly once and
leave precisely `D[O]`. -/
theorem degree_sixteen_fourLayer_orphan_defect_adj_iff_no_shared_service
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : z ≠ z') :
    (secondOrderDefectGraph G).Adj z z' ↔
      ∀ u : minimumLayerVertex (secondOrderDefectGraph G) c₀,
        ∀ y ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ u,
          ¬(G.Adj z y ∧ G.Adj z' y) := by
  classical
  constructor
  · intro hD u y hyE hpair
    have hanti := degree_sixteen_fourLayer_orphan_defect_adj_antipodal
      G hfree hmin hcard c₀ hregChild hcardChild hz hD
    have hzero := ((mem_antipodalNeighbors G z z').mp hanti).2.2
    have hyMem : y ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z y).mpr hpair.1,
          (G.mem_neighborFinset z' y).mpr hpair.2⟩
    rw [Finset.card_eq_zero.mp hzero] at hyMem
    exact Finset.notMem_empty y hyMem
  · exact degree_sixteen_fourLayer_uncovered_orphans_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz'

/-- Complementary form of the exact leave law: every non-defect orphan
pair occurs together at one unique service point in one unique row. -/
theorem degree_sixteen_fourLayer_nondefect_orphans_unique_service
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : z ≠ z')
    (hnotD : ¬(secondOrderDefectGraph G).Adj z z') :
    ∃ u : minimumLayerVertex (secondOrderDefectGraph G) c₀, ∃ y : V,
      y ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ u ∧
      G.Adj z y ∧ G.Adj z' y ∧
      ∀ v : minimumLayerVertex (secondOrderDefectGraph G) c₀, ∀ y' : V,
        y' ∈ minimumLayerExternalNeighborFinset G
            (secondOrderDefectGraph G) c₀ v →
        G.Adj z y' → G.Adj z' y' → v = u ∧ y' = y := by
  classical
  have hcollision : ¬(∀ u : minimumLayerVertex
      (secondOrderDefectGraph G) c₀,
      ∀ y ∈ minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ u,
        ¬(G.Adj z y ∧ G.Adj z' y)) := by
    intro hnone
    exact hnotD ((degree_sixteen_fourLayer_orphan_defect_adj_iff_no_shared_service
      G hfree hmin hcard c₀ hregChild hcardChild hz hz' hzz').mpr hnone)
  push_neg at hcollision
  obtain ⟨u, y, hyE, hzy, hz'y⟩ := hcollision
  refine ⟨u, y, hyE, hzy, hz'y, ?_⟩
  intro v y' hy'E hzy' hz'y'
  have huv := degree_sixteen_fourLayer_shared_service_row_unique
    G hfree hmin hcard c₀ hregChild hcardChild hzz'
      hyE hzy hz'y hy'E hzy' hz'y'
  have hcommon := common_le_one_of_not_containsC4 hfree z z' hzz'
  have hyMem : y ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y).mpr hzy,
        (G.mem_neighborFinset z' y).mpr hz'y⟩
  have hy'Mem : y' ∈ G.neighborFinset z ∩ G.neighborFinset z' :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z y').mpr hzy',
        (G.mem_neighborFinset z' y').mpr hz'y'⟩
  exact ⟨huv.symm, Finset.card_le_one.mp hcommon y' hy'Mem y hyMem⟩

/-- Every edge incident to an orphan lies in a triangle; equivalently its
open neighborhood is a perfect matching.  This is the child-side pairing
structure left after the all-antipodal defect closure. -/
theorem degree_sixteen_fourLayer_orphan_localNeighborhood_oneRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    (z : V)
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀)) :
    (triangleFreeNeighbors G z).card = 0 ∧
      ∀ y : {q : V // q ∈ G.neighborSet z},
        (G.induce (G.neighborSet z)).degree y = 1 := by
  classical
  have hzero : (triangleFreeNeighbors G z).card = 0 := by
    rw [Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hqTF
    have hqData := (mem_triangleFreeNeighbors G z q).mp hqTF
    have hzqD : (secondOrderDefectGraph G).Adj z q := Or.inr hqTF
    have hqO := degree_sixteen_fourLayer_orphans_defect_closed
      G hfree hmin hcard c₀ hregChild hcardChild z hz
        (((secondOrderDefectGraph G).mem_neighborFinset z q).mpr hzqD)
    exact degree_sixteen_fourLayer_orphan_matching_not_defect_adj
      G hfree hmin hcard c₀ hregChild hcardChild hz hqO hqData.1 hzqD
  refine ⟨hzero, ?_⟩
  intro y
  have hle : (G.induce (G.neighborSet z)).degree y ≤ 1 := by
    rw [degree_induce_neighborSet_eq_card_common]
    exact common_le_one_of_not_containsC4 hfree z y.1 (G.ne_of_adj y.2)
  have hne : (G.induce (G.neighborSet z)).degree y ≠ 0 := by
    intro hdegzero
    have hcommonzero :
        (G.neighborFinset z ∩ G.neighborFinset y.1).card = 0 := by
      rwa [degree_induce_neighborSet_eq_card_common] at hdegzero
    have hyTF : y.1 ∈ triangleFreeNeighbors G z :=
      (mem_triangleFreeNeighbors G z y.1).mpr ⟨y.2, hcommonzero⟩
    rw [Finset.card_eq_zero] at hzero
    exact Finset.notMem_empty y.1 (hzero ▸ hyTF)
  omega

/-- A nonshared service of a matched orphan has its local-triangle partner
at a service in a distinct child-nonadjacent row.  These seven pairings are
the near-perfect matching of the child complement selected by each orphan. -/
theorem degree_sixteen_fourLayer_orphan_nonshared_service_partner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) (hmin : 16 ≤ G.minDegree)
    (hcard : Fintype.card V = 16 * (16 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 4)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) = 15)
    {z z' : V}
    (hz : z ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hz' : z' ∈
      (Finset.univ \ minimumLayerImageFinset (secondOrderDefectGraph G) c₀) \
        Finset.univ.biUnion (minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀))
    (hzz' : G.Adj z z')
    (u : minimumLayerVertex (secondOrderDefectGraph G) c₀) {y : V}
    (hyE : y ∈ minimumLayerExternalNeighborFinset G
      (secondOrderDefectGraph G) c₀ u)
    (hzy : G.Adj z y) (hnotShared : ¬G.Adj z' y) :
    ∃ v : minimumLayerVertex (secondOrderDefectGraph G) c₀, ∃ y' : V,
      y' ∈ minimumLayerExternalNeighborFinset G
          (secondOrderDefectGraph G) c₀ v ∧
      v ≠ u ∧
      ¬(minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj v u ∧
      G.Adj z y' ∧ G.Adj y y' ∧ ¬G.Adj z' y' ∧
      ∀ w : V, G.Adj z w → G.Adj y w → w = y' := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  let R := Finset.univ.biUnion E
  let O := (Finset.univ \ U) \ R
  let yy : {q : V // q ∈ G.neighborSet z} := ⟨y, hzy⟩
  have hlocal :=
    (degree_sixteen_fourLayer_orphan_localNeighborhood_oneRegular
      G hfree hmin hcard c₀ hregChild hcardChild z hz).2 yy
  have hcardLocal :
      ((G.induce (G.neighborSet z)).neighborFinset yy).card = 1 := by
    rw [(G.induce (G.neighborSet z)).card_neighborFinset_eq_degree, hlocal]
  obtain ⟨ww, hww⟩ := Finset.card_eq_one.mp hcardLocal
  have hwwMem : ww ∈ (G.induce (G.neighborSet z)).neighborFinset yy := by
    simp [hww]
  have hyw : G.Adj y ww.1 :=
    ((G.induce (G.neighborSet z)).mem_neighborFinset yy ww).mp hwwMem
  have hzw : G.Adj z ww.1 := ww.2
  have hwne : ww.1 ≠ z' := by
    intro hwz'
    apply hnotShared
    rw [← hwz']
    exact hyw.symm
  have hzOutside : z ∉ U :=
    (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hz).1).2
  have hzUnused : z ∉ R := (Finset.mem_sdiff.mp hz).2
  have hwOutside : ww.1 ∉ U := by
    intro hwU
    obtain ⟨a, _ha, haw⟩ := Finset.mem_image.mp hwU
    apply hzUnused
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨?_, hzOutside⟩⟩
    change a.2.1 = ww.1 at haw
    exact (G.mem_neighborFinset a.2.1 z).mpr (by simpa [haw] using hzw.symm)
  have hwR : ww.1 ∈ R := by
    by_contra hwNotR
    have hwO : ww.1 ∈ O := Finset.mem_sdiff.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwOutside⟩, hwNotR⟩
    have hone := degree_sixteen_fourLayer_orphan_neighbor_card_eq_one
      G hfree hmin hcard c₀ hregChild hcardChild z hz
    have hz'Mem : z' ∈ O ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr
        ⟨hz', (G.mem_neighborFinset z z').mpr hzz'⟩
    have hwMem : ww.1 ∈ O ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr
        ⟨hwO, (G.mem_neighborFinset z ww.1).mpr hzw⟩
    have hle : (O ∩ G.neighborFinset z).card ≤ 1 := by rw [hone]
    exact hwne (Finset.card_le_one.mp hle ww.1 hwMem z' hz'Mem)
  obtain ⟨v, _hv, hwE⟩ := Finset.mem_biUnion.mp hwR
  have hvu : v ≠ u := by
    intro hvu
    subst v
    have hone := minimumLayer_orphan_service_card_eq_one
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) z hzOutside hzUnused u
    have hyMem : y ∈ E u ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hyE, (G.mem_neighborFinset z y).mpr hzy⟩
    have hwMem : ww.1 ∈ E u ∩ G.neighborFinset z :=
      Finset.mem_inter.mpr ⟨hwE, (G.mem_neighborFinset z ww.1).mpr hzw⟩
    have hle : (E u ∩ G.neighborFinset z).card ≤ 1 := by rw [hone]
    have hywEq := Finset.card_le_one.mp hle y hyMem ww.1 hwMem
    exact G.loopless.irrefl y (hywEq ▸ hyw)
  have hnotH : ¬(minimumLayerGraph G D c₀).Adj v u := by
    intro hvuH
    have hblock := degree_sixteen_fourLayer_used_exterior_row_neighbor_card
      G hfree hmin hcard c₀ hregChild hcardChild v u hyE
    rw [if_pos hvuH] at hblock
    have hwMem : ww.1 ∈ E v ∩ G.neighborFinset y :=
      Finset.mem_inter.mpr ⟨hwE, (G.mem_neighborFinset y ww.1).mpr hyw⟩
    rw [Finset.card_eq_zero.mp hblock] at hwMem
    exact Finset.notMem_empty ww.1 hwMem
  have hnotShared' : ¬G.Adj z' ww.1 := by
    intro hz'w
    have hzy'ne : z ≠ ww.1 := G.ne_of_adj hzw
    have hcommon := common_le_one_of_not_containsC4 hfree z ww.1 hzy'ne
    have hyMem : y ∈ G.neighborFinset z ∩ G.neighborFinset ww.1 :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z y).mpr hzy,
          (G.mem_neighborFinset ww.1 y).mpr hyw.symm⟩
    have hz'Mem : z' ∈ G.neighborFinset z ∩ G.neighborFinset ww.1 :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z z').mpr hzz',
          (G.mem_neighborFinset ww.1 z').mpr hz'w.symm⟩
    have hyz' : y = z' :=
      Finset.card_le_one.mp hcommon y hyMem z' hz'Mem
    have hyR : y ∈ R := Finset.mem_biUnion.mpr
      ⟨u, Finset.mem_univ _, hyE⟩
    exact (Finset.mem_sdiff.mp hz').2 (hyz' ▸ hyR)
  refine ⟨v, ww.1, hwE, hvu, hnotH, hzw, hyw, hnotShared', ?_⟩
  intro w hzw' hyw'
  have hzyne : z ≠ y := G.ne_of_adj hzy
  have hcommon := common_le_one_of_not_containsC4 hfree z y hzyne
  have hwMem : w ∈ G.neighborFinset z ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z w).mpr hzw',
        (G.mem_neighborFinset y w).mpr hyw'⟩
  have hpartnerMem : ww.1 ∈ G.neighborFinset z ∩ G.neighborFinset y :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z ww.1).mpr hzw,
        (G.mem_neighborFinset y ww.1).mpr hyw⟩
  exact Finset.card_le_one.mp hcommon w hwMem ww.1 hpartnerMem

end

end Erdos85
