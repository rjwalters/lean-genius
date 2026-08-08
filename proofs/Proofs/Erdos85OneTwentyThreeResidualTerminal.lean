import Proofs.Erdos85AbstractTraceEscape
import Proofs.Erdos85OneTwentyThreeTraceEscape
import Proofs.Erdos85SymmetricRestrictionSemisimple
import Proofs.Erdos85OneTwentyThreeArithmetic
import Proofs.Erdos85ExteriorCharpolyDivisibility
import Proofs.Erdos85OneTwentyThreeSemisimplePackage
import Proofs.Erdos85OwnerFiberProjectedSquare

/-!
# Scalar-123 residual terminal

The operator theorem below is the final contradiction engine.  The graph
wrapper transports the saturated owner-fiber hard sector into this engine.
-/

open Polynomial
open SimpleGraph

namespace Erdos85

noncomputable section

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

end

end Erdos85
