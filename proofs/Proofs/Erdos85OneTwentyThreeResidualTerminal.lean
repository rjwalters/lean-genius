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

/-- Every used exterior vertex has exactly four orphan neighbors.  Its other
twelve neighbors are forced: its child owner, plus one vertex in each of the
eleven exterior rows whose child vertex is not adjacent to the owner. -/
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
    G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
      c₀ hregChild (by norm_num; exact hcardChild)
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
      G hfree (d := 16) (s := 4) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild (by norm_num; exact hcardChild) u v hyv
  have hnonAdjCount :
      (Finset.univ.filter (fun u : minimumLayerVertex D c₀ => ¬H.Adj u v)).card = 11 := by
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
  have hRN : (R ∩ N).card = 11 := by
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
      _ = 11 := hnonAdjCount
  have hURdisj : Disjoint U R := by
    rw [Finset.disjoint_left]
    intro q hqU hqR
    have hRsub := minimumLayer_externalBiUnion_subset_complement G D c₀ hqR
    exact (Finset.mem_sdiff.mp hRsub).2 hqU
  have hURN : ((U ∪ R) ∩ N).card = 12 := by
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

end

end Erdos85
