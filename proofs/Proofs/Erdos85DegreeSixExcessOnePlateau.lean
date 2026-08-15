import Proofs.Erdos85DegreeSixBoundaryPackage
import Proofs.Erdos85EvenExcessOneDefectKernel
import Proofs.Erdos85BoundedReplacementObstruction
import Proofs.Erdos85EvenExcessOneThirdMoment
import Proofs.Erdos85AlternatingFourthMoment
import Proofs.Erdos85SecondOrderColorTrace
import Proofs.Erdos85ExcessEigenspace
import Proofs.Erdos85QuadraticDimension

/-!
# The degree-six excess-one plateau kernel

The order-34 residue of the degree-six plateau band feeds directly into the
mod-two defect-kernel theorem.  This file exports that consequence without
requiring later assembly code to unpack `PositiveExcessPlateauData`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Edge partition at even excess one.  Triangular edges occur in disjoint
triangles, while the triangle-free color has degree zero or two, so twice
the colored-sector order plus six times the triangular clique count is the
total degree mass. -/
theorem six_mul_triangularCliqueCount_add_two_mul_colorOrder_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    6 * ((triangularEdgeGraph G).cliqueFinset 3).card +
        2 * ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 2).card) =
      Fintype.card V * d := by
  let H := triangularEdgeGraph G
  let T := triangleFreeEdgeGraph G
  let s := (Finset.univ.filter fun x : V => T.degree x = 2).card
  have hsumG : ∑ x : V, G.degree x = Fintype.card V * d := by
    simp_rw [hreg]
    simp
  have hedgeG : 2 * G.edgeFinset.card = Fintype.card V * d := by
    rw [← SimpleGraph.sum_degrees_eq_twice_card_edges G]
    exact hsumG
  have hsumT : ∑ x : V, T.degree x = 2 * s := by
    change ∑ x : V, (triangleFreeEdgeGraph G).degree x = 2 * s
    calc
      _ = ∑ x : V, if (triangleFreeEdgeGraph G).degree x = 2
          then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rcases excessOne_even_triangleFree_degree_zero_or_two
            G hfree heven hreg hcard x with hx | hx <;> simp [hx]
      _ = 2 * s := by
        simp only [s, T]
        rw [← Finset.sum_filter]
        simp [mul_comm]
  have hedgeT : T.edgeFinset.card = s := by
    have hhand := SimpleGraph.sum_degrees_eq_twice_card_edges T
    omega
  have hTle : T ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have hedgeH : H.edgeFinset.card = G.edgeFinset.card - T.edgeFinset.card := by
    have heq : H.edgeFinset = G.edgeFinset \ T.edgeFinset := by
      ext e
      simp [H, T, triangularEdgeGraph]
    rw [heq, Finset.card_sdiff_of_subset]
    exact edgeFinset_mono hTle
  have hpartition : G.edgeFinset.card = H.edgeFinset.card + T.edgeFinset.card := by
    have hlecard : T.edgeFinset.card ≤ G.edgeFinset.card :=
      Finset.card_le_card (edgeFinset_mono hTle)
    omega
  have hlocal : H.LocallyLinear :=
    triangularEdgeGraph_locallyLinear_of_not_containsC4 G hfree
  have htri : H.edgeFinset.card = 3 * (H.cliqueFinset 3).card :=
    hlocal.card_edgeFinset
  change 6 * (H.cliqueFinset 3).card + 2 * s = Fintype.card V * d
  omega

/-- At order 34 and degree six, the degree-two triangle-free color sector
has order divisible by three. -/
theorem degreeSix_thirtyFour_colorOrder_mod_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 34) :
    ((Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card) % 3 = 0 := by
  have hmass := six_mul_triangularCliqueCount_add_two_mul_colorOrder_excessOne
    G hfree (d := 6) (by norm_num) hreg (by omega)
  omega

/-- If the order-34 triangle-free degree-two sector is empty, then the
triangle-free color has degree zero at every vertex. -/
theorem degreeSix_thirtyFour_triangleFree_degree_zero_of_colorOrder_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 34)
    (hzero : (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card = 0) :
    ∀ x : V, (triangleFreeEdgeGraph G).degree x = 0 := by
  have hempty : (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2) = ∅ :=
    Finset.card_eq_zero.mp hzero
  intro x
  rcases excessOne_even_triangleFree_degree_zero_or_two
      G hfree (d := 6) (by norm_num) hreg (by omega) x with hx | hx
  · exact hx
  · have hxmem : x ∈ Finset.univ.filter (fun y : V =>
        (triangleFreeEdgeGraph G).degree y = 2) := by simp [hx]
    rw [hempty] at hxmem
    exact (Finset.notMem_empty x hxmem).elim

/-- In the pure antipodal branch at order 34, the second-order defect graph
is exactly the antipodal graph: the triangle-free summand has no edges. -/
theorem degreeSix_thirtyFour_secondOrderDefectGraph_eq_antipodalGraph_of_colorOrder_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 34)
    (hzero : (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card = 0) :
    secondOrderDefectGraph G = antipodalGraph G := by
  have hTzero :=
    degreeSix_thirtyFour_triangleFree_degree_zero_of_colorOrder_zero
      G hfree hreg hcard hzero
  apply SimpleGraph.ext
  funext x y
  have hnotT : ¬ (triangleFreeEdgeGraph G).Adj x y := by
    intro hxy
    have hy : y ∈ (triangleFreeEdgeGraph G).neighborFinset x :=
      ((triangleFreeEdgeGraph G).mem_neighborFinset x y).mpr hxy
    have hempty : (triangleFreeEdgeGraph G).neighborFinset x = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, hTzero x]
    rw [hempty] at hy
    exact Finset.notMem_empty y hy
  apply propext
  constructor
  · intro hxy
    change (antipodalGraph G).Adj x y ∨
      (triangleFreeEdgeGraph G).Adj x y at hxy
    exact hxy.resolve_right hnotT
  · intro hxy
    change (antipodalGraph G).Adj x y ∨
      (triangleFreeEdgeGraph G).Adj x y
    exact Or.inl hxy

/-- In the zero-color-order branch every original edge is triangular, so
the triangular-edge graph is the whole original graph. -/
theorem degreeSix_thirtyFour_triangularEdgeGraph_eq_of_colorOrder_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 34)
    (hzero : (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card = 0) :
    triangularEdgeGraph G = G := by
  have hTzero :=
    degreeSix_thirtyFour_triangleFree_degree_zero_of_colorOrder_zero
      G hfree hreg hcard hzero
  apply SimpleGraph.ext
  funext x y
  apply propext
  constructor
  · exact fun hxy => (triangularEdgeGraph_adj G x y).mp hxy |>.1
  · intro hxy
    apply (triangularEdgeGraph_adj G x y).mpr
    refine ⟨hxy, ?_⟩
    intro hcommon
    have hT : (triangleFreeEdgeGraph G).Adj x y :=
      (triangleFreeEdgeGraph_adj G x y).mpr
        ((mem_triangleFreeNeighbors G x y).mpr ⟨hxy, hcommon⟩)
    have hy : y ∈ (triangleFreeEdgeGraph G).neighborFinset x :=
      ((triangleFreeEdgeGraph G).mem_neighborFinset x y).mpr hT
    have hempty : (triangleFreeEdgeGraph G).neighborFinset x = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, hTzero x]
    rw [hempty] at hy
    exact Finset.notMem_empty y hy

/-- The pure antipodal branch has exactly 34 triangular 3-cliques. -/
theorem degreeSix_thirtyFour_triangularCliqueCount_eq_thirtyFour_of_colorOrder_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 34)
    (hzero : (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card = 0) :
    ((triangularEdgeGraph G).cliqueFinset 3).card = 34 := by
  have hmass := six_mul_triangularCliqueCount_add_two_mul_colorOrder_excessOne
    G hfree (d := 6) (by norm_num) hreg (by omega)
  omega

/-- The `-1` defect eigenspace at order 34 has even rational dimension.
On this eigenspace the commuting adjacency restriction squares to `6`, a
rational nonsquare.  This is the spectral parity constraint seen by an
adjacent-defect-twin vector. -/
theorem degreeSix_thirtyFour_negOne_defectEigenspace_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hregD : ∀ x, (secondOrderDefectGraph G).degree x = 3) :
    Even (Module.finrank ℚ
      (defectEigenspace
        ((secondOrderDefectGraph G).adjMatrix ℚ) (-1 : ℚ))) := by
  let A := G.adjMatrix ℚ
  let D := (secondOrderDefectGraph G).adjMatrix ℚ
  let hcomm : A * D = D * A :=
    adjMatrix_comm_secondOrderDefect_of_regular_rat G hfree hreg
  have hsq :
      defectEigenspaceRestrict A hcomm (-1 : ℚ) *
          defectEigenspaceRestrict A hcomm (-1 : ℚ) =
        (6 : ℚ) • LinearMap.id := by
    simpa [A, D] using
      (graph_defectEigenspaceRestrict_sq_of_regular_excess
        G hfree (d := 6) (e := 1) hreg hregD
          (μ := (-1 : ℚ)) (by norm_num))
  exact LinearMap.even_finrank_of_sq_eq_nonsquare_nat
    (defectEigenspaceRestrict A hcomm (-1 : ℚ)) 6
      (by
        rintro ⟨x, hx⟩
        have hle : x ≤ 6 := Nat.le_of_dvd (by norm_num) ⟨x, hx⟩
        interval_cases x <;> omega) hsq

/-- Decode the mod-two defect-set equation when the set has even order. -/
theorem oddDefectSet_neighborParity_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    (∀ v ∈ W, Odd (D.neighborFinset v ∩ W).card) ∧
      (∀ v ∉ W, Even (D.neighborFinset v ∩ W).card) := by
  have hWcast : (W.card : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hW
  constructor
  · intro v hv
    have h := hparity v
    rw [if_pos hv, hWcast] at h
    have hone : (((D.neighborFinset v ∩ W).card : ZMod 2)) = 1 := by
      have htwo : (2 : ZMod 2) = 0 := by decide
      linear_combination h - htwo
    exact ZMod.natCast_eq_one_iff_odd.mp hone
  · intro v hv
    have h := hparity v
    rw [if_neg hv, hWcast] at h
    exact ZMod.natCast_eq_zero_iff_even.mp (by simpa using h)

/-- Decode the mod-two defect-set equation when the set has odd order. -/
theorem oddDefectSet_neighborParity_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    (∀ v ∈ W, Even (D.neighborFinset v ∩ W).card) ∧
      (∀ v ∉ W, Odd (D.neighborFinset v ∩ W).card) := by
  have hWcast : (W.card : ZMod 2) = 1 :=
    ZMod.natCast_eq_one_iff_odd.mpr hW
  constructor
  · intro v hv
    have h := hparity v
    rw [if_pos hv, hWcast] at h
    apply ZMod.natCast_eq_zero_iff_even.mp
    have htwo : (2 : ZMod 2) = 0 := by decide
    linear_combination h - htwo
  · intro v hv
    have h := hparity v
    rw [if_neg hv, hWcast] at h
    have hone : (((D.neighborFinset v ∩ W).card : ZMod 2)) = 1 := by
      have htwo : (2 : ZMod 2) = 0 := by decide
      linear_combination h - htwo
    exact ZMod.natCast_eq_one_iff_odd.mp hone

/-- If an odd defect set has odd cardinality, every vertex outside it has a
defect neighbor inside it. -/
theorem oddDefectSet_dominates_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v ∉ W, ∃ w ∈ W, D.Adj v w := by
  have hout := (oddDefectSet_neighborParity_of_odd D W hW hparity).2
  intro v hv
  have hpos : 0 < (D.neighborFinset v ∩ W).card :=
    (hout v hv).pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  exact ⟨w, (Finset.mem_inter.mp hw).2,
    (D.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1⟩

/-- If an odd defect set has even cardinality, every vertex inside it has a
defect neighbor inside it. -/
theorem oddDefectSet_no_isolated_inside_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v ∈ W, ∃ w ∈ W, D.Adj v w := by
  have hin := (oddDefectSet_neighborParity_of_even D W hW hparity).1
  intro v hv
  have hpos : 0 < (D.neighborFinset v ∩ W).card :=
    (hin v hv).pos
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
  exact ⟨w, (Finset.mem_inter.mp hw).2,
    (D.mem_neighborFinset v w).mp (Finset.mem_inter.mp hw).1⟩

/-- In a cubic graph on 34 vertices, an odd-cardinality defect set satisfying
the kernel law has at least nine vertices.  Every outside vertex contributes
at least one cut incidence, while the set supplies at most three per vertex. -/
theorem oddDefectSet_nine_le_card_of_odd_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    9 ≤ W.card := by
  have hdom := oddDefectSet_dominates_of_odd D W hW hparity
  have hpoint : ∀ v : {v : V // v ∉ W},
      1 ≤ (D.neighborFinset v.1 ∩ W).card := by
    intro v
    obtain ⟨w, hwW, hvw⟩ := hdom v.1 v.2
    exact Finset.one_le_card.mpr ⟨w, Finset.mem_inter.mpr
      ⟨(D.mem_neighborFinset v.1 w).mpr hvw, hwW⟩⟩
  have hlower : Fintype.card {v : V // v ∉ W} ≤
      ∑ v : {v : V // v ∉ W}, (D.neighborFinset v.1 ∩ W).card := by
    have hsum := Finset.sum_le_sum (s :=
      (Finset.univ : Finset {v : V // v ∉ W})) fun v _hv => hpoint v
    simpa using hsum
  have hupper := sum_card_neighbor_inter_deleted_le_sum_degrees D W
  have hrhs : (∑ x ∈ W, D.degree x) = W.card * 3 := by
    simp [hreg]
  have hcut : Fintype.card {v : V // v ∉ W} ≤ W.card * 3 := by
    rw [← hrhs]
    exact hlower.trans hupper
  have hinside : Fintype.card {v : V // v ∈ W} = W.card := by
    simpa using Fintype.card_coe W
  have houtside : Fintype.card {v : V // v ∉ W} = 34 - W.card := by
    rw [Fintype.card_subtype_compl (fun v : V => v ∈ W), hcard, hinside]
  have hWle : W.card ≤ 34 := by
    rw [← hcard]
    exact Finset.card_le_univ W
  rw [houtside] at hcut
  omega

/-- In the odd-cardinality branch of a cubic defect graph, every vertex of
the defect set also has a neighbor outside it. -/
theorem oddDefectSet_complement_dominates_inside_of_odd_of_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hreg : ∀ v, D.degree v = 3) (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v ∈ W, ∃ w ∉ W, D.Adj v w := by
  have hin := (oddDefectSet_neighborParity_of_odd D W hW hparity).1
  intro v hv
  by_contra hnone
  push Not at hnone
  have hsubset : D.neighborFinset v ⊆ W := by
    intro w hw
    by_contra hwW
    exact hnone w hwW ((D.mem_neighborFinset v w).mp hw)
  have hinter : D.neighborFinset v ∩ W = D.neighborFinset v :=
    Finset.inter_eq_left.mpr hsubset
  have hthree : (D.neighborFinset v ∩ W).card = 3 := by
    rw [hinter, D.card_neighborFinset_eq_degree, hreg v]
  have heven := hin v hv
  rw [hthree] at heven
  norm_num at heven

/-- The symmetric cubic cut count bounds an odd-cardinality defect set on 34
vertices from above by 25. -/
theorem oddDefectSet_card_le_twentyFive_of_odd_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    W.card ≤ 25 := by
  let S : Finset V := Wᶜ
  have hdom := oddDefectSet_complement_dominates_inside_of_odd_of_cubic
    D W hreg hW hparity
  have hpoint : ∀ v : {v : V // v ∉ S},
      1 ≤ (D.neighborFinset v.1 ∩ S).card := by
    intro v
    have hvW : v.1 ∈ W := by simpa [S] using v.2
    obtain ⟨w, hwW, hvw⟩ := hdom v.1 hvW
    have hwS : w ∈ S := by simpa [S] using hwW
    exact Finset.one_le_card.mpr ⟨w, Finset.mem_inter.mpr
      ⟨(D.mem_neighborFinset v.1 w).mpr hvw, hwS⟩⟩
  have hlower : Fintype.card {v : V // v ∉ S} ≤
      ∑ v : {v : V // v ∉ S}, (D.neighborFinset v.1 ∩ S).card := by
    have hsum := Finset.sum_le_sum (s :=
      (Finset.univ : Finset {v : V // v ∉ S})) fun v _hv => hpoint v
    simpa using hsum
  have hupper := sum_card_neighbor_inter_deleted_le_sum_degrees D S
  have hrhs : (∑ x ∈ S, D.degree x) = S.card * 3 := by
    simp [hreg]
  have hcut : Fintype.card {v : V // v ∉ S} ≤ S.card * 3 := by
    rw [← hrhs]
    exact hlower.trans hupper
  have houtside : Fintype.card {v : V // v ∉ S} = W.card := by
    simp [S]
  have hScard : S.card = 34 - W.card := by
    simp [S, Finset.card_compl, hcard]
  have hWle : W.card ≤ 34 := by
    rw [← hcard]
    exact Finset.card_le_univ W
  rw [houtside, hScard] at hcut
  omega

/-- Combined size window for the odd-cardinality branch of the order-34
cubic defect kernel. -/
theorem oddDefectSet_card_mem_nine_twentyFive_of_odd_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    9 ≤ W.card ∧ W.card ≤ 25 :=
  ⟨oddDefectSet_nine_le_card_of_odd_of_cubic_thirtyFour
      D W hcard hreg hW hparity,
    oddDefectSet_card_le_twentyFive_of_odd_of_cubic_thirtyFour
      D W hcard hreg hW hparity⟩

/-- On 34 vertices with cubic defect degree, the complement of an
odd-cardinality defect-kernel set satisfies the same kernel law. -/
theorem oddDefectSet_compl_parity_of_odd_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v : V,
      (if v ∈ Wᶜ then (1 : ZMod 2) else 0) + (Wᶜ.card : ZMod 2) +
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 0 := by
  have hWle : W.card ≤ 34 := by
    rw [← hcard]
    exact Finset.card_le_univ W
  have hScard : Wᶜ.card = 34 - W.card := by
    simp [Finset.card_compl, hcard]
  have hSodd : Odd Wᶜ.card := by
    rcases hW with ⟨k, hk⟩
    rw [hScard]
    refine ⟨16 - k, ?_⟩
    omega
  have hScast : (Wᶜ.card : ZMod 2) = 1 :=
    ZMod.natCast_eq_one_iff_odd.mpr hSodd
  have hdecoded := oddDefectSet_neighborParity_of_odd D W hW hparity
  intro v
  have hinter : D.neighborFinset v ∩ Wᶜ = D.neighborFinset v \ W := by
    ext x
    simp
  have hsplit : (D.neighborFinset v ∩ W).card +
      (D.neighborFinset v ∩ Wᶜ).card = 3 := by
    rw [hinter]
    simpa [D.card_neighborFinset_eq_degree, hreg v] using
      Finset.card_inter_add_card_sdiff (D.neighborFinset v) W
  by_cases hv : v ∈ W
  · have hvS : v ∉ Wᶜ := by simpa using hv
    have hleftEven := hdecoded.1 v hv
    have hrightOdd : Odd (D.neighborFinset v ∩ Wᶜ).card := by
      rcases hleftEven with ⟨k, hk⟩
      refine ⟨1 - k, ?_⟩
      omega
    have hrightCast :
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 1 :=
      ZMod.natCast_eq_one_iff_odd.mpr hrightOdd
    rw [if_neg hvS, hScast, hrightCast]
    decide
  · have hvS : v ∈ Wᶜ := by simpa using hv
    have hleftOdd := hdecoded.2 v hv
    have hrightEven : Even (D.neighborFinset v ∩ Wᶜ).card := by
      rcases hleftOdd with ⟨k, hk⟩
      refine ⟨1 - k, ?_⟩
      omega
    have hrightCast :
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr hrightEven
    rw [if_pos hvS, hScast, hrightCast]
    decide

/-- On 34 vertices with cubic defect degree, the complement of an
even-cardinality defect-kernel set also satisfies the kernel law. -/
theorem oddDefectSet_compl_parity_of_even_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∀ v : V,
      (if v ∈ Wᶜ then (1 : ZMod 2) else 0) + (Wᶜ.card : ZMod 2) +
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 0 := by
  have hWle : W.card ≤ 34 := by
    rw [← hcard]
    exact Finset.card_le_univ W
  have hScard : Wᶜ.card = 34 - W.card := by
    simp [Finset.card_compl, hcard]
  have hSeven : Even Wᶜ.card := by
    rcases hW with ⟨k, hk⟩
    rw [hScard]
    refine ⟨17 - k, ?_⟩
    omega
  have hScast : (Wᶜ.card : ZMod 2) = 0 :=
    ZMod.natCast_eq_zero_iff_even.mpr hSeven
  have hdecoded := oddDefectSet_neighborParity_of_even D W hW hparity
  intro v
  have hinter : D.neighborFinset v ∩ Wᶜ = D.neighborFinset v \ W := by
    ext x
    simp
  have hsplit : (D.neighborFinset v ∩ W).card +
      (D.neighborFinset v ∩ Wᶜ).card = 3 := by
    rw [hinter]
    simpa [D.card_neighborFinset_eq_degree, hreg v] using
      Finset.card_inter_add_card_sdiff (D.neighborFinset v) W
  by_cases hv : v ∈ W
  · have hvS : v ∉ Wᶜ := by simpa using hv
    have hleftOdd := hdecoded.1 v hv
    have hrightEven : Even (D.neighborFinset v ∩ Wᶜ).card := by
      rcases hleftOdd with ⟨k, hk⟩
      refine ⟨1 - k, ?_⟩
      omega
    have hrightCast :
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 0 :=
      ZMod.natCast_eq_zero_iff_even.mpr hrightEven
    rw [if_neg hvS, hScast, hrightCast]
    norm_num
  · have hvS : v ∈ Wᶜ := by simpa using hv
    have hleftEven := hdecoded.2 v hv
    have hrightOdd : Odd (D.neighborFinset v ∩ Wᶜ).card := by
      rcases hleftEven with ⟨k, hk⟩
      refine ⟨1 - k, ?_⟩
      omega
    have hrightCast :
        (((D.neighborFinset v ∩ Wᶜ).card : ZMod 2)) = 1 :=
      ZMod.natCast_eq_one_iff_odd.mpr hrightOdd
    rw [if_pos hvS, hScast, hrightCast]
    decide

/-- Normalize an odd-cardinality kernel set by complementing if necessary.
The resulting representative has one of the five possible odd sizes
`9, 11, 13, 15, 17`. -/
theorem exists_normalized_oddDefectSet_of_odd_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ S : Finset V, Odd S.card ∧ 9 ≤ S.card ∧ S.card ≤ 17 ∧
      ∀ v : V,
        (if v ∈ S then (1 : ZMod 2) else 0) + (S.card : ZMod 2) +
          (((D.neighborFinset v ∩ S).card : ZMod 2)) = 0 := by
  have hwindow :=
    oddDefectSet_card_mem_nine_twentyFive_of_odd_of_cubic_thirtyFour
      D W hcard hreg hW hparity
  by_cases hsmall : W.card ≤ 17
  · exact ⟨W, hW, hwindow.1, hsmall, hparity⟩
  · have hWle : W.card ≤ 34 := by
      rw [← hcard]
      exact Finset.card_le_univ W
    have hScard : Wᶜ.card = 34 - W.card := by
      simp [Finset.card_compl, hcard]
    have hSodd : Odd Wᶜ.card := by
      rcases hW with ⟨k, hk⟩
      rw [hScard]
      refine ⟨16 - k, ?_⟩
      omega
    refine ⟨Wᶜ, hSodd, ?_, ?_,
      oddDefectSet_compl_parity_of_odd_of_cubic_thirtyFour
        D W hcard hreg hW hparity⟩
    · rw [hScard]
      omega
    · rw [hScard]
      omega

/-- Finite size dispatcher for normalized odd defect-kernel sets. -/
theorem exists_oddDefectSet_card_nine_or_eleven_or_thirteen_or_fifteen_or_seventeen
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hW : Odd W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ S : Finset V,
      (S.card = 9 ∨ S.card = 11 ∨ S.card = 13 ∨
        S.card = 15 ∨ S.card = 17) ∧
      ∀ v : V,
        (if v ∈ S then (1 : ZMod 2) else 0) + (S.card : ZMod 2) +
          (((D.neighborFinset v ∩ S).card : ZMod 2)) = 0 := by
  obtain ⟨S, hSodd, hSlo, hShi, hSparity⟩ :=
    exists_normalized_oddDefectSet_of_odd_of_cubic_thirtyFour
      D W hcard hreg hW hparity
  refine ⟨S, ?_, hSparity⟩
  rcases hSodd with ⟨k, hk⟩
  omega

/-- Normalize a nontrivial even-cardinality kernel set by complementing if
necessary.  The smaller representative has even size between two and 16. -/
theorem exists_normalized_even_oddDefectSet_of_cubic_thirtyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hWempty : W ≠ ∅) (hWuniv : W ≠ Finset.univ) (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ S : Finset V, Even S.card ∧ 2 ≤ S.card ∧ S.card ≤ 16 ∧
      ∀ v : V,
        (if v ∈ S then (1 : ZMod 2) else 0) + (S.card : ZMod 2) +
          (((D.neighborFinset v ∩ S).card : ZMod 2)) = 0 := by
  have hWpos : 0 < W.card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr hWempty)
  have hWlt : W.card < 34 := by
    rw [← hcard]
    exact (Finset.card_lt_iff_ne_univ W).2 hWuniv
  by_cases hsmall : W.card ≤ 17
  · refine ⟨W, hW, ?_, ?_, hparity⟩
    · rcases hW with ⟨k, hk⟩
      omega
    · rcases hW with ⟨k, hk⟩
      omega
  · have hScard : Wᶜ.card = 34 - W.card := by
      simp [Finset.card_compl, hcard]
    have hSeven : Even Wᶜ.card := by
      rcases hW with ⟨k, hk⟩
      rw [hScard]
      refine ⟨17 - k, ?_⟩
      omega
    refine ⟨Wᶜ, hSeven, ?_, ?_,
      oddDefectSet_compl_parity_of_even_of_cubic_thirtyFour
        D W hcard hreg hW hparity⟩
    · rw [hScard]
      rcases hSeven with ⟨k, hk⟩
      omega
    · rw [hScard]
      omega

/-- Finite size dispatcher for normalized nontrivial even kernel sets. -/
theorem exists_even_oddDefectSet_card_two_or_four_or_six_or_eight_or_ten_or_twelve_or_fourteen_or_sixteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hcard : Fintype.card V = 34) (hreg : ∀ v, D.degree v = 3)
    (hWempty : W ≠ ∅) (hWuniv : W ≠ Finset.univ) (hW : Even W.card)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ S : Finset V,
      (S.card = 2 ∨ S.card = 4 ∨ S.card = 6 ∨ S.card = 8 ∨
        S.card = 10 ∨ S.card = 12 ∨ S.card = 14 ∨ S.card = 16) ∧
      ∀ v : V,
        (if v ∈ S then (1 : ZMod 2) else 0) + (S.card : ZMod 2) +
          (((D.neighborFinset v ∩ S).card : ZMod 2)) = 0 := by
  obtain ⟨S, hSeven, hSlo, hShi, hSparity⟩ :=
    exists_normalized_even_oddDefectSet_of_cubic_thirtyFour
      D W hcard hreg hWempty hWuniv hW hparity
  refine ⟨S, ?_, hSparity⟩
  rcases hSeven with ⟨k, hk⟩
  omega

/-- A two-vertex even kernel set is an adjacent-twin pair in the defect
graph: the two vertices are adjacent and have identical adjacency to every
other vertex. -/
theorem oddDefectSet_card_two_exists_adjacent_twins
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hWcard : W.card = 2)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ a b : V, a ≠ b ∧ W = {a, b} ∧ D.Adj a b ∧
      ∀ v, v ≠ a → v ≠ b → (D.Adj a v ↔ D.Adj b v) := by
  obtain ⟨a, b, hab, hW⟩ := Finset.card_eq_two.mp hWcard
  have hWeven : Even W.card := by rw [hWcard]; decide
  have hinside := oddDefectSet_no_isolated_inside_of_even D W hWeven hparity
  have haW : a ∈ W := by simp [hW]
  obtain ⟨w, hwW, haw⟩ := hinside a haW
  have hw : w = a ∨ w = b := by simpa [hW] using hwW
  have habAdj : D.Adj a b := by
    rcases hw with rfl | rfl
    · exact (D.ne_of_adj haw rfl).elim
    · exact haw
  refine ⟨a, b, hab, hW, habAdj, ?_⟩
  intro v hva hvb
  have hvW : v ∉ W := by simp [hW, hva, hvb]
  have hout := (oddDefectSet_neighborParity_of_even D W hWeven hparity).2 v hvW
  have hsub : D.neighborFinset v ∩ W ⊆ W := Finset.inter_subset_right
  have hle : (D.neighborFinset v ∩ W).card ≤ 2 := by
    rw [← hWcard]
    exact Finset.card_le_card hsub
  constructor
  · intro hav
    have haMem : a ∈ D.neighborFinset v ∩ W := Finset.mem_inter.mpr
      ⟨(D.mem_neighborFinset v a).mpr hav.symm, haW⟩
    have hpos : 0 < (D.neighborFinset v ∩ W).card :=
      Finset.card_pos.mpr ⟨a, haMem⟩
    have heq : (D.neighborFinset v ∩ W).card = 2 := by
      rcases hout with ⟨k, hk⟩
      omega
    have hall : D.neighborFinset v ∩ W = W :=
      Finset.eq_of_subset_of_card_le hsub (by rw [heq, hWcard])
    have hbMem : b ∈ D.neighborFinset v := by
      have : b ∈ D.neighborFinset v ∩ W := by rw [hall]; simp [hW]
      exact (Finset.mem_inter.mp this).1
    exact ((D.mem_neighborFinset v b).mp hbMem).symm
  · intro hbv
    have hbMem : b ∈ D.neighborFinset v ∩ W := Finset.mem_inter.mpr
      ⟨(D.mem_neighborFinset v b).mpr hbv.symm, by simp [hW]⟩
    have hpos : 0 < (D.neighborFinset v ∩ W).card :=
      Finset.card_pos.mpr ⟨b, hbMem⟩
    have heq : (D.neighborFinset v ∩ W).card = 2 := by
      rcases hout with ⟨k, hk⟩
      omega
    have hall : D.neighborFinset v ∩ W = W :=
      Finset.eq_of_subset_of_card_le hsub (by rw [heq, hWcard])
    have haMem : a ∈ D.neighborFinset v := by
      have : a ∈ D.neighborFinset v ∩ W := by rw [hall]; simp [hW]
      exact (Finset.mem_inter.mp this).1
    exact ((D.mem_neighborFinset v a).mp haMem).symm

/-- Adjacent twins in a cubic graph have exactly two common neighbors, so
their shared edge belongs to exactly two triangles. -/
theorem adjacent_twins_commonNeighbor_card_eq_two_of_cubic
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ v, D.degree v = 3) {a b : V} (hadj : D.Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b → (D.Adj a v ↔ D.Adj b v)) :
    (D.neighborFinset a ∩ D.neighborFinset b).card = 2 := by
  have heq : D.neighborFinset a ∩ D.neighborFinset b =
      (D.neighborFinset a).erase b := by
    ext v
    constructor
    · intro hv
      have hva := (Finset.mem_inter.mp hv).1
      have hvb := (Finset.mem_inter.mp hv).2
      have hvne : v ≠ b := fun h => by
        subst v
        exact D.loopless.irrefl b ((D.mem_neighborFinset b b).mp hvb)
      exact Finset.mem_erase.mpr ⟨hvne, hva⟩
    · intro hv
      have hv' := Finset.mem_erase.mp hv
      have hav : D.Adj a v := (D.mem_neighborFinset a v).mp hv'.2
      have hva : v ≠ a := fun h => by
        subst v
        exact D.loopless.irrefl a hav
      have hbv : D.Adj b v := (htwins v hva hv'.1).mp hav
      exact Finset.mem_inter.mpr
        ⟨hv'.2, (D.mem_neighborFinset b v).mpr hbv⟩
  rw [heq, Finset.card_erase_of_mem
    ((D.mem_neighborFinset a b).mpr hadj),
    D.card_neighborFinset_eq_degree, hreg a]

/-- Cubic specialization of the two-vertex kernel classification: the
forced adjacent twins have exactly two common defect neighbors. -/
theorem oddDefectSet_card_two_exists_adjacent_twins_with_two_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (W : Finset V)
    (hreg : ∀ v, D.degree v = 3) (hWcard : W.card = 2)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        (((D.neighborFinset v ∩ W).card : ZMod 2)) = 0) :
    ∃ a b : V, a ≠ b ∧ W = {a, b} ∧ D.Adj a b ∧
      (∀ v, v ≠ a → v ≠ b → (D.Adj a v ↔ D.Adj b v)) ∧
      (D.neighborFinset a ∩ D.neighborFinset b).card = 2 := by
  obtain ⟨a, b, hab, hW, hadj, htwins⟩ :=
    oddDefectSet_card_two_exists_adjacent_twins D W hWcard hparity
  exact ⟨a, b, hab, hW, hadj, htwins,
    adjacent_twins_commonNeighbor_card_eq_two_of_cubic D hreg hadj htwins⟩

/-- In an even-degree excess-one graph, the shared edge of adjacent twins in
the combined defect graph cannot have the triangle-free color. -/
theorem excessOne_even_adjacent_defect_twins_not_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V}
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    ¬ (triangleFreeEdgeGraph G).Adj a b := by
  intro habT
  have hsubset : (triangleFreeEdgeGraph G).neighborFinset a ⊆ {b} := by
    intro v hv
    have havT : (triangleFreeEdgeGraph G).Adj a v :=
      ((triangleFreeEdgeGraph G).mem_neighborFinset a v).mp hv
    by_cases hvb : v = b
    · simp [hvb]
    · have hva : v ≠ a :=
        (triangleFreeEdgeGraph G).ne_of_adj havT |>.symm
      have havD : (secondOrderDefectGraph G).Adj a v := by
        simp only [secondOrderDefectGraph, SimpleGraph.sup_adj]
        exact Or.inr havT
      have hbvD : (secondOrderDefectGraph G).Adj b v :=
        (htwins v hva hvb).mp havD
      exact (not_two_adjacent_triangleFree_in_defect_triangle
        G habT.symm havT hbvD.symm).elim
  have hbmem : b ∈ (triangleFreeEdgeGraph G).neighborFinset a :=
    ((triangleFreeEdgeGraph G).mem_neighborFinset a b).mpr habT
  have heq : (triangleFreeEdgeGraph G).neighborFinset a = {b} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hbmem, fun v hv => by
      have := hsubset hv
      simpa using this⟩
  have hdegOne : (triangleFreeEdgeGraph G).degree a = 1 := by
    rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, heq]
    simp
  rcases excessOne_even_triangleFree_degree_zero_or_two
      G hfree heven hreg hcard a with hzero | htwo <;> omega

/-- Therefore the shared edge of adjacent defect twins has the antipodal
color. -/
theorem excessOne_even_adjacent_defect_twins_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    (antipodalGraph G).Adj a b := by
  simp only [secondOrderDefectGraph, SimpleGraph.sup_adj] at habD
  rcases habD with habC | habT
  · exact habC
  · exact (excessOne_even_adjacent_defect_twins_not_triangleFree
      G hfree heven hreg hcard htwins habT).elim

/-- The triangle-free degrees at adjacent defect twins have exactly three
possibilities: `(0,0)`, `(2,0)`, or `(0,2)`.  The `(2,2)` case would force
both two-element color neighborhoods to equal the same pair of common defect
neighbors, creating a forbidden defect triangle with two triangle-free
edges. -/
theorem excessOne_even_adjacent_defect_twins_triangleFree_degree_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    ((triangleFreeEdgeGraph G).degree a = 0 ∧
        (triangleFreeEdgeGraph G).degree b = 0) ∨
      ((triangleFreeEdgeGraph G).degree a = 2 ∧
        (triangleFreeEdgeGraph G).degree b = 0) ∨
      ((triangleFreeEdgeGraph G).degree a = 0 ∧
        (triangleFreeEdgeGraph G).degree b = 2) := by
  have haCases := excessOne_even_triangleFree_degree_zero_or_two
    G hfree heven hreg hcard a
  have hbCases := excessOne_even_triangleFree_degree_zero_or_two
    G hfree heven hreg hcard b
  rcases haCases with ha0 | ha2
  · rcases hbCases with hb0 | hb2
    · exact Or.inl ⟨ha0, hb0⟩
    · exact Or.inr (Or.inr ⟨ha0, hb2⟩)
  · rcases hbCases with hb0 | hb2
    · exact Or.inr (Or.inl ⟨ha2, hb0⟩)
    · exfalso
      have habT : ¬ (triangleFreeEdgeGraph G).Adj a b :=
        excessOne_even_adjacent_defect_twins_not_triangleFree
          G hfree heven hreg hcard htwins
      have hDreg : ∀ x, (secondOrderDefectGraph G).degree x = 3 := by
        intro x
        simpa using secondOrderDefectGraph_degree_eq_excess_add_two
          G hfree hreg (e := 1) (by simpa using hcard) x
      have hcommon : ((secondOrderDefectGraph G).neighborFinset a ∩
          (secondOrderDefectGraph G).neighborFinset b).card = 2 :=
        adjacent_twins_commonNeighbor_card_eq_two_of_cubic
          (secondOrderDefectGraph G) hDreg habD htwins
      let C := (secondOrderDefectGraph G).neighborFinset a ∩
        (secondOrderDefectGraph G).neighborFinset b
      have haSub : (triangleFreeEdgeGraph G).neighborFinset a ⊆ C := by
        intro v hv
        have havT := ((triangleFreeEdgeGraph G).mem_neighborFinset a v).mp hv
        have havD : (secondOrderDefectGraph G).Adj a v := by
          simp only [secondOrderDefectGraph, SimpleGraph.sup_adj]
          exact Or.inr havT
        have hva : v ≠ a := (triangleFreeEdgeGraph G).ne_of_adj havT |>.symm
        have hvb : v ≠ b := fun h => by
          subst v
          exact habT havT
        have hbvD := (htwins v hva hvb).mp havD
        exact Finset.mem_inter.mpr
          ⟨((secondOrderDefectGraph G).mem_neighborFinset a v).mpr havD,
            ((secondOrderDefectGraph G).mem_neighborFinset b v).mpr hbvD⟩
      have hbSub : (triangleFreeEdgeGraph G).neighborFinset b ⊆ C := by
        intro v hv
        have hbvT := ((triangleFreeEdgeGraph G).mem_neighborFinset b v).mp hv
        have hbvD : (secondOrderDefectGraph G).Adj b v := by
          simp only [secondOrderDefectGraph, SimpleGraph.sup_adj]
          exact Or.inr hbvT
        have hvb : v ≠ b := (triangleFreeEdgeGraph G).ne_of_adj hbvT |>.symm
        have hva : v ≠ a := fun h => by
          subst v
          exact habT hbvT.symm
        have havD := (htwins v hva hvb).mpr hbvD
        exact Finset.mem_inter.mpr
          ⟨((secondOrderDefectGraph G).mem_neighborFinset a v).mpr havD,
            ((secondOrderDefectGraph G).mem_neighborFinset b v).mpr hbvD⟩
      have haCard : ((triangleFreeEdgeGraph G).neighborFinset a).card = 2 := by
        rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, ha2]
      have hbCard : ((triangleFreeEdgeGraph G).neighborFinset b).card = 2 := by
        rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, hb2]
      have haEq : (triangleFreeEdgeGraph G).neighborFinset a = C :=
        Finset.eq_of_subset_of_card_le haSub (by
          rw [haCard]
          simpa [C] using hcommon.le)
      have hbEq : (triangleFreeEdgeGraph G).neighborFinset b = C :=
        Finset.eq_of_subset_of_card_le hbSub (by
          rw [hbCard]
          simpa [C] using hcommon.le)
      have hCcard : C.card = 2 := by simpa [C] using hcommon
      have hCpos : 0 < C.card := by rw [hCcard]; omega
      obtain ⟨v, hvC⟩ := Finset.card_pos.mp hCpos
      have havT : (triangleFreeEdgeGraph G).Adj a v :=
        ((triangleFreeEdgeGraph G).mem_neighborFinset a v).mp (by
          rw [haEq]; exact hvC)
      have hbvT : (triangleFreeEdgeGraph G).Adj b v :=
        ((triangleFreeEdgeGraph G).mem_neighborFinset b v).mp (by
          rw [hbEq]; exact hvC)
      exact not_two_adjacent_triangleFree_in_defect_triangle
        G havT hbvT.symm habD.symm

/-- Full two-color degree profile at adjacent defect twins.  The three
triangle-free cases lift respectively to `(T,C)` degree pairs
`((0,3),(0,3))`, `((2,1),(0,3))`, and `((0,3),(2,1))`. -/
theorem excessOne_even_adjacent_defect_twins_color_degree_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    (((triangleFreeEdgeGraph G).degree a = 0 ∧
          (antipodalGraph G).degree a = 3) ∧
        ((triangleFreeEdgeGraph G).degree b = 0 ∧
          (antipodalGraph G).degree b = 3)) ∨
      (((triangleFreeEdgeGraph G).degree a = 2 ∧
          (antipodalGraph G).degree a = 1) ∧
        ((triangleFreeEdgeGraph G).degree b = 0 ∧
          (antipodalGraph G).degree b = 3)) ∨
      (((triangleFreeEdgeGraph G).degree a = 0 ∧
          (antipodalGraph G).degree a = 3) ∧
        ((triangleFreeEdgeGraph G).degree b = 2 ∧
          (antipodalGraph G).degree b = 1)) := by
  have ha := excessOne_even_color_degree_classification
    G hfree heven hreg hcard a
  have hb := excessOne_even_color_degree_classification
    G hfree heven hreg hcard b
  rcases excessOne_even_adjacent_defect_twins_triangleFree_degree_cases
      G hfree heven hreg hcard habD htwins with h00 | h20 | h02
  · left
    rcases ha with ha0 | ha2
    · rcases hb with hb0 | hb2
      · exact ⟨ha0, hb0⟩
      · omega
    · omega
  · right; left
    rcases ha with ha0 | ha2
    · omega
    · rcases hb with hb0 | hb2
      · exact ⟨ha2, hb0⟩
      · omega
  · right; right
    rcases ha with ha0 | ha2
    · rcases hb with hb0 | hb2
      · omega
      · exact ⟨ha0, hb2⟩
    · omega

/-- In the asymmetric twin-diamond case, every common defect neighbor is
joined to the degree-two twin by the triangle-free color and to the
degree-zero twin by the antipodal color. -/
theorem excessOne_even_adjacent_defect_twins_asymmetric_spokes
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v))
    (ha2 : (triangleFreeEdgeGraph G).degree a = 2)
    (hb0 : (triangleFreeEdgeGraph G).degree b = 0) :
    ∀ v ∈ (secondOrderDefectGraph G).neighborFinset a ∩
        (secondOrderDefectGraph G).neighborFinset b,
      (triangleFreeEdgeGraph G).Adj a v ∧
        (antipodalGraph G).Adj b v := by
  have habT : ¬ (triangleFreeEdgeGraph G).Adj a b :=
    excessOne_even_adjacent_defect_twins_not_triangleFree
      G hfree heven hreg hcard htwins
  have hDreg : ∀ x, (secondOrderDefectGraph G).degree x = 3 := by
    intro x
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) x
  let C := (secondOrderDefectGraph G).neighborFinset a ∩
    (secondOrderDefectGraph G).neighborFinset b
  have hcommon : C.card = 2 := by
    simpa [C] using adjacent_twins_commonNeighbor_card_eq_two_of_cubic
      (secondOrderDefectGraph G) hDreg habD htwins
  have haSub : (triangleFreeEdgeGraph G).neighborFinset a ⊆ C := by
    intro v hv
    have havT := ((triangleFreeEdgeGraph G).mem_neighborFinset a v).mp hv
    have havD : (secondOrderDefectGraph G).Adj a v := by
      simp only [secondOrderDefectGraph, SimpleGraph.sup_adj]
      exact Or.inr havT
    have hva : v ≠ a := (triangleFreeEdgeGraph G).ne_of_adj havT |>.symm
    have hvb : v ≠ b := fun h => by
      subst v
      exact habT havT
    have hbvD := (htwins v hva hvb).mp havD
    exact Finset.mem_inter.mpr
      ⟨((secondOrderDefectGraph G).mem_neighborFinset a v).mpr havD,
        ((secondOrderDefectGraph G).mem_neighborFinset b v).mpr hbvD⟩
  have haCard : ((triangleFreeEdgeGraph G).neighborFinset a).card = 2 := by
    rw [(triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, ha2]
  have haEq : (triangleFreeEdgeGraph G).neighborFinset a = C :=
    Finset.eq_of_subset_of_card_le haSub (by rw [haCard, hcommon])
  intro v hv
  have hvC : v ∈ C := by simpa [C] using hv
  have havT : (triangleFreeEdgeGraph G).Adj a v :=
    ((triangleFreeEdgeGraph G).mem_neighborFinset a v).mp (by
      rw [haEq]
      exact hvC)
  have hbvD : (secondOrderDefectGraph G).Adj b v :=
    ((secondOrderDefectGraph G).mem_neighborFinset b v).mp
      (Finset.mem_inter.mp hv).2
  have hbvNotT : ¬ (triangleFreeEdgeGraph G).Adj b v := by
    intro hbvT
    have hmem := ((triangleFreeEdgeGraph G).mem_neighborFinset b v).mpr hbvT
    have hempty : (triangleFreeEdgeGraph G).neighborFinset b = ∅ := by
      rw [← Finset.card_eq_zero,
        (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, hb0]
    rw [hempty] at hmem
    exact Finset.notMem_empty v hmem
  simp only [secondOrderDefectGraph, SimpleGraph.sup_adj] at hbvD
  exact ⟨havT, hbvD.resolve_right hbvNotT⟩

/-- The asymmetric twin-diamond colorings are impossible.  At the `(a,b)`
entry, `A D` counts both common defect neighbors because their `a`-spokes
are triangle-free, while `D A` counts none because their `b`-spokes are
antipodal.  This contradicts commutation of `A` with the combined defect
operator `D`. -/
theorem excessOne_even_adjacent_defect_twins_not_asymmetric
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    ¬ ((triangleFreeEdgeGraph G).degree a = 2 ∧
        (triangleFreeEdgeGraph G).degree b = 0) := by
  rintro ⟨ha2, hb0⟩
  let D := secondOrderDefectGraph G
  let C := D.neighborFinset a ∩ D.neighborFinset b
  have hDreg : ∀ x, D.degree x = 3 := by
    intro x
    simpa [D] using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) x
  have hCcard : C.card = 2 := by
    simpa [C, D] using adjacent_twins_commonNeighbor_card_eq_two_of_cubic
      (secondOrderDefectGraph G) (by simpa [D] using hDreg) habD htwins
  have hspokes := excessOne_even_adjacent_defect_twins_asymmetric_spokes
    G hfree heven hreg hcard habD htwins ha2 hb0
  have hleftSub : C ⊆ G.neighborFinset a ∩ D.neighborFinset b := by
    intro v hv
    have hv' : v ∈ (secondOrderDefectGraph G).neighborFinset a ∩
        (secondOrderDefectGraph G).neighborFinset b := by simpa [C, D] using hv
    have havT := (hspokes v hv').1
    have hvParts := Finset.mem_inter.mp hv'
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset a v).mpr
          (((mem_triangleFreeNeighbors G a v).mp
            ((triangleFreeEdgeGraph_adj G a v).mp havT)).1),
        (D.mem_neighborFinset b v).mpr (by
          simpa [D] using
            ((secondOrderDefectGraph G).mem_neighborFinset b v).mp hvParts.2)⟩
  have hleft : 2 ≤ (G.neighborFinset a ∩ D.neighborFinset b).card := by
    rw [← hCcard]
    exact Finset.card_le_card hleftSub
  have hrightEmpty : D.neighborFinset a ∩ G.neighborFinset b = ∅ := by
    ext v
    simp
    intro havD' hbvG
    have havD : (secondOrderDefectGraph G).Adj a v := by
      simpa [D] using havD'
    have hva : v ≠ a := fun h => by
      subst v
      exact (secondOrderDefectGraph G).loopless.irrefl a havD
    have hvb : v ≠ b := fun h => by
      subst v
      exact G.loopless.irrefl b hbvG
    have hbvD : (secondOrderDefectGraph G).Adj b v :=
      (htwins v hva hvb).mp havD
    have hvCommon : v ∈ (secondOrderDefectGraph G).neighborFinset a ∩
        (secondOrderDefectGraph G).neighborFinset b :=
      Finset.mem_inter.mpr
        ⟨((secondOrderDefectGraph G).mem_neighborFinset a v).mpr havD,
          ((secondOrderDefectGraph G).mem_neighborFinset b v).mpr hbvD⟩
    have hbvC := (hspokes v hvCommon).2
    exact ((mem_antipodalNeighbors G b v).mp
      ((antipodalGraph_adj G b v).mp hbvC)).2.1 hbvG
  have hcomm := adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hab := congrFun (congrFun hcomm a) b
  rw [adjMatrix_mul_subgraph_apply_eq_card_mixed,
    adjMatrix_mul_subgraph_apply_eq_card_mixed] at hab
  have hright : (D.neighborFinset a ∩ G.neighborFinset b).card = 0 := by
    rw [hrightEmpty, Finset.card_empty]
  change ((G.neighborFinset a ∩ D.neighborFinset b).card : ℤ) =
      ((D.neighborFinset a ∩ G.neighborFinset b).card : ℤ) at hab
  rw [hright] at hab
  omega

/-- Hence adjacent defect twins can only have triangle-free degree zero at
both endpoints. -/
theorem excessOne_even_adjacent_defect_twins_triangleFree_degree_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    (triangleFreeEdgeGraph G).degree a = 0 ∧
      (triangleFreeEdgeGraph G).degree b = 0 := by
  rcases excessOne_even_adjacent_defect_twins_triangleFree_degree_cases
      G hfree heven hreg hcard habD htwins with h00 | h20 | h02
  · exact h00
  · exact (excessOne_even_adjacent_defect_twins_not_asymmetric
      G hfree heven hreg hcard habD htwins h20).elim
  · have hcontra := excessOne_even_adjacent_defect_twins_not_asymmetric
      G hfree heven hreg hcard habD.symm (fun v hvb hva =>
        (htwins v hva hvb).symm) ⟨h02.2, h02.1⟩
    exact hcontra.elim

/-- The all-antipodal twin diamond propagates the zero triangle-free degree
to both common defect neighbors.  Each such vertex already has the two
distinct antipodal neighbors `a` and `b`, ruling out the alternative local
profile `(T,C) = (2,1)`. -/
theorem excessOne_even_adjacent_defect_twins_common_color_degree_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    ∀ v ∈ (secondOrderDefectGraph G).neighborFinset a ∩
        (secondOrderDefectGraph G).neighborFinset b,
      (triangleFreeEdgeGraph G).degree v = 0 ∧
        (antipodalGraph G).degree v = 3 := by
  have hzero := excessOne_even_adjacent_defect_twins_triangleFree_degree_zero
    G hfree heven hreg hcard habD htwins
  have hab : a ≠ b := (secondOrderDefectGraph G).ne_of_adj habD
  intro v hv
  have hvParts := Finset.mem_inter.mp hv
  have havD := ((secondOrderDefectGraph G).mem_neighborFinset a v).mp hvParts.1
  have hbvD := ((secondOrderDefectGraph G).mem_neighborFinset b v).mp hvParts.2
  have havNotT : ¬ (triangleFreeEdgeGraph G).Adj a v := by
    intro havT
    have hmem := ((triangleFreeEdgeGraph G).mem_neighborFinset a v).mpr havT
    have hempty : (triangleFreeEdgeGraph G).neighborFinset a = ∅ := by
      rw [← Finset.card_eq_zero,
        (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, hzero.1]
    rw [hempty] at hmem
    exact Finset.notMem_empty v hmem
  have hbvNotT : ¬ (triangleFreeEdgeGraph G).Adj b v := by
    intro hbvT
    have hmem := ((triangleFreeEdgeGraph G).mem_neighborFinset b v).mpr hbvT
    have hempty : (triangleFreeEdgeGraph G).neighborFinset b = ∅ := by
      rw [← Finset.card_eq_zero,
        (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree, hzero.2]
    rw [hempty] at hmem
    exact Finset.notMem_empty v hmem
  have havC : (antipodalGraph G).Adj a v := by
    simp only [secondOrderDefectGraph, SimpleGraph.sup_adj] at havD
    exact havD.resolve_right havNotT
  have hbvC : (antipodalGraph G).Adj b v := by
    simp only [secondOrderDefectGraph, SimpleGraph.sup_adj] at hbvD
    exact hbvD.resolve_right hbvNotT
  have hpairs : ({a, b} : Finset V) ⊆ (antipodalGraph G).neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · rw [hx]
      exact ((antipodalGraph G).mem_neighborFinset v a).mpr havC.symm
    · rw [hx]
      exact ((antipodalGraph G).mem_neighborFinset v b).mpr hbvC.symm
  have hpairsCard : ({a, b} : Finset V).card = 2 := by simp [hab]
  have hCtwo : 2 ≤ (antipodalGraph G).degree v := by
    rw [← (antipodalGraph G).card_neighborFinset_eq_degree, ← hpairsCard]
    exact Finset.card_le_card hpairs
  rcases excessOne_even_color_degree_classification
      G hfree heven hreg hcard v with h03 | h21
  · exact h03
  · omega

/-- Quantitative form of the propagated all-antipodal diamond: adjacent
defect twins force at least four vertices into the triangle-free-degree-zero
sector (the twins and their two common defect neighbors). -/
theorem excessOne_even_adjacent_defect_twins_four_le_colorDegreeZero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    4 ≤ (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 0).card := by
  let C := (secondOrderDefectGraph G).neighborFinset a ∩
    (secondOrderDefectGraph G).neighborFinset b
  have hDreg : ∀ x, (secondOrderDefectGraph G).degree x = 3 := by
    intro x
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) x
  have hCcard : C.card = 2 := by
    simpa [C] using adjacent_twins_commonNeighbor_card_eq_two_of_cubic
      (secondOrderDefectGraph G) hDreg habD htwins
  have haNotC : a ∉ C := by
    intro ha
    have haa := ((secondOrderDefectGraph G).mem_neighborFinset a a).mp
      (Finset.mem_inter.mp ha).1
    exact (secondOrderDefectGraph G).loopless.irrefl a haa
  have hbNotC : b ∉ C := by
    intro hb
    have hbb := ((secondOrderDefectGraph G).mem_neighborFinset b b).mp
      (Finset.mem_inter.mp hb).2
    exact (secondOrderDefectGraph G).loopless.irrefl b hbb
  let Q := insert a (insert b C)
  have hQcard : Q.card = 4 := by
    have hbNot : b ∉ C := hbNotC
    have haNot : a ∉ insert b C := by
      simp only [Finset.mem_insert]
      exact fun h => h.elim (fun hab =>
        (secondOrderDefectGraph G).ne_of_adj habD hab) haNotC
    simp only [Q, Finset.card_insert_of_notMem haNot,
      Finset.card_insert_of_notMem hbNot, hCcard]
  have hzero := excessOne_even_adjacent_defect_twins_triangleFree_degree_zero
    G hfree heven hreg hcard habD htwins
  have hcommon :=
    excessOne_even_adjacent_defect_twins_common_color_degree_zero
      G hfree heven hreg hcard habD htwins
  have hQsub : Q ⊆ Finset.univ.filter (fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 0) := by
    intro v hv
    simp only [Q, Finset.mem_insert] at hv
    rcases hv with rfl | rfl | hv
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero.1⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero.2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hcommon v hv).1⟩
  rw [← hQcard]
  exact Finset.card_le_card hQsub

/-- Exact global color-order dispatcher forced by a size-two defect kernel
at order 34.  The degree-two sector is a union of cycles, its order is
divisible by three, and the propagated all-antipodal seed leaves at least
four vertices outside it. -/
theorem degreeSix_thirtyFour_adjacent_defect_twins_colorOrder_cases
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 34)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v)) :
    let s := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card
    s = 0 ∨ s = 6 ∨ s = 9 ∨ s = 12 ∨ s = 15 ∨ s = 18 ∨
      s = 21 ∨ s = 24 ∨ s = 27 ∨ s = 30 := by
  let s := (Finset.univ.filter fun x : V =>
    (triangleFreeEdgeGraph G).degree x = 2).card
  let z := (Finset.univ.filter fun x : V =>
    (triangleFreeEdgeGraph G).degree x = 0).card
  have hlocal := excessOne_even_triangleFree_degree_zero_or_two
    G hfree (d := 6) (by norm_num) hreg (by omega)
  have hnot : (Finset.univ.filter fun x : V =>
      ¬ (triangleFreeEdgeGraph G).degree x = 2) =
      Finset.univ.filter (fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 0) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hlocal x with hx | hx <;> simp [hx]
  have hpartition : s + z = 34 := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V))
      (p := fun x : V => (triangleFreeEdgeGraph G).degree x = 2)
    rw [hnot, Finset.card_univ, hcard] at hsplit
    exact hsplit
  have hz : 4 ≤ z := by
    exact excessOne_even_adjacent_defect_twins_four_le_colorDegreeZero
      G hfree (d := 6) (by norm_num) hreg (by omega) habD htwins
  have hmod : s % 3 = 0 := by
    exact degreeSix_thirtyFour_colorOrder_mod_three G hfree hreg hcard
  have hpath : s = 0 ∨ 5 ≤ s := by
    exact excessOne_even_pathSector_card_eq_zero_or_five_le
      G hfree (d := 6) (by norm_num) hreg (by omega)
  dsimp only
  omega

/-- In the pure antipodal size-two-kernel branch, the original-graph
neighborhoods of the defect twins are disjoint and the bipartite graph
between them is one-regular on both sides.  Thus the two six-element
neighborhoods are joined by a perfect matching. -/
theorem degreeSix_thirtyFour_adjacent_defect_twins_neighbor_matching_of_colorOrder_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 34)
    {a b : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v))
    (hzero : (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card = 0) :
    G.neighborFinset a ∩ G.neighborFinset b = ∅ ∧
      (∀ p ∈ G.neighborFinset a,
        (G.neighborFinset p ∩ G.neighborFinset b).card = 1) ∧
      ∀ q ∈ G.neighborFinset b,
        (G.neighborFinset q ∩ G.neighborFinset a).card = 1 := by
  have hDeq :=
    degreeSix_thirtyFour_secondOrderDefectGraph_eq_antipodalGraph_of_colorOrder_zero
      G hfree hreg hcard hzero
  have habC : (antipodalGraph G).Adj a b := by
    rw [← hDeq]
    exact habD
  have habFacts := (mem_antipodalNeighbors G a b).mp
    ((antipodalGraph_adj G a b).mp habC)
  have habNotG : ¬ G.Adj a b := habFacts.2.1
  have habCommon : G.neighborFinset a ∩ G.neighborFinset b = ∅ := by
    exact Finset.card_eq_zero.mp habFacts.2.2
  refine ⟨habCommon, ?_, ?_⟩
  · intro p hp
    have hapG : G.Adj a p := (G.mem_neighborFinset a p).mp hp
    have hpa : p ≠ a := fun h => G.loopless.irrefl a (h ▸ hapG)
    have hpb : p ≠ b := by
      intro h
      exact habNotG (h ▸ hapG)
    have hnotDa : ¬ (secondOrderDefectGraph G).Adj a p := by
      rw [hDeq]
      intro hapC
      exact ((mem_antipodalNeighbors G a p).mp
        ((antipodalGraph_adj G a p).mp hapC)).2.1 hapG
    have hnotDb : ¬ (secondOrderDefectGraph G).Adj b p := by
      intro hbpD
      exact hnotDa ((htwins p hpa hpb).mpr hbpD)
    have hnotMem : p ∉ (secondOrderDefectGraph G).neighborFinset b := by
      simpa using hnotDb
    have hone := card_common_eq_if_secondOrderDefect
      G hfree b p hpb.symm
    rw [if_neg hnotMem] at hone
    simpa [Finset.inter_comm] using hone
  · intro q hq
    have hbqG : G.Adj b q := (G.mem_neighborFinset b q).mp hq
    have hqb : q ≠ b := fun h => G.loopless.irrefl b (h ▸ hbqG)
    have hqa : q ≠ a := by
      intro h
      exact habNotG (by simpa [h] using hbqG.symm)
    have hnotDb : ¬ (secondOrderDefectGraph G).Adj b q := by
      rw [hDeq]
      intro hbqC
      exact ((mem_antipodalNeighbors G b q).mp
        ((antipodalGraph_adj G b q).mp hbqC)).2.1 hbqG
    have hnotDa : ¬ (secondOrderDefectGraph G).Adj a q := by
      intro haqD
      exact hnotDb ((htwins q hqa hqb).mp haqD)
    have hnotMem : q ∉ (secondOrderDefectGraph G).neighborFinset a := by
      simpa using hnotDa
    have hone := card_common_eq_if_secondOrderDefect
      G hfree a q hqa.symm
    rw [if_neg hnotMem] at hone
    simpa [Finset.inter_comm] using hone

/-- The four vertices of a cubic defect-twin diamond already have original
neighborhood union of order at least 23.  Every defect edge makes the two
corresponding original neighborhoods disjoint; among the six diamond pairs,
only the pair of common defect neighbors can overlap, and C4-freeness bounds
that overlap by one. -/
theorem degreeSix_adjacent_defect_twins_four_neighborhood_union_twentyThree_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ v, G.degree v = 6)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : x ≠ y) :
    23 ≤ (G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y).card := by
  have hinter_of_defect : ∀ {u v : V},
      (secondOrderDefectGraph G).Adj u v →
        G.neighborFinset u ∩ G.neighborFinset v = ∅ := by
    intro u v huv
    have hne : u ≠ v := (secondOrderDefectGraph G).ne_of_adj huv
    have hmem : v ∈ (secondOrderDefectGraph G).neighborFinset u :=
      ((secondOrderDefectGraph G).mem_neighborFinset u v).mpr huv
    have hc := card_common_eq_if_secondOrderDefect G hfree u v hne
    rw [if_pos hmem] at hc
    exact Finset.card_eq_zero.mp hc
  have hdAB : Disjoint (G.neighborFinset a) (G.neighborFinset b) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (hinter_of_defect hab)
  have hdAX : Disjoint (G.neighborFinset a) (G.neighborFinset x) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (hinter_of_defect hax)
  have hdBX : Disjoint (G.neighborFinset b) (G.neighborFinset x) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (hinter_of_defect hbx)
  have hdAY : Disjoint (G.neighborFinset a) (G.neighborFinset y) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (hinter_of_defect hay)
  have hdBY : Disjoint (G.neighborFinset b) (G.neighborFinset y) :=
    Finset.disjoint_iff_inter_eq_empty.mpr (hinter_of_defect hby)
  have hdABX : Disjoint
      (G.neighborFinset a ∪ G.neighborFinset b) (G.neighborFinset x) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdAX, hdBX⟩
  have hdABY : Disjoint
      (G.neighborFinset a ∪ G.neighborFinset b) (G.neighborFinset y) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdAY, hdBY⟩
  have hABcard : (G.neighborFinset a ∪ G.neighborFinset b).card = 12 := by
    rw [Finset.card_union_of_disjoint hdAB,
      G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree,
      hreg a, hreg b]
  have hABXcard : (G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x).card = 18 := by
    rw [Finset.card_union_of_disjoint hdABX, hABcard,
      G.card_neighborFinset_eq_degree, hreg x]
  have hinterSub :
      ((G.neighborFinset a ∪ G.neighborFinset b ∪ G.neighborFinset x) ∩
          G.neighborFinset y) ⊆
        G.neighborFinset x ∩ G.neighborFinset y := by
    intro z hz
    have hzparts := Finset.mem_inter.mp hz
    refine Finset.mem_inter.mpr ⟨?_, hzparts.2⟩
    rcases Finset.mem_union.mp hzparts.1 with hzAB | hzx
    · exact (Finset.disjoint_left.mp hdABY hzAB hzparts.2).elim
    · exact hzx
  have hinterLe : ((G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x) ∩ G.neighborFinset y).card ≤ 1 := by
    exact (Finset.card_le_card hinterSub).trans
      (common_le_one_of_not_containsC4 hfree x y hxy)
  have hie := Finset.card_union_add_card_inter
    (G.neighborFinset a ∪ G.neighborFinset b ∪ G.neighborFinset x)
    (G.neighborFinset y)
  rw [hABXcard, G.card_neighborFinset_eq_degree, hreg y] at hie
  omega

/-- A size-two even defect-kernel set therefore produces an explicit
four-vertex defect diamond whose four original neighborhoods occupy at
least 23 vertices. -/
theorem oddDefectSet_card_two_exists_twinDiamond_neighborhood_union_twentyThree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ v, G.degree v = 6)
    (hregD : ∀ v, (secondOrderDefectGraph G).degree v = 3)
    (W : Finset V) (hWcard : W.card = 2)
    (hparity : ∀ v : V,
      (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
        ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
          ZMod 2)) = 0) :
    ∃ a b x y : V,
      (secondOrderDefectGraph G).Adj a b ∧
      (secondOrderDefectGraph G).Adj a x ∧
      (secondOrderDefectGraph G).Adj b x ∧
      (secondOrderDefectGraph G).Adj a y ∧
      (secondOrderDefectGraph G).Adj b y ∧ x ≠ y ∧
      23 ≤ (G.neighborFinset a ∪ G.neighborFinset b ∪
        G.neighborFinset x ∪ G.neighborFinset y).card := by
  obtain ⟨a, b, _habne, _hW, hab, htwins⟩ :=
    oddDefectSet_card_two_exists_adjacent_twins
      (secondOrderDefectGraph G) W hWcard hparity
  let C := (secondOrderDefectGraph G).neighborFinset a ∩
    (secondOrderDefectGraph G).neighborFinset b
  have hCcard : C.card = 2 := by
    simpa [C] using adjacent_twins_commonNeighbor_card_eq_two_of_cubic
      (secondOrderDefectGraph G) hregD hab htwins
  obtain ⟨x, y, hxy, hC⟩ := Finset.card_eq_two.mp hCcard
  have hxC : x ∈ C := by rw [hC]; simp
  have hyC : y ∈ C := by rw [hC]; simp
  have hxParts := Finset.mem_inter.mp hxC
  have hyParts := Finset.mem_inter.mp hyC
  have hax := ((secondOrderDefectGraph G).mem_neighborFinset a x).mp hxParts.1
  have hbx := ((secondOrderDefectGraph G).mem_neighborFinset b x).mp hxParts.2
  have hay := ((secondOrderDefectGraph G).mem_neighborFinset a y).mp hyParts.1
  have hby := ((secondOrderDefectGraph G).mem_neighborFinset b y).mp hyParts.2
  exact ⟨a, b, x, y, hab, hax, hbx, hay, hby, hxy,
    degreeSix_adjacent_defect_twins_four_neighborhood_union_twentyThree_le
      G hfree hreg hab hax hbx hay hby hxy⟩

/-- Every hypothetical degree-six plateau core at order 34 carries a proper,
nonempty defect set satisfying the exact mod-two neighborhood law. -/
theorem C4PlateauCore.degreeSix_thirtyFour_exists_odd_defect_set
    (hcore : C4PlateauCore 34 6) :
    ∃ (G : SimpleGraph (Fin 34)) (_ : DecidableRel G.Adj)
        (W : Finset (Fin 34)),
      ¬ containsC4 (Fin 34) G ∧
      (∀ x, G.degree x = 6) ∧
      W ≠ ∅ ∧ W ≠ Finset.univ ∧ ∀ v : Fin 34,
        (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
          ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
            ZMod 2)) = 0 := by
  rcases hcore.degreeSix_thirtyFour_positiveExcessOne with
    ⟨_hm, _he, G, hdec, hfree, hreg, _hregD, _hsq, _hcomm, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  obtain ⟨W, hWempty, hWuniv, hWparity⟩ :=
    excessOne_even_exists_odd_defect_set G hfree (by decide) hreg (by norm_num)
  exact ⟨G, hdec, W, hfree, hreg, hWempty, hWuniv, hWparity⟩

/-- Plateau-facing structural dichotomy for the order-34 excess-one kernel.
The even-cardinality branch has no isolated vertex in the induced defect
subgraph; the odd branch admits a normalized representative of one of five
explicit sizes. -/
theorem C4PlateauCore.degreeSix_thirtyFour_defectKernel_dichotomy
    (hcore : C4PlateauCore 34 6) :
    ∃ (G : SimpleGraph (Fin 34)) (_ : DecidableRel G.Adj)
        (W : Finset (Fin 34)),
      ¬ containsC4 (Fin 34) G ∧
      (∀ x, G.degree x = 6) ∧
      (∀ x, (secondOrderDefectGraph G).degree x = 3) ∧
      W ≠ ∅ ∧ W ≠ Finset.univ ∧
      (∀ v : Fin 34,
        (if v ∈ W then (1 : ZMod 2) else 0) + (W.card : ZMod 2) +
          ((((secondOrderDefectGraph G).neighborFinset v ∩ W).card :
            ZMod 2)) = 0) ∧
      ((Even W.card ∧ (∀ v ∈ W, ∃ w ∈ W,
          (secondOrderDefectGraph G).Adj v w) ∧
          ∃ S : Finset (Fin 34),
            (S.card = 2 ∨ S.card = 4 ∨ S.card = 6 ∨ S.card = 8 ∨
              S.card = 10 ∨ S.card = 12 ∨ S.card = 14 ∨ S.card = 16) ∧
            ∀ v : Fin 34,
              (if v ∈ S then (1 : ZMod 2) else 0) +
                (S.card : ZMod 2) +
                ((((secondOrderDefectGraph G).neighborFinset v ∩ S).card :
                  ZMod 2)) = 0) ∨
        ∃ S : Finset (Fin 34),
          (S.card = 9 ∨ S.card = 11 ∨ S.card = 13 ∨
            S.card = 15 ∨ S.card = 17) ∧
          ∀ v : Fin 34,
            (if v ∈ S then (1 : ZMod 2) else 0) + (S.card : ZMod 2) +
              ((((secondOrderDefectGraph G).neighborFinset v ∩ S).card :
                ZMod 2)) = 0) := by
  rcases hcore.degreeSix_thirtyFour_positiveExcessOne with
    ⟨_hm, _he, G, hdec, hfree, hreg, hregD, _hsq, _hcomm, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  obtain ⟨W, hWempty, hWuniv, hWparity⟩ :=
    excessOne_even_exists_odd_defect_set G hfree (by decide) hreg (by norm_num)
  have hDreg : ∀ x, (secondOrderDefectGraph G).degree x = 3 := by
    intro x
    simpa using hregD x
  refine ⟨G, hdec, W, hfree, hreg, hDreg, hWempty, hWuniv,
    hWparity, ?_⟩
  rcases Nat.even_or_odd W.card with hWeven | hWodd
  · left
    exact ⟨hWeven,
      oddDefectSet_no_isolated_inside_of_even
        (secondOrderDefectGraph G) W hWeven hWparity,
      exists_even_oddDefectSet_card_two_or_four_or_six_or_eight_or_ten_or_twelve_or_fourteen_or_sixteen
        (secondOrderDefectGraph G) W (by simp) hDreg hWempty hWuniv
          hWeven hWparity⟩
  · right
    exact exists_oddDefectSet_card_nine_or_eleven_or_thirteen_or_fifteen_or_seventeen
      (secondOrderDefectGraph G) W (by simp) hDreg hWodd hWparity

end

end Erdos85
