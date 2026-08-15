import Proofs.Erdos85DegreeSixBoundaryPackage
import Proofs.Erdos85EvenExcessOneDefectKernel
import Proofs.Erdos85BoundedReplacementObstruction
import Proofs.Erdos85EvenExcessOneThirdMoment
import Proofs.Erdos85AlternatingFourthMoment
import Proofs.Erdos85SecondOrderColorTrace
import Proofs.Erdos85ExcessEigenspace
import Proofs.Erdos85QuadraticDimension
import Proofs.Erdos85PositiveExcessOnePropagation

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

/-- Endpoints of a second-order defect edge have disjoint original-graph
neighborhoods. -/
theorem neighborFinset_disjoint_of_secondOrderDefect_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {u v : V}
    (huv : (secondOrderDefectGraph G).Adj u v) :
    Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
  have huvNe : u ≠ v := (secondOrderDefectGraph G).ne_of_adj huv
  have hvMem : v ∈ (secondOrderDefectGraph G).neighborFinset u :=
    ((secondOrderDefectGraph G).mem_neighborFinset u v).mpr huv
  have hcommon := card_common_eq_if_secondOrderDefect G hfree u v huvNe
  rw [if_pos hvMem] at hcommon
  exact Finset.disjoint_iff_inter_eq_empty.mpr (Finset.card_eq_zero.mp hcommon)

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

/-- The `-3` defect eigenspace likewise has even rational dimension: the
original adjacency restriction squares to `8`, again a rational
nonsquare.  The residual `K₃,₃` contributes one visible `-3` direction, so
this parity forces another such direction elsewhere in the defect graph. -/
theorem degreeSix_thirtyFour_negThree_defectEigenspace_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hregD : ∀ x, (secondOrderDefectGraph G).degree x = 3) :
    Even (Module.finrank ℚ
      (defectEigenspace
        ((secondOrderDefectGraph G).adjMatrix ℚ) (-3 : ℚ))) := by
  let A := G.adjMatrix ℚ
  let D := (secondOrderDefectGraph G).adjMatrix ℚ
  let hcomm : A * D = D * A :=
    adjMatrix_comm_secondOrderDefect_of_regular_rat G hfree hreg
  have hsq :
      defectEigenspaceRestrict A hcomm (-3 : ℚ) *
          defectEigenspaceRestrict A hcomm (-3 : ℚ) =
        (8 : ℚ) • LinearMap.id := by
    have ht := graph_defectEigenspaceRestrict_sq_of_regular_excess
      G hfree (d := 6) (e := 1) hreg hregD
        (μ := (-3 : ℚ)) (by norm_num)
    norm_num at ht
    simpa [A, D] using ht
  exact LinearMap.even_finrank_of_sq_eq_nonsquare_nat
    (defectEigenspaceRestrict A hcomm (-3 : ℚ)) 8
      (by
        rintro ⟨x, hx⟩
        have hle : x ≤ 8 := Nat.le_of_dvd (by norm_num) ⟨x, hx⟩
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

/-- Joint color/triangle dispatcher for the size-two kernel branch.  Once
the color-sector order is fixed, the edge-mass identity fixes the exact
number of triangular 3-cliques. -/
theorem degreeSix_thirtyFour_adjacent_defect_twins_colorOrder_triangleCount_cases
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
    let t := ((triangularEdgeGraph G).cliqueFinset 3).card
    (s = 0 ∧ t = 34) ∨ (s = 6 ∧ t = 32) ∨
      (s = 9 ∧ t = 31) ∨ (s = 12 ∧ t = 30) ∨
      (s = 15 ∧ t = 29) ∨ (s = 18 ∧ t = 28) ∨
      (s = 21 ∧ t = 27) ∨ (s = 24 ∧ t = 26) ∨
      (s = 27 ∧ t = 25) ∨ (s = 30 ∧ t = 24) := by
  let s := (Finset.univ.filter fun x : V =>
    (triangleFreeEdgeGraph G).degree x = 2).card
  let t := ((triangularEdgeGraph G).cliqueFinset 3).card
  have hcases := degreeSix_thirtyFour_adjacent_defect_twins_colorOrder_cases
    G hfree hreg hcard habD htwins
  have hmass := six_mul_triangularCliqueCount_add_two_mul_colorOrder_excessOne
    G hfree (d := 6) (by norm_num) hreg (by omega)
  have hmass' : 6 * t + 2 * s = 34 * 6 := by
    simpa [s, t, hcard] using hmass
  dsimp only
  rcases hcases with hs | hs | hs | hs | hs | hs | hs | hs | hs | hs <;>
    subst s <;> omega

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

/-- The six cross-matching edges between the twin neighborhoods have six
distinct triangle witnesses, all outside both neighborhoods and distinct
from the twins.  The witnesses are indexed by the six-element subtype
`N_G(a)`, making the injection explicit for later residual counting. -/
theorem degreeSix_thirtyFour_adjacent_defect_twins_exists_injective_crossTriangleWitnesses
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
        (secondOrderDefectGraph G).Adj b v))
    (hzero : (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card = 0) :
    ∃ (m r : {p // p ∈ G.neighborFinset a} → V),
      Function.Injective m ∧ Function.Injective r ∧
      ∀ p,
        m p ∈ G.neighborFinset b ∧ G.Adj p (m p) ∧
        G.Adj p (r p) ∧ G.Adj (m p) (r p) ∧
        r p ∉ G.neighborFinset a ∧ r p ∉ G.neighborFinset b ∧
        r p ≠ a ∧ r p ≠ b := by
  classical
  have hgeom :=
    degreeSix_thirtyFour_adjacent_defect_twins_neighbor_matching_of_colorOrder_zero
      G hfree hreg hcard habD htwins hzero
  have hABempty := hgeom.1
  have hmatch := hgeom.2.1
  have habC : (antipodalGraph G).Adj a b := by
    rw [← degreeSix_thirtyFour_secondOrderDefectGraph_eq_antipodalGraph_of_colorOrder_zero
      G hfree hreg hcard hzero]
    exact habD
  have habNotG : ¬ G.Adj a b :=
    ((mem_antipodalNeighbors G a b).mp
      ((antipodalGraph_adj G a b).mp habC)).2.1
  have hexM : ∀ p : {p // p ∈ G.neighborFinset a},
      ∃ q : V, q ∈ G.neighborFinset b ∧ G.Adj p q := by
    intro p
    have hcardOne := hmatch p p.property
    have hnonempty :
        (G.neighborFinset p ∩ G.neighborFinset b).Nonempty :=
      Finset.card_pos.mp (by omega)
    obtain ⟨q, hq⟩ := hnonempty
    have hqParts := Finset.mem_inter.mp hq
    exact ⟨q, hqParts.2, (G.mem_neighborFinset p q).mp hqParts.1⟩
  choose m hmB hmEdge using hexM
  have hmInj : Function.Injective m := by
    intro p q hpq
    by_contra hpqSub
    have hpqVal : (p : V) ≠ (q : V) := by
      intro hpqVal
      exact hpqSub (Subtype.ext hpqVal)
    have haCommon : a ∈ G.neighborFinset p ∩ G.neighborFinset q := by
      apply Finset.mem_inter.mpr
      exact ⟨(G.mem_neighborFinset p a).mpr
          ((G.mem_neighborFinset a p).mp p.property).symm,
        (G.mem_neighborFinset q a).mpr
          ((G.mem_neighborFinset a q).mp q.property).symm⟩
    have hmCommon : m p ∈ G.neighborFinset p ∩ G.neighborFinset q := by
      apply Finset.mem_inter.mpr
      refine ⟨(G.mem_neighborFinset p (m p)).mpr (hmEdge p), ?_⟩
      exact (G.mem_neighborFinset q (m p)).mpr (hpq ▸ hmEdge q)
    have hle := common_le_one_of_not_containsC4 hfree (p : V) (q : V) hpqVal
    have ham : a = m p :=
      (Finset.card_le_one.mp hle) a haCommon (m p) hmCommon
    apply habNotG
    rw [ham]
    exact ((G.mem_neighborFinset b (m p)).mp (hmB p)).symm
  have htriEq := degreeSix_thirtyFour_triangularEdgeGraph_eq_of_colorOrder_zero
    G hfree hreg hcard hzero
  have hexR : ∀ p : {p // p ∈ G.neighborFinset a},
      ∃ z : V, G.Adj p z ∧ G.Adj (m p) z := by
    intro p
    have htri : (triangularEdgeGraph G).Adj p (m p) := by
      rw [htriEq]
      exact hmEdge p
    have hnonzero := (triangularEdgeGraph_adj G p (m p)).mp htri |>.2
    have hnonempty :
        (G.neighborFinset p ∩ G.neighborFinset (m p)).Nonempty :=
      Finset.card_ne_zero.mp hnonzero
    obtain ⟨z, hz⟩ := hnonempty
    have hzParts := Finset.mem_inter.mp hz
    exact ⟨z, (G.mem_neighborFinset p z).mp hzParts.1,
      (G.mem_neighborFinset (m p) z).mp hzParts.2⟩
  choose r hrP hrM using hexR
  have hrInj : Function.Injective r := by
    intro p q hpq
    by_contra hpqSub
    have hpqVal : (p : V) ≠ (q : V) := by
      intro hpqVal
      exact hpqSub (Subtype.ext hpqVal)
    have haCommon : a ∈ G.neighborFinset p ∩ G.neighborFinset q := by
      apply Finset.mem_inter.mpr
      exact ⟨(G.mem_neighborFinset p a).mpr
          ((G.mem_neighborFinset a p).mp p.property).symm,
        (G.mem_neighborFinset q a).mpr
          ((G.mem_neighborFinset a q).mp q.property).symm⟩
    have hrCommon : r p ∈ G.neighborFinset p ∩ G.neighborFinset q := by
      apply Finset.mem_inter.mpr
      refine ⟨(G.mem_neighborFinset p (r p)).mpr (hrP p), ?_⟩
      exact (G.mem_neighborFinset q (r p)).mpr (hpq ▸ hrP q)
    have hle := common_le_one_of_not_containsC4 hfree (p : V) (q : V) hpqVal
    have har : a = r p := (Finset.card_le_one.mp hle) a haCommon (r p) hrCommon
    have hmInA : m p ∈ G.neighborFinset a := by
      apply (G.mem_neighborFinset a (m p)).mpr
      exact har ▸ (hrM p).symm
    have : m p ∈ G.neighborFinset a ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr ⟨hmInA, hmB p⟩
    rw [hABempty] at this
    exact Finset.notMem_empty (m p) this
  refine ⟨m, r, hmInj, hrInj, ?_⟩
  intro p
  have hrNotAset : r p ∉ G.neighborFinset a := by
    intro hrA
    have haCommon : a ∈ G.neighborFinset p ∩ G.neighborFinset (r p) := by
      apply Finset.mem_inter.mpr
      exact ⟨(G.mem_neighborFinset p a).mpr
          ((G.mem_neighborFinset a p).mp p.property).symm,
        (G.mem_neighborFinset (r p) a).mpr
          ((G.mem_neighborFinset a (r p)).mp hrA).symm⟩
    have hmCommon : m p ∈ G.neighborFinset p ∩ G.neighborFinset (r p) := by
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset p (m p)).mpr (hmEdge p),
          (G.mem_neighborFinset (r p) (m p)).mpr (hrM p).symm⟩
    have hpr : (p : V) ≠ r p := G.ne_of_adj (hrP p)
    have hle := common_le_one_of_not_containsC4 hfree (p : V) (r p) hpr
    have ham : a = m p :=
      (Finset.card_le_one.mp hle) a haCommon (m p) hmCommon
    exact habNotG (ham ▸ (G.mem_neighborFinset b (m p)).mp (hmB p) |>.symm)
  have hrNotBset : r p ∉ G.neighborFinset b := by
    intro hrB
    have hbCommon : b ∈ G.neighborFinset (m p) ∩ G.neighborFinset (r p) := by
      apply Finset.mem_inter.mpr
      exact ⟨(G.mem_neighborFinset (m p) b).mpr
          ((G.mem_neighborFinset b (m p)).mp (hmB p)).symm,
        (G.mem_neighborFinset (r p) b).mpr
          ((G.mem_neighborFinset b (r p)).mp hrB).symm⟩
    have hpCommon : (p : V) ∈
        G.neighborFinset (m p) ∩ G.neighborFinset (r p) := by
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset (m p) p).mpr (hmEdge p).symm,
          (G.mem_neighborFinset (r p) p).mpr (hrP p).symm⟩
    have hmr : m p ≠ r p := G.ne_of_adj (hrM p)
    have hle := common_le_one_of_not_containsC4 hfree (m p) (r p) hmr
    have hbp : b = (p : V) :=
      (Finset.card_le_one.mp hle) b hbCommon p hpCommon
    apply habNotG
    rw [hbp]
    exact (G.mem_neighborFinset a p).mp p.property
  have hrNeA : r p ≠ a := by
    intro hra
    have hmInA : m p ∈ G.neighborFinset a := by
      apply (G.mem_neighborFinset a (m p)).mpr
      exact hra ▸ (hrM p).symm
    have hmBoth : m p ∈ G.neighborFinset a ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr ⟨hmInA, hmB p⟩
    rw [hABempty] at hmBoth
    exact Finset.notMem_empty (m p) hmBoth
  have hrNeB : r p ≠ b := by
    intro hrb
    have hpInB : (p : V) ∈ G.neighborFinset b := by
      apply (G.mem_neighborFinset b p).mpr
      exact hrb ▸ (hrP p).symm
    have hpBoth : (p : V) ∈ G.neighborFinset a ∩ G.neighborFinset b :=
      Finset.mem_inter.mpr ⟨p.property, hpInB⟩
    rw [hABempty] at hpBoth
    exact Finset.notMem_empty (p : V) hpBoth
  exact ⟨hmB p, hmEdge p, hrP p, hrM p, hrNotAset, hrNotBset,
    hrNeA, hrNeB⟩

/-- Finset form of the cross-triangle witness injection: six witness
vertices lie outside both twin neighborhoods and avoid the twins. -/
theorem degreeSix_thirtyFour_adjacent_defect_twins_exists_six_crossTriangleWitnesses
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
        (secondOrderDefectGraph G).Adj b v))
    (hzero : (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 2).card = 0) :
    ∃ R : Finset V, R.card = 6 ∧
      Disjoint R (G.neighborFinset a) ∧
      Disjoint R (G.neighborFinset b) ∧ a ∉ R ∧ b ∉ R ∧
      ∀ c : V, (secondOrderDefectGraph G).Adj a c → c ∉ R := by
  classical
  obtain ⟨_m, r, _hmInj, hrInj, hprops⟩ :=
    degreeSix_thirtyFour_adjacent_defect_twins_exists_injective_crossTriangleWitnesses
      G hfree hreg hcard habD htwins hzero
  let R : Finset V := Finset.univ.image r
  have hRcard : R.card = 6 := by
    change (Finset.univ.image r).card = 6
    rw [Finset.card_image_of_injective _ hrInj,
      Finset.card_univ, Fintype.card_coe,
      G.card_neighborFinset_eq_degree, hreg a]
  have hRA : Disjoint R (G.neighborFinset a) := by
    rw [Finset.disjoint_left]
    intro z hzR hzA
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hzR
    exact (hprops p).2.2.2.2.1 hzA
  have hRB : Disjoint R (G.neighborFinset b) := by
    rw [Finset.disjoint_left]
    intro z hzR hzB
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hzR
    exact (hprops p).2.2.2.2.2.1 hzB
  have haR : a ∉ R := by
    intro ha
    obtain ⟨p, _hp, hpa⟩ := Finset.mem_image.mp ha
    exact (hprops p).2.2.2.2.2.2.1 hpa
  have hbR : b ∉ R := by
    intro hb
    obtain ⟨p, _hp, hpb⟩ := Finset.mem_image.mp hb
    exact (hprops p).2.2.2.2.2.2.2 hpb
  have havoid : ∀ c : V, (secondOrderDefectGraph G).Adj a c → c ∉ R := by
    intro c hac hcR
    obtain ⟨p, _hp, hpc⟩ := Finset.mem_image.mp hcR
    have hacNe : a ≠ c := (secondOrderDefectGraph G).ne_of_adj hac
    have hcMem : c ∈ (secondOrderDefectGraph G).neighborFinset a :=
      ((secondOrderDefectGraph G).mem_neighborFinset a c).mpr hac
    have hcommon := card_common_eq_if_secondOrderDefect G hfree a c hacNe
    rw [if_pos hcMem] at hcommon
    have hempty : G.neighborFinset a ∩ G.neighborFinset c = ∅ :=
      Finset.card_eq_zero.mp hcommon
    have hpCommon : (p : V) ∈
        G.neighborFinset a ∩ G.neighborFinset c := by
      apply Finset.mem_inter.mpr
      refine ⟨p.property, ?_⟩
      apply (G.mem_neighborFinset c p).mpr
      exact hpc ▸ (hprops p).2.2.1 |>.symm
    rw [hempty] at hpCommon
    exact Finset.notMem_empty (p : V) hpCommon
  exact ⟨R, hRcard, hRA, hRB, haR, hbR, havoid⟩

/-- A six-element witness set cannot meet both neighborhoods of two
distinct vertices in four or more points: the two intersections live inside
the six-set, while their overlap is a common-neighbor set of order at most
one. -/
theorem sixSet_one_neighbor_intersection_le_three_of_c4Free
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (R : Finset V) (hRcard : R.card = 6)
    {x y : V} (hxy : x ≠ y) :
    (R ∩ G.neighborFinset x).card ≤ 3 ∨
      (R ∩ G.neighborFinset y).card ≤ 3 := by
  let X := R ∩ G.neighborFinset x
  let Y := R ∩ G.neighborFinset y
  change X.card ≤ 3 ∨ Y.card ≤ 3
  have hUnionSub : X ∪ Y ⊆ R := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzX | hzY
    · exact (Finset.mem_inter.mp hzX).1
    · exact (Finset.mem_inter.mp hzY).1
  have hUnion : (X ∪ Y).card ≤ 6 := by
    rw [← hRcard]
    exact Finset.card_le_card hUnionSub
  have hInterSub : X ∩ Y ⊆
      G.neighborFinset x ∩ G.neighborFinset y := by
    intro z hz
    have hzParts := Finset.mem_inter.mp hz
    exact Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hzParts.1).2,
        (Finset.mem_inter.mp hzParts.2).2⟩
  have hInter : (X ∩ Y).card ≤ 1 :=
    (Finset.card_le_card hInterSub).trans
      (common_le_one_of_not_containsC4 hfree x y hxy)
  have hie := Finset.card_union_add_card_inter X Y
  by_contra hnot
  push Not at hnot
  omega

/-- Degree-six complement form: at least one of the two neighborhoods has
three vertices outside the six-set. -/
theorem sixSet_one_neighbor_sdiff_three_le_of_c4Free_degreeSix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ v, G.degree v = 6)
    (R : Finset V) (hRcard : R.card = 6)
    {x y : V} (hxy : x ≠ y) :
    3 ≤ (G.neighborFinset x \ R).card ∨
      3 ≤ (G.neighborFinset y \ R).card := by
  have hsmall := sixSet_one_neighbor_intersection_le_three_of_c4Free
    G hfree R hRcard hxy
  have hxpart := Finset.card_sdiff_add_card_inter
    (G.neighborFinset x) R
  have hypart := Finset.card_sdiff_add_card_inter
    (G.neighborFinset y) R
  rw [G.card_neighborFinset_eq_degree, hreg x] at hxpart
  rw [G.card_neighborFinset_eq_degree, hreg y] at hypart
  rcases hsmall with hx | hy
  · left
    have hx' : (G.neighborFinset x ∩ R).card ≤ 3 := by
      simpa [Finset.inter_comm] using hx
    omega
  · right
    have hy' : (G.neighborFinset y ∩ R).card ≤ 3 := by
      simpa [Finset.inter_comm] using hy
    omega

/-- Applied to the six cross-triangle witnesses, at least one of the two
common defect neighbors sees at most three witnesses. -/
theorem degreeSix_thirtyFour_adjacent_defect_twins_exists_six_crossTriangleWitnesses_one_common_inter_le_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V} (habD : (secondOrderDefectGraph G).Adj a b)
    (htwins : ∀ v, v ≠ a → v ≠ b →
      ((secondOrderDefectGraph G).Adj a v ↔
        (secondOrderDefectGraph G).Adj b v))
    (haxD : (secondOrderDefectGraph G).Adj a x)
    (hayD : (secondOrderDefectGraph G).Adj a y)
    (hxy : x ≠ y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    ∃ R : Finset V, R.card = 6 ∧
      Disjoint R (G.neighborFinset a) ∧
      Disjoint R (G.neighborFinset b) ∧
      a ∉ R ∧ b ∉ R ∧ x ∉ R ∧ y ∉ R ∧
      ((R ∩ G.neighborFinset x).card ≤ 3 ∨
        (R ∩ G.neighborFinset y).card ≤ 3) := by
  obtain ⟨R, hRcard, hRA, hRB, haR, hbR, havoid⟩ :=
    degreeSix_thirtyFour_adjacent_defect_twins_exists_six_crossTriangleWitnesses
      G hfree hreg hcard habD htwins hzero
  exact ⟨R, hRcard, hRA, hRB, haR, hbR, havoid x haxD, havoid y hayD,
    sixSet_one_neighbor_intersection_le_three_of_c4Free
      G hfree R hRcard hxy⟩

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

/-- If the two common neighbors of the twin pair are themselves defect
adjacent, the defect diamond closes to a `K₄`; all four original
neighborhoods are then pairwise disjoint and have total order 24. -/
theorem degreeSix_defectKFour_four_neighborhood_union_card_eq_twentyFour
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
    (hxy : (secondOrderDefectGraph G).Adj x y) :
    (G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y).card = 24 := by
  have hdAB := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hab
  have hdAX := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hax
  have hdBX := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hbx
  have hdAY := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hay
  have hdBY := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hby
  have hdXY := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hxy
  have hdABX : Disjoint
      (G.neighborFinset a ∪ G.neighborFinset b) (G.neighborFinset x) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdAX, hdBX⟩
  have hdABY : Disjoint
      (G.neighborFinset a ∪ G.neighborFinset b) (G.neighborFinset y) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdAY, hdBY⟩
  have hdABXY : Disjoint
      (G.neighborFinset a ∪ G.neighborFinset b ∪ G.neighborFinset x)
      (G.neighborFinset y) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdABY, hdXY⟩
  rw [Finset.card_union_of_disjoint hdABXY,
    Finset.card_union_of_disjoint hdABX,
    Finset.card_union_of_disjoint hdAB,
    G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree,
    G.card_neighborFinset_eq_degree, G.card_neighborFinset_eq_degree,
    hreg a, hreg b, hreg x, hreg y]

/-- Three displayed distinct neighbors exhaust the neighborhood of a
degree-three vertex. -/
theorem neighborFinset_eq_triple_of_degree_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    {u p q r : V} (hdeg : H.degree u = 3)
    (hup : H.Adj u p) (huq : H.Adj u q) (hur : H.Adj u r)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    H.neighborFinset u = {p, q, r} := by
  have hsub : ({p, q, r} : Finset V) ⊆ H.neighborFinset u := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
      H.mem_neighborFinset]
    exact ⟨hup, huq, hur⟩
  have htriple : ({p, q, r} : Finset V).card = 3 := by
    simp [hpq, hpr, hqr]
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [htriple, H.card_neighborFinset_eq_degree, hdeg]

/-- A cubic defect `K₄` is an isolated defect component: each center's
defect neighborhood is exactly the other three centers. -/
theorem cubic_defectKFour_neighborFinsets
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hregD : ∀ v, D.degree v = 3)
    {a b x y : V}
    (hab : D.Adj a b) (hax : D.Adj a x) (hbx : D.Adj b x)
    (hay : D.Adj a y) (hby : D.Adj b y) (hxy : D.Adj x y) :
    D.neighborFinset a = {b, x, y} ∧
      D.neighborFinset b = {a, x, y} ∧
      D.neighborFinset x = {a, b, y} ∧
      D.neighborFinset y = {a, b, x} := by
  have habNe := D.ne_of_adj hab
  have haxNe := D.ne_of_adj hax
  have hayNe := D.ne_of_adj hay
  have hbxNe := D.ne_of_adj hbx
  have hbyNe := D.ne_of_adj hby
  have hxyNe := D.ne_of_adj hxy
  refine ⟨neighborFinset_eq_triple_of_degree_three D (hregD a)
      hab hax hay hbxNe hbyNe hxyNe,
    neighborFinset_eq_triple_of_degree_three D (hregD b)
      hab.symm hbx hby haxNe hayNe hxyNe,
    neighborFinset_eq_triple_of_degree_three D (hregD x)
      hax.symm hbx.symm hxy habNe hayNe hbyNe,
    neighborFinset_eq_triple_of_degree_three D (hregD y)
      hay.symm hby.symm hxy.symm habNe haxNe hbxNe⟩

/-- Every edge of a cubic `K₄` joins adjacent twins: away from its two
endpoints, the endpoint defect-adjacency predicates agree. -/
theorem cubic_defectKFour_adjacent_twins
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hregD : ∀ v, D.degree v = 3)
    {a b x y : V}
    (hab : D.Adj a b) (hax : D.Adj a x) (hbx : D.Adj b x)
    (hay : D.Adj a y) (hby : D.Adj b y) (hxy : D.Adj x y) :
    ∀ v, v ≠ a → v ≠ b → (D.Adj a v ↔ D.Adj b v) := by
  rcases cubic_defectKFour_neighborFinsets D hregD
      hab hax hbx hay hby hxy with ⟨hKa, hKb, _, _⟩
  intro v hva hvb
  rw [← D.mem_neighborFinset, ← D.mem_neighborFinset, hKa, hKb]
  simp [hva, hvb]

/-- Entrywise commutation propagates zero contact with an isolated defect
block across a defect edge.  If all defect neighbors of `u` lie in `Q` and
`v` has no original-graph neighbor in `Q`, then every defect neighbor `w`
of `v` is nonadjacent to `u` in the original graph. -/
theorem no_adj_of_defect_adj_of_zero_block_contact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d)
    (Q : Finset V) {u v w : V}
    (huD : (secondOrderDefectGraph G).neighborFinset u ⊆ Q)
    (hvQ : ∀ z ∈ Q, ¬ G.Adj z v)
    (hvwD : (secondOrderDefectGraph G).Adj v w) :
    ¬ G.Adj u w := by
  have hcomm := card_filter_adj_secondOrderDefect_comm_of_regular
    G hfree hreg u v
  have hright : (((secondOrderDefectGraph G).neighborFinset u).filter
      (fun z => G.Adj z v)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro z hzD
    exact hvQ z (huD hzD)
  rw [hright] at hcomm
  intro huw
  have hwMem : w ∈ (((secondOrderDefectGraph G).neighborFinset v).filter
      (fun z => G.Adj u z)) := by
    apply Finset.mem_filter.mpr
    exact ⟨((secondOrderDefectGraph G).mem_neighborFinset v w).mpr hvwD, huw⟩
  have hpos : 0 < ((((secondOrderDefectGraph G).neighborFinset v).filter
      (fun z => G.Adj u z)).card) := Finset.card_pos.mpr ⟨w, hwMem⟩
  omega

/-- Entrywise commutation also gives the exact positive propagation count:
if an isolated defect neighborhood is the triple `{u,r,s}` and `v` is
adjacent in the original graph to exactly `u` from that triple, then exactly
one defect neighbor of `v` is adjacent to the center `q`. -/
theorem card_defectNeighbors_adj_center_eq_one_of_unique_triple_contact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d)
    {q u r s v : V}
    (hqD : (secondOrderDefectGraph G).neighborFinset q = {u, r, s})
    (huv : G.Adj u v) (hrv : ¬ G.Adj r v) (hsv : ¬ G.Adj s v) :
    (((secondOrderDefectGraph G).neighborFinset v).filter
      (fun z => G.Adj q z)).card = 1 := by
  have hcomm := card_filter_adj_secondOrderDefect_comm_of_regular
    G hfree hreg q v
  have hfilter : (((secondOrderDefectGraph G).neighborFinset q).filter
      (fun z => G.Adj z v)) = {u} := by
    ext z
    rw [hqD]
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzu | hzr | hzs, hzv⟩
      · exact hzu
      · exact (hrv (hzr ▸ hzv)).elim
      · exact (hsv (hzs ▸ hzv)).elim
    · intro hzu
      exact ⟨Or.inl hzu, hzu ▸ huv⟩
  rw [hfilter, Finset.card_singleton] at hcomm
  exact hcomm

/-- Entrywise commutation transports a unique contact with a defect-closed
set across a defect edge inside that set.  If `r` is the unique vertex of
`R` adjacent to `p`, the defect neighborhood of `s` stays in `R`, and
`s—r` is a defect edge, then exactly one defect neighbor of `p` is adjacent
to `s`.  In the residual `K₃,₃` branch this is the cover-label transition
rule from a residual label to each label on the opposite side. -/
theorem card_defectNeighbors_adj_eq_one_of_unique_closed_contact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d)
    (R : Finset V) {p r s : V}
    (hDs : (secondOrderDefectGraph G).neighborFinset s ⊆ R)
    (hpr : G.Adj p r)
    (hunique : ∀ z ∈ R, G.Adj p z → z = r)
    (hsrD : (secondOrderDefectGraph G).Adj s r) :
    (((secondOrderDefectGraph G).neighborFinset p).filter
      (fun z => G.Adj z s)).card = 1 := by
  have hcomm := card_filter_adj_secondOrderDefect_comm_of_regular
    G hfree hreg p s
  have hfilter : (((secondOrderDefectGraph G).neighborFinset s).filter
      (fun z => G.Adj p z)) = {r} := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hzD, hpz⟩
      exact hunique z (hDs hzD) hpz
    · intro hzr
      subst z
      exact ⟨((secondOrderDefectGraph G).mem_neighborFinset s r).mpr hsrD,
        hpr⟩
  rw [hfilter, Finset.card_singleton] at hcomm
  exact hcomm.symm

/-- If `p` has unique contact `r` with `R`, and `r—s` is an original edge,
then `p` and `s` have no common neighbor outside `R`: their unique possible
common neighbor is already `r`. -/
theorem card_common_outside_eq_zero_of_unique_contact_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (R : Finset V) {p r s : V}
    (hps : p ≠ s)
    (hpr : G.Adj p r) (hrs : G.Adj r s)
    (hrR : r ∈ R) :
    ((G.neighborFinset p ∩ G.neighborFinset s) ∩
      (Finset.univ \ R)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  ext z
  constructor
  · intro hz
    rcases Finset.mem_inter.mp hz with ⟨hzCommon, hzOut⟩
    rcases Finset.mem_inter.mp hzCommon with ⟨hpz, hsz⟩
    have hrCommon : r ∈ G.neighborFinset p ∩ G.neighborFinset s := by
      exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset p r).mpr hpr,
        (G.mem_neighborFinset s r).mpr hrs.symm⟩
    have hzEq : z = r :=
      Finset.card_le_one.mp
        (common_le_one_of_not_containsC4 hfree p s hps) z
          (Finset.mem_inter.mpr ⟨hpz, hsz⟩) r hrCommon
    exact ((Finset.mem_sdiff.mp hzOut).2 (hzEq ▸ hrR)).elim
  · simp

/-- Opposite residual labels force exactly one common neighbor outside the
closed residual.  Here `s` has no defect edge leaving `R`, `p` lies outside
`R`, and the unique residual contact `r` of `p` is defect-adjacent (hence
not originally adjacent) to `s`. -/
theorem card_common_outside_eq_one_of_unique_contact_defectAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (R : Finset V) {p r s : V}
    (hpOut : p ∉ R) (hsR : s ∈ R)
    (hDs : (secondOrderDefectGraph G).neighborFinset s ⊆ R)
    (hpr : G.Adj p r) (hrR : r ∈ R)
    (hunique : ∀ z ∈ R, G.Adj p z → z = r)
    (hrsD : (secondOrderDefectGraph G).Adj r s)
    (hrsNotG : ¬ G.Adj r s) :
    ((G.neighborFinset p ∩ G.neighborFinset s) ∩
      (Finset.univ \ R)).card = 1 := by
  have _hrContact : r ∈ G.neighborFinset p ∩ R :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p r).mpr hpr, hrR⟩
  have _hrsNe : r ≠ s := (secondOrderDefectGraph G).ne_of_adj hrsD
  have hps : p ≠ s := by
    intro hps
    exact hpOut (hps ▸ hsR)
  have hpsNotD : p ∉ (secondOrderDefectGraph G).neighborFinset s := by
    intro hpsD
    exact hpOut (hDs hpsD)
  have hsNotD : s ∉ (secondOrderDefectGraph G).neighborFinset p := by
    intro hsD
    have hpsAdj : (secondOrderDefectGraph G).Adj p s := by simpa using hsD
    exact hpsNotD (by simpa using hpsAdj.symm)
  have hcommon : (G.neighborFinset p ∩ G.neighborFinset s).card = 1 := by
    have hc := card_common_eq_if_secondOrderDefect G hfree p s hps
    rw [if_neg hsNotD] at hc
    exact hc
  have hsub : G.neighborFinset p ∩ G.neighborFinset s ⊆
      Finset.univ \ R := by
    intro z hz
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ z, ?_⟩
    intro hzR
    have hpz : G.Adj p z :=
      (G.mem_neighborFinset p z).mp (Finset.mem_inter.mp hz).1
    have hzr : z = r := hunique z hzR hpz
    have hsz : G.Adj s z :=
      (G.mem_neighborFinset s z).mp (Finset.mem_inter.mp hz).2
    exact hrsNotG (hzr ▸ hsz.symm)
  rw [Finset.inter_eq_left.mpr hsub, hcommon]

/-- Around a closed cubic defect `K₄`, every vertex in one center's
original neighborhood has exactly one defect neighbor in each of the other
three center-neighborhood blocks. -/
theorem defectKFour_neighbor_block_three_exact_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y v : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hv : v ∈ G.neighborFinset a) :
    ((((secondOrderDefectGraph G).neighborFinset v).filter
        (fun z => G.Adj b z)).card = 1) ∧
      ((((secondOrderDefectGraph G).neighborFinset v).filter
        (fun z => G.Adj x z)).card = 1) ∧
      (((secondOrderDefectGraph G).neighborFinset v).filter
        (fun z => G.Adj y z)).card = 1 := by
  let D := secondOrderDefectGraph G
  rcases cubic_defectKFour_neighborFinsets D hregD
      hab hax hbx hay hby hxy with ⟨hKa, hKb, hKx, hKy⟩
  have hav : G.Adj a v := (G.mem_neighborFinset a v).mp hv
  have hbNot : ¬ G.Adj b v := by
    intro hbv
    exact Finset.disjoint_left.mp
      (neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hab)
      hv ((G.mem_neighborFinset b v).mpr hbv)
  have hxNot : ¬ G.Adj x v := by
    intro hxv
    exact Finset.disjoint_left.mp
      (neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hax)
      hv ((G.mem_neighborFinset x v).mpr hxv)
  have hyNot : ¬ G.Adj y v := by
    intro hyv
    exact Finset.disjoint_left.mp
      (neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hay)
      hv ((G.mem_neighborFinset y v).mpr hyv)
  exact ⟨
    card_defectNeighbors_adj_center_eq_one_of_unique_triple_contact
      G hfree hreg hKb hav hxNot hyNot,
    card_defectNeighbors_adj_center_eq_one_of_unique_triple_contact
      G hfree hreg hKx hav hbNot hyNot,
    card_defectNeighbors_adj_center_eq_one_of_unique_triple_contact
      G hfree hreg hKy hav hbNot hxNot⟩

/-- In the pure antipodal branch, each pair of center-neighborhood blocks
of a closed cubic defect `K₄` is also joined by an original-graph perfect
matching.  This statement records the pair indexed by `a,b`; permutations
of the four centers give the other five pairs. -/
theorem degreeSix_thirtyFour_defectKFour_original_neighbor_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    G.neighborFinset a ∩ G.neighborFinset b = ∅ ∧
      (∀ p ∈ G.neighborFinset a,
        (G.neighborFinset p ∩ G.neighborFinset b).card = 1) ∧
      ∀ q ∈ G.neighborFinset b,
        (G.neighborFinset q ∩ G.neighborFinset a).card = 1 := by
  apply degreeSix_thirtyFour_adjacent_defect_twins_neighbor_matching_of_colorOrder_zero
    G hfree hreg hcard hab
  · exact cubic_defectKFour_adjacent_twins (secondOrderDefectGraph G)
      hregD hab hax hbx hay hby hxy
  · exact hzero

/-- In the pure antipodal branch, the graph induced by the original graph
on each center's six-element neighborhood is one-regular: every incident
edge through the center has its unique triangle partner in that block. -/
theorem degreeSix_thirtyFour_center_neighborFinset_internal_degree_one_of_colorOrder_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0)
    (a : V) :
    ∀ p ∈ G.neighborFinset a,
      (G.neighborFinset p ∩ G.neighborFinset a).card = 1 := by
  have hDeq :=
    degreeSix_thirtyFour_secondOrderDefectGraph_eq_antipodalGraph_of_colorOrder_zero
      G hfree hreg hcard hzero
  intro p hp
  have hap : G.Adj a p := (G.mem_neighborFinset a p).mp hp
  have hapNe : a ≠ p := G.ne_of_adj hap
  have hnotD : ¬ (secondOrderDefectGraph G).Adj a p := by
    rw [hDeq]
    intro hapC
    exact ((mem_antipodalNeighbors G a p).mp
      ((antipodalGraph_adj G a p).mp hapC)).2.1 hap
  have hnotMem : p ∉ (secondOrderDefectGraph G).neighborFinset a := by
    simpa using hnotD
  have hone := card_common_eq_if_secondOrderDefect G hfree a p hapNe
  rw [if_neg hnotMem] at hone
  simpa [Finset.inter_comm] using hone

/-- Exact original-graph degree ledger inside the four six-element blocks:
a vertex of `N(a)` has one neighbor in its own block and one in each of the
other three blocks. -/
theorem degreeSix_thirtyFour_defectKFour_centerBlock_four_G_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y v : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0)
    (hv : v ∈ G.neighborFinset a) :
    (G.neighborFinset v ∩ G.neighborFinset a).card = 1 ∧
      (G.neighborFinset v ∩ G.neighborFinset b).card = 1 ∧
      (G.neighborFinset v ∩ G.neighborFinset x).card = 1 ∧
      (G.neighborFinset v ∩ G.neighborFinset y).card = 1 := by
  have hself :=
    degreeSix_thirtyFour_center_neighborFinset_internal_degree_one_of_colorOrder_zero
      G hfree hreg hcard hzero a v hv
  have habMatch :=
    degreeSix_thirtyFour_defectKFour_original_neighbor_matching
      G hfree hreg hcard hregD hab hax hbx hay hby hxy hzero
  have haxMatch :=
    degreeSix_thirtyFour_defectKFour_original_neighbor_matching
      G hfree hreg hcard hregD hax hab hbx.symm hay hxy hby hzero
  have hayMatch :=
    degreeSix_thirtyFour_defectKFour_original_neighbor_matching
      G hfree hreg hcard hregD hay hab hby.symm hax hxy.symm hbx hzero
  exact ⟨hself, habMatch.2.1 v hv, haxMatch.2.1 v hv,
    hayMatch.2.1 v hv⟩

/-- The preceding four one-neighbor contributions are disjoint, so exactly
four neighbors of a block vertex lie in the union of the four six-blocks. -/
theorem degreeSix_thirtyFour_defectKFour_centerBlock_union_inter_card_eq_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y v : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0)
    (hv : v ∈ G.neighborFinset a) :
    (G.neighborFinset v ∩ (G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y)).card = 4 := by
  have hc := degreeSix_thirtyFour_defectKFour_centerBlock_four_G_counts
    G hfree hreg hcard hregD hab hax hbx hay hby hxy hzero hv
  rcases hc with ⟨hA, hB, hX, hY⟩
  have hdAB := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hab
  have hdAX := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hax
  have hdBX := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hbx
  have hdAY := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hay
  have hdBY := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hby
  have hdXY := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hxy
  have hdABX : Disjoint
      (G.neighborFinset a ∪ G.neighborFinset b) (G.neighborFinset x) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdAX, hdBX⟩
  have hdABXY : Disjoint
      (G.neighborFinset a ∪ G.neighborFinset b ∪ G.neighborFinset x)
      (G.neighborFinset y) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨hdAY, hdBY⟩, hdXY⟩
  have hcardInterUnion (P Q : Finset V) (hd : Disjoint P Q) :
      (G.neighborFinset v ∩ (P ∪ Q)).card =
        (G.neighborFinset v ∩ P).card +
          (G.neighborFinset v ∩ Q).card := by
    rw [Finset.inter_union_distrib_left]
    apply Finset.card_union_of_disjoint
    exact hd.mono Finset.inter_subset_right Finset.inter_subset_right
  calc
    (G.neighborFinset v ∩ (G.neighborFinset a ∪ G.neighborFinset b ∪
        G.neighborFinset x ∪ G.neighborFinset y)).card =
      (G.neighborFinset v ∩ (G.neighborFinset a ∪ G.neighborFinset b ∪
        G.neighborFinset x)).card +
      (G.neighborFinset v ∩ G.neighborFinset y).card :=
        hcardInterUnion _ _ hdABXY
    _ = ((G.neighborFinset v ∩ (G.neighborFinset a ∪
        G.neighborFinset b)).card +
      (G.neighborFinset v ∩ G.neighborFinset x).card) +
      (G.neighborFinset v ∩ G.neighborFinset y).card := by
        rw [hcardInterUnion _ _ hdABX]
    _ = (((G.neighborFinset v ∩ G.neighborFinset a).card +
        (G.neighborFinset v ∩ G.neighborFinset b).card) +
      (G.neighborFinset v ∩ G.neighborFinset x).card) +
      (G.neighborFinset v ∩ G.neighborFinset y).card := by
        rw [hcardInterUnion _ _ hdAB]
    _ = 4 := by omega

/-- A vertex in `N(a)` meets the four defect-`K₄` centers themselves only
at `a`. -/
theorem defectKFour_centerBlock_center_inter_eq_singleton
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {a b x y v : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hv : v ∈ G.neighborFinset a) :
    G.neighborFinset v ∩ ({a, b, x, y} : Finset V) = {a} := by
  have hav : G.Adj a v := (G.mem_neighborFinset a v).mp hv
  have hbNot : ¬ G.Adj b v := by
    intro hbv
    exact Finset.disjoint_left.mp
      (neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hab)
      hv ((G.mem_neighborFinset b v).mpr hbv)
  have hxNot : ¬ G.Adj x v := by
    intro hxv
    exact Finset.disjoint_left.mp
      (neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hax)
      hv ((G.mem_neighborFinset x v).mpr hxv)
  have hyNot : ¬ G.Adj y v := by
    intro hyv
    exact Finset.disjoint_left.mp
      (neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hay)
      hv ((G.mem_neighborFinset y v).mpr hyv)
  ext z
  simp only [Finset.mem_inter, G.mem_neighborFinset, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hzv, hza | hzb | hzx | hzy⟩
    · exact hza
    · exact (hbNot (hzb ▸ hzv.symm)).elim
    · exact (hxNot (hzx ▸ hzv.symm)).elim
    · exact (hyNot (hzy ▸ hzv.symm)).elim
  · intro hza
    exact ⟨hza ▸ hav.symm, Or.inl hza⟩

/-- Adding the unique incident center to the four block contributions, a
vertex in one six-block has exactly five neighbors in the full 28-vertex
centered footprint. -/
theorem degreeSix_thirtyFour_defectKFour_centered_footprint_inter_card_eq_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y v : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0)
    (hv : v ∈ G.neighborFinset a) :
    (G.neighborFinset v ∩ (G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y ∪ {a, b, x, y})).card = 5 := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let Q : Finset V := {a, b, x, y}
  have hDeq :=
    degreeSix_thirtyFour_secondOrderDefectGraph_eq_antipodalGraph_of_colorOrder_zero
      G hfree hreg hcard hzero
  have hnotG_of_D : ∀ {u w : V},
      (secondOrderDefectGraph G).Adj u w → ¬ G.Adj u w := by
    intro u w huw
    rw [hDeq] at huw
    exact ((mem_antipodalNeighbors G u w).mp
      ((antipodalGraph_adj G u w).mp huw)).2.1
  have hdBQ : Disjoint B Q := by
    rw [Finset.disjoint_left]
    intro z hzB hzQ
    simp only [B, Finset.mem_union, G.mem_neighborFinset] at hzB
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hzQ
    have haa : ¬ G.Adj a a := G.loopless.irrefl a
    have hbb : ¬ G.Adj b b := G.loopless.irrefl b
    have hxx : ¬ G.Adj x x := G.loopless.irrefl x
    have hyy : ¬ G.Adj y y := G.loopless.irrefl y
    have habG := hnotG_of_D hab
    have haxG := hnotG_of_D hax
    have hbxG := hnotG_of_D hbx
    have hayG := hnotG_of_D hay
    have hbyG := hnotG_of_D hby
    have hxyG := hnotG_of_D hxy
    have hbaG : ¬ G.Adj b a := fun h => habG h.symm
    have hxaG : ¬ G.Adj x a := fun h => haxG h.symm
    have hxbG : ¬ G.Adj x b := fun h => hbxG h.symm
    have hyaG : ¬ G.Adj y a := fun h => hayG h.symm
    have hybG : ¬ G.Adj y b := fun h => hbyG h.symm
    have hyxG : ¬ G.Adj y x := fun h => hxyG h.symm
    aesop
  have hBinter : (G.neighborFinset v ∩ B).card = 4 := by
    simpa [B] using
      degreeSix_thirtyFour_defectKFour_centerBlock_union_inter_card_eq_four
        G hfree hreg hcard hregD hab hax hbx hay hby hxy hzero hv
  have hQinter : G.neighborFinset v ∩ Q = {a} := by
    simpa [Q] using defectKFour_centerBlock_center_inter_eq_singleton
      G hfree hab hax hay hv
  change (G.neighborFinset v ∩ (B ∪ Q)).card = 5
  rw [Finset.inter_union_distrib_left,
    Finset.card_union_of_disjoint
      (hdBQ.mono Finset.inter_subset_right Finset.inter_subset_right),
    hBinter, hQinter, Finset.card_singleton]

/-- Consequently every vertex in a center-neighborhood block has exactly
one original-graph neighbor in the complementary six-vertex residual. -/
theorem degreeSix_thirtyFour_defectKFour_centerBlock_residual_inter_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y v : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0)
    (hv : v ∈ G.neighborFinset a) :
    (G.neighborFinset v ∩ (Finset.univ \ (
      G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y ∪ {a, b, x, y}))).card = 1 := by
  let U := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y ∪ {a, b, x, y}
  have hUinter : (G.neighborFinset v ∩ U).card = 5 := by
    simpa [U] using
      degreeSix_thirtyFour_defectKFour_centered_footprint_inter_card_eq_five
        G hfree hreg hcard hregD hab hax hbx hay hby hxy hzero hv
  have hdiff : G.neighborFinset v ∩ (Finset.univ \ U) =
      G.neighborFinset v \ U := by
    ext z
    simp
  have hie := Finset.card_sdiff_add_card_inter (G.neighborFinset v) U
  rw [G.card_neighborFinset_eq_degree, hreg v, hUinter] at hie
  change (G.neighborFinset v ∩ (Finset.univ \ U)).card = 1
  rw [hdiff]
  omega

/-- Permutation-invariant form: every vertex in the union of the four
center-neighborhood blocks has exactly one neighbor in the residual six-set. -/
theorem degreeSix_thirtyFour_defectKFour_blockVertex_residual_inter_card_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y v : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0)
    (hv : v ∈ G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y) :
    (G.neighborFinset v ∩ (Finset.univ \ (
      G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y ∪ {a, b, x, y}))).card = 1 := by
  simp only [Finset.mem_union] at hv
  rcases hv with ((hva | hvb) | hvx) | hvy
  · exact degreeSix_thirtyFour_defectKFour_centerBlock_residual_inter_card_eq_one
      G hfree hreg hcard hregD hab hax hbx hay hby hxy hzero hva
  · have ht :=
      degreeSix_thirtyFour_defectKFour_centerBlock_residual_inter_card_eq_one
        G hfree hreg hcard hregD hab.symm hbx hax hby hay hxy hzero hvb
    have hQ : ({b, a, x, y} : Finset V) = {a, b, x, y} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hQ] at ht
    simpa only [Finset.union_comm, Finset.union_left_comm,
      Finset.union_assoc] using ht
  · have ht :=
      degreeSix_thirtyFour_defectKFour_centerBlock_residual_inter_card_eq_one
        G hfree hreg hcard hregD hax.symm hbx.symm hab hxy hay hby hzero hvx
    have hQ : ({x, a, b, y} : Finset V) = {a, b, x, y} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hQ] at ht
    simpa only [Finset.union_comm, Finset.union_left_comm,
      Finset.union_assoc] using ht
  · have ht :=
      degreeSix_thirtyFour_defectKFour_centerBlock_residual_inter_card_eq_one
        G hfree hreg hcard hregD hay.symm hby.symm hab hxy.symm hax hbx hzero hvy
    have hQ : ({y, a, b, x} : Finset V) = {a, b, x, y} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hQ] at ht
    simpa only [Finset.union_comm, Finset.union_left_comm,
      Finset.union_assoc] using ht

/-- In a six-set closed under a cubic antipodal defect graph, a vertex has
at most two original-graph neighbors inside the set: its three defect
neighbors and itself already exclude four of the six positions. -/
theorem internal_G_neighbor_card_le_two_of_closed_cubic_antipodal_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    (hDeq : secondOrderDefectGraph G = antipodalGraph G)
    (R : Finset V) (hRcard : R.card = 6)
    {v : V} (hv : v ∈ R)
    (hDsub : (secondOrderDefectGraph G).neighborFinset v ⊆ R)
    (hDcard : ((secondOrderDefectGraph G).neighborFinset v).card = 3) :
    (G.neighborFinset v ∩ R).card ≤ 2 := by
  let A := G.neighborFinset v ∩ R
  let Dv := (secondOrderDefectGraph G).neighborFinset v
  have hdAD : Disjoint A Dv := by
    rw [Finset.disjoint_left]
    intro z hzA hzD
    have hvzG : G.Adj v z :=
      (G.mem_neighborFinset v z).mp (Finset.mem_inter.mp hzA).1
    have hvzD : (secondOrderDefectGraph G).Adj v z :=
      ((secondOrderDefectGraph G).mem_neighborFinset v z).mp hzD
    rw [hDeq] at hvzD
    exact ((mem_antipodalNeighbors G v z).mp
      ((antipodalGraph_adj G v z).mp hvzD)).2.1 hvzG
  have hsub : A ∪ Dv ⊆ R.erase v := by
    intro z hz
    apply Finset.mem_erase.mpr
    rcases Finset.mem_union.mp hz with hzA | hzD
    · have hzParts := Finset.mem_inter.mp hzA
      exact ⟨fun hzv => G.loopless.irrefl v (hzv ▸
        (G.mem_neighborFinset v z).mp hzParts.1), hzParts.2⟩
    · have hvzD : (secondOrderDefectGraph G).Adj v z :=
        ((secondOrderDefectGraph G).mem_neighborFinset v z).mp hzD
      exact ⟨fun hzv => (secondOrderDefectGraph G).loopless.irrefl v
        (hzv ▸ hvzD), hDsub hzD⟩
  have herase : (R.erase v).card = 5 := by
    rw [Finset.card_erase_of_mem hv, hRcard]
  have hunion : (A ∪ Dv).card = A.card + Dv.card :=
    Finset.card_union_of_disjoint hdAD
  have hle := Finset.card_le_card hsub
  dsimp only [A, Dv] at hunion ⊢
  rw [hunion, hDcard, herase] at hle
  omega

/-- Sharp form of the same six-set count: once the internal original degree
is two, the two original neighbors and three defect neighbors partition all
five other residual vertices. -/
theorem internal_G_union_defect_neighbors_eq_erase_of_closed_cubic_antipodal_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    (hDeq : secondOrderDefectGraph G = antipodalGraph G)
    (R : Finset V) (hRcard : R.card = 6)
    {v : V} (hv : v ∈ R)
    (hDsub : (secondOrderDefectGraph G).neighborFinset v ⊆ R)
    (hDcard : ((secondOrderDefectGraph G).neighborFinset v).card = 3)
    (hGcard : (G.neighborFinset v ∩ R).card = 2) :
    (G.neighborFinset v ∩ R) ∪
      (secondOrderDefectGraph G).neighborFinset v = R.erase v := by
  let A := G.neighborFinset v ∩ R
  let Dv := (secondOrderDefectGraph G).neighborFinset v
  have hdAD : Disjoint A Dv := by
    rw [Finset.disjoint_left]
    intro z hzA hzD
    have hvzG : G.Adj v z :=
      (G.mem_neighborFinset v z).mp (Finset.mem_inter.mp hzA).1
    have hvzD : (secondOrderDefectGraph G).Adj v z :=
      ((secondOrderDefectGraph G).mem_neighborFinset v z).mp hzD
    rw [hDeq] at hvzD
    exact ((mem_antipodalNeighbors G v z).mp
      ((antipodalGraph_adj G v z).mp hvzD)).2.1 hvzG
  have hsub : A ∪ Dv ⊆ R.erase v := by
    intro z hz
    apply Finset.mem_erase.mpr
    rcases Finset.mem_union.mp hz with hzA | hzD
    · have hzParts := Finset.mem_inter.mp hzA
      exact ⟨fun hzv => G.loopless.irrefl v (hzv ▸
        (G.mem_neighborFinset v z).mp hzParts.1), hzParts.2⟩
    · have hvzD : (secondOrderDefectGraph G).Adj v z :=
        ((secondOrderDefectGraph G).mem_neighborFinset v z).mp hzD
      exact ⟨fun hzv => (secondOrderDefectGraph G).loopless.irrefl v
        (hzv ▸ hvzD), hDsub hzD⟩
  have herase : (R.erase v).card = 5 := by
    rw [Finset.card_erase_of_mem hv, hRcard]
  have hunion : (A ∪ Dv).card = A.card + Dv.card :=
    Finset.card_union_of_disjoint hdAD
  change A ∪ Dv = R.erase v
  apply Finset.eq_of_subset_of_card_le hsub
  rw [herase, hunion]
  dsimp only [A, Dv]
  omega

/-- Symmetric cut-incidence double count for two finite vertex sets. -/
theorem sum_card_neighbor_inter_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V) :
    (∑ a ∈ A, (G.neighborFinset a ∩ B).card) =
      ∑ b ∈ B, (G.neighborFinset b ∩ A).card := by
  classical
  rw [← Finset.card_sigma, ← Finset.card_sigma]
  apply Finset.card_bij (fun p _ => ⟨p.2, p.1⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_inter, G.mem_neighborFinset] at hp ⊢
    exact ⟨hp.2.2, hp.2.1.symm, hp.1⟩
  · intro p hp q hq heq
    cases p
    cases q
    cases heq
    rfl
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_inter, G.mem_neighborFinset] at hp
    refine ⟨⟨p.2, p.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨hp.2.2, hp.2.1.symm, hp.1⟩
    · cases p
      rfl

/-- The four six-blocks send exactly 24 original-graph incidences into the
residual six-set, and the symmetric residual-side incidence sum is therefore
also exactly 24. -/
theorem degreeSix_thirtyFour_defectKFour_block_residual_incidence_sum_eq_twentyFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    let R := Finset.univ \ (B ∪ {a, b, x, y})
    (∑ v ∈ B, (G.neighborFinset v ∩ R).card) = 24 ∧
      (∑ r ∈ R, (G.neighborFinset r ∩ B).card) = 24 := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let R := Finset.univ \ (B ∪ {a, b, x, y})
  have hone : ∀ v ∈ B, (G.neighborFinset v ∩ R).card = 1 := by
    intro v hv
    simp only [B, Finset.mem_union] at hv
    rcases hv with ((hva | hvb) | hvx) | hvy
    · simpa only [B, R] using
        degreeSix_thirtyFour_defectKFour_centerBlock_residual_inter_card_eq_one
          G hfree hreg hcard hregD hab hax hbx hay hby hxy hzero hva
    · have ht :=
        degreeSix_thirtyFour_defectKFour_centerBlock_residual_inter_card_eq_one
          G hfree hreg hcard hregD hab.symm hbx hax hby hay hxy hzero hvb
      have hQ : ({b, a, x, y} : Finset V) = {a, b, x, y} := by
        ext z
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hQ] at ht
      simpa only [B, R, Finset.union_comm, Finset.union_left_comm,
        Finset.union_assoc] using ht
    · have ht :=
        degreeSix_thirtyFour_defectKFour_centerBlock_residual_inter_card_eq_one
          G hfree hreg hcard hregD hax.symm hbx.symm hab hxy hay hby hzero hvx
      have hQ : ({x, a, b, y} : Finset V) = {a, b, x, y} := by
        ext z
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hQ] at ht
      simpa only [B, R, Finset.union_comm, Finset.union_left_comm,
        Finset.union_assoc] using ht
    · have ht :=
        degreeSix_thirtyFour_defectKFour_centerBlock_residual_inter_card_eq_one
          G hfree hreg hcard hregD hay.symm hby.symm hab hxy.symm hax hbx hzero hvy
      have hQ : ({y, a, b, x} : Finset V) = {a, b, x, y} := by
        ext z
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hQ] at ht
      simpa only [B, R, Finset.union_comm, Finset.union_left_comm,
        Finset.union_assoc] using ht
  have hBcard : B.card = 24 := by
    simpa [B] using
      degreeSix_defectKFour_four_neighborhood_union_card_eq_twentyFour
        G hfree hreg hab hax hbx hay hby hxy
  have hleft : (∑ v ∈ B, (G.neighborFinset v ∩ R).card) = 24 := by
    calc
      (∑ v ∈ B, (G.neighborFinset v ∩ R).card) = ∑ v ∈ B, 1 := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hone v hv
      _ = 24 := by simp [hBcard]
  refine ⟨hleft, ?_⟩
  rw [← sum_card_neighbor_inter_comm G B R]
  exact hleft

/-- A sharp averaging lemma for the residual incidence count. -/
theorem eq_four_of_mem_of_card_six_of_four_le_of_sum_eq_twentyFour
    {V : Type*} [DecidableEq V] (R : Finset V) (hRcard : R.card = 6)
    (f : V → ℕ) (hlower : ∀ r ∈ R, 4 ≤ f r)
    (hsum : (∑ r ∈ R, f r) = 24) {v : V} (hv : v ∈ R) :
    f v = 4 := by
  have hrest : ∑ r ∈ R.erase v, 4 ≤ ∑ r ∈ R.erase v, f r := by
    apply Finset.sum_le_sum
    intro r hr
    exact hlower r (Finset.mem_of_mem_erase hr)
  have herase : (R.erase v).card = 5 := by
    rw [Finset.card_erase_of_mem hv, hRcard]
  have hdecomp := Finset.sum_erase_add _ f hv
  have hvLower := hlower v hv
  simp [herase] at hrest
  rw [hsum] at hdecomp
  omega

/-- Degree partition across a set `B` and the complement of `B ∪ Q`, when
the vertex has no neighbors in the omitted set `Q`. -/
theorem card_neighbor_inter_add_card_neighbor_inter_compl_union
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (B Q : Finset V) {v : V} (hdeg : G.degree v = 6)
    (hvQ : ∀ q ∈ Q, ¬ G.Adj v q) :
    (G.neighborFinset v ∩ B).card +
      (G.neighborFinset v ∩ (Finset.univ \ (B ∪ Q))).card = 6 := by
  let R := Finset.univ \ (B ∪ Q)
  have hdBR : Disjoint B R := by
    rw [Finset.disjoint_left]
    intro z hzB hzR
    exact (Finset.mem_sdiff.mp hzR).2 (Finset.mem_union_left Q hzB)
  have hcover : G.neighborFinset v =
      (G.neighborFinset v ∩ B) ∪ (G.neighborFinset v ∩ R) := by
    ext z
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hvz
      by_cases hzB : z ∈ B
      · exact Or.inl ⟨hvz, hzB⟩
      · by_cases hzR : z ∈ R
        · exact Or.inr ⟨hvz, hzR⟩
        · exfalso
          have hzU : z ∈ B ∪ Q := by
            by_contra hzU
            exact hzR (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzU⟩)
          rcases Finset.mem_union.mp hzU with hzB' | hzQ
          · exact hzB hzB'
          · exact hvQ z hzQ ((G.mem_neighborFinset v z).mp hvz)
    · rintro (⟨hvz, -⟩ | ⟨hvz, -⟩)
      · exact hvz
      · exact hvz
  have hdInter : Disjoint (G.neighborFinset v ∩ B)
      (G.neighborFinset v ∩ R) :=
    hdBR.mono Finset.inter_subset_right Finset.inter_subset_right
  have hcard := Finset.card_union_of_disjoint hdInter
  rw [← hcover, G.card_neighborFinset_eq_degree, hdeg] at hcard
  simpa [R] using hcard.symm

/-- The four centers of a defect `K₄` are disjoint from the union of their
four original neighborhoods when the defect graph is antipodal. -/
theorem defectKFour_blocks_disjoint_centers_of_eq_antipodal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (secondOrderDefectGraph G).Adj]
    (hDeq : secondOrderDefectGraph G = antipodalGraph G)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y) :
    Disjoint (G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y) ({a, b, x, y} : Finset V) := by
  have hnotG_of_D : ∀ {u w : V},
      (secondOrderDefectGraph G).Adj u w → ¬ G.Adj u w := by
    intro u w huw
    rw [hDeq] at huw
    exact ((mem_antipodalNeighbors G u w).mp
      ((antipodalGraph_adj G u w).mp huw)).2.1
  rw [Finset.disjoint_left]
  intro z hzB hzQ
  simp only [Finset.mem_union, G.mem_neighborFinset] at hzB
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzQ
  have haa : ¬ G.Adj a a := G.loopless.irrefl a
  have hbb : ¬ G.Adj b b := G.loopless.irrefl b
  have hxx : ¬ G.Adj x x := G.loopless.irrefl x
  have hyy : ¬ G.Adj y y := G.loopless.irrefl y
  have habG := hnotG_of_D hab
  have haxG := hnotG_of_D hax
  have hbxG := hnotG_of_D hbx
  have hayG := hnotG_of_D hay
  have hbyG := hnotG_of_D hby
  have hxyG := hnotG_of_D hxy
  have hbaG : ¬ G.Adj b a := fun h => habG h.symm
  have hxaG : ¬ G.Adj x a := fun h => haxG h.symm
  have hxbG : ¬ G.Adj x b := fun h => hbxG h.symm
  have hyaG : ¬ G.Adj y a := fun h => hayG h.symm
  have hybG : ¬ G.Adj y b := fun h => hbyG h.symm
  have hyxG : ¬ G.Adj y x := fun h => hxyG h.symm
  aesop

/-- Sharp residual degree structure in the pure antipodal closed-`K₄`
branch: every residual vertex has four neighbors in the 24-vertex block
layer and two neighbors inside the residual six-set. -/
theorem degreeSix_thirtyFour_defectKFour_residual_G_degree_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    let R := Finset.univ \ (B ∪ {a, b, x, y})
    R.card = 6 ∧ ∀ r ∈ R,
      (G.neighborFinset r ∩ R).card = 2 ∧
        (G.neighborFinset r ∩ B).card = 4 := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let Q : Finset V := {a, b, x, y}
  let R := Finset.univ \ (B ∪ Q)
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = 3 := by
    intro z
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) z
  have hDeq :=
    degreeSix_thirtyFour_secondOrderDefectGraph_eq_antipodalGraph_of_colorOrder_zero
      G hfree hreg hcard hzero
  have hBcard : B.card = 24 := by
    simpa [B] using
      degreeSix_defectKFour_four_neighborhood_union_card_eq_twentyFour
        G hfree hreg hab hax hbx hay hby hxy
  have hQcard : Q.card = 4 := by
    have habNe := (secondOrderDefectGraph G).ne_of_adj hab
    have haxNe := (secondOrderDefectGraph G).ne_of_adj hax
    have hbxNe := (secondOrderDefectGraph G).ne_of_adj hbx
    have hayNe := (secondOrderDefectGraph G).ne_of_adj hay
    have hbyNe := (secondOrderDefectGraph G).ne_of_adj hby
    have hxyNe := (secondOrderDefectGraph G).ne_of_adj hxy
    simp [Q, habNe, haxNe, hbxNe, hayNe, hbyNe, hxyNe]
  have hdBQ : Disjoint B Q := by
    simpa [B, Q] using defectKFour_blocks_disjoint_centers_of_eq_antipodal
      G hDeq hab hax hbx hay hby hxy
  have hUcard : (B ∪ Q).card = 28 := by
    rw [Finset.card_union_of_disjoint hdBQ, hBcard, hQcard]
  have hRcard : R.card = 6 := by
    change (Finset.univ \ (B ∪ Q)).card = 6
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, hcard, hUcard]
  rcases cubic_defectKFour_neighborFinsets (secondOrderDefectGraph G) hDreg
      hab hax hbx hay hby hxy with ⟨hKa, hKb, hKx, hKy⟩
  have hinternal : ∀ r ∈ R, (G.neighborFinset r ∩ R).card ≤ 2 := by
    intro r hr
    have hDsub : (secondOrderDefectGraph G).neighborFinset r ⊆ R := by
      intro w hrw
      have hrwAdj : (secondOrderDefectGraph G).Adj r w := by simpa using hrw
      have hrNotU := (Finset.mem_sdiff.mp hr).2
      have hrOutside : r ∉ Q := by
        intro hrQ
        exact hrNotU (Finset.mem_union_right B hrQ)
      have hrZero : ∀ z ∈ Q, ¬ G.Adj z r := by
        intro z hzQ hzr
        apply hrNotU
        apply Finset.mem_union_left Q
        simp only [B, Finset.mem_union, G.mem_neighborFinset]
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hzQ
        rcases hzQ with hza | hzb | hzx | hzy
        · exact Or.inl (Or.inl (Or.inl (hza ▸ hzr)))
        · exact Or.inl (Or.inl (Or.inr (hzb ▸ hzr)))
        · exact Or.inl (Or.inr (hzx ▸ hzr))
        · exact Or.inr (hzy ▸ hzr)
      have haZero : ¬ G.Adj a w :=
        no_adj_of_defect_adj_of_zero_block_contact G hfree hreg Q
          (by rw [hKa]; simp [Q]) hrZero hrwAdj
      have hbZero : ¬ G.Adj b w :=
        no_adj_of_defect_adj_of_zero_block_contact G hfree hreg Q
          (by rw [hKb]; simp [Q]) hrZero hrwAdj
      have hxZero : ¬ G.Adj x w :=
        no_adj_of_defect_adj_of_zero_block_contact G hfree hreg Q
          (by rw [hKx]; simp [Q]) hrZero hrwAdj
      have hyZero : ¬ G.Adj y w :=
        no_adj_of_defect_adj_of_zero_block_contact G hfree hreg Q
          (by rw [hKy]; simp [Q]) hrZero hrwAdj
      have hwOutside : w ∉ Q := by
        intro hwQ
        apply hrOutside
        have hrMem : r ∈ (secondOrderDefectGraph G).neighborFinset w := by
          simpa using hrwAdj.symm
        simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hwQ ⊢
        rcases hwQ with hwa | hwb | hwx | hwy
        · rw [hwa, hKa] at hrMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hrMem ⊢
          aesop
        · rw [hwb, hKb] at hrMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hrMem ⊢
          aesop
        · rw [hwx, hKx] at hrMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hrMem ⊢
          aesop
        · rw [hwy, hKy] at hrMem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hrMem ⊢
          aesop
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ w, ?_⟩
      intro hwU
      rcases Finset.mem_union.mp hwU with hwB | hwQ
      · simp only [B, Finset.mem_union, G.mem_neighborFinset] at hwB
        rcases hwB with ((hwa | hwb) | hwx) | hwy
        · exact haZero hwa
        · exact hbZero hwb
        · exact hxZero hwx
        · exact hyZero hwy
      · exact hwOutside hwQ
    have hDcard : ((secondOrderDefectGraph G).neighborFinset r).card = 3 := by
      rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree, hDreg r]
    exact internal_G_neighbor_card_le_two_of_closed_cubic_antipodal_six
      G hDeq R hRcard hr hDsub hDcard
  have hpartition : ∀ r ∈ R,
      (G.neighborFinset r ∩ B).card + (G.neighborFinset r ∩ R).card = 6 := by
    intro r hr
    have hrNotU := (Finset.mem_sdiff.mp hr).2
    have hrQ : ∀ q ∈ Q, ¬ G.Adj r q := by
      intro q hq hrq
      apply hrNotU
      apply Finset.mem_union_left Q
      simp only [B, Finset.mem_union, G.mem_neighborFinset]
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with hqa | hqb | hqx | hqy
      · exact Or.inl (Or.inl (Or.inl (hqa ▸ hrq.symm)))
      · exact Or.inl (Or.inl (Or.inr (hqb ▸ hrq.symm)))
      · exact Or.inl (Or.inr (hqx ▸ hrq.symm))
      · exact Or.inr (hqy ▸ hrq.symm)
    simpa [R] using
      card_neighbor_inter_add_card_neighbor_inter_compl_union
        G B Q (hreg r) hrQ
  have hlower : ∀ r ∈ R, 4 ≤ (G.neighborFinset r ∩ B).card := by
    intro r hr
    have hi := hinternal r hr
    have hp := hpartition r hr
    omega
  have hsum : (∑ r ∈ R, (G.neighborFinset r ∩ B).card) = 24 := by
    simpa [B, Q, R] using
      (degreeSix_thirtyFour_defectKFour_block_residual_incidence_sum_eq_twentyFour
        G hfree hreg hcard hDreg hab hax hbx hay hby hxy hzero).2
  refine ⟨hRcard, ?_⟩
  intro r hr
  have hcross := eq_four_of_mem_of_card_six_of_four_le_of_sum_eq_twentyFour
    R hRcard (fun z => (G.neighborFinset z ∩ B).card) hlower hsum hr
  have hp := hpartition r hr
  refine ⟨?_, hcross⟩
  change (G.neighborFinset r ∩ R).card = 2
  omega

/-- Every residual vertex has exactly one original neighbor in each of the
four center-neighborhood fibers.  The four total layer neighbors are forced
to distribute one per fiber because two in the same fiber would give that
residual vertex and the fiber's center two common neighbors, creating a
`C₄`. -/
theorem degreeSix_thirtyFour_defectKFour_residual_four_fiber_counts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y r : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0)
    (hr : r ∈ Finset.univ \ (
      (G.neighborFinset a ∪ G.neighborFinset b ∪
        G.neighborFinset x ∪ G.neighborFinset y) ∪ {a, b, x, y})) :
    (G.neighborFinset r ∩ G.neighborFinset a).card = 1 ∧
      (G.neighborFinset r ∩ G.neighborFinset b).card = 1 ∧
      (G.neighborFinset r ∩ G.neighborFinset x).card = 1 ∧
      (G.neighborFinset r ∩ G.neighborFinset y).card = 1 := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let Q : Finset V := {a, b, x, y}
  let R := Finset.univ \ (B ∪ Q)
  have hrR : r ∈ R := by simpa [B, Q, R] using hr
  have hprofile := degreeSix_thirtyFour_defectKFour_residual_G_degree_profile
    G hfree hreg hcard hab hax hbx hay hby hxy hzero
  have htotal : (G.neighborFinset r ∩ B).card = 4 := hprofile.2 r hrR |>.2
  have hrNotQ : r ∉ Q := by
    intro hrQ
    exact (Finset.mem_sdiff.mp hrR).2 (Finset.mem_union_right B hrQ)
  have hra : r ≠ a := by
    intro hra
    apply hrNotQ
    simp [Q, hra]
  have hrb : r ≠ b := by
    intro hrb
    apply hrNotQ
    simp [Q, hrb]
  have hrx : r ≠ x := by
    intro hrx
    apply hrNotQ
    simp [Q, hrx]
  have hry : r ≠ y := by
    intro hry
    apply hrNotQ
    simp [Q, hry]
  have hA : (G.neighborFinset r ∩ G.neighborFinset a).card ≤ 1 :=
    common_le_one_of_not_containsC4 hfree r a hra
  have hB : (G.neighborFinset r ∩ G.neighborFinset b).card ≤ 1 :=
    common_le_one_of_not_containsC4 hfree r b hrb
  have hX : (G.neighborFinset r ∩ G.neighborFinset x).card ≤ 1 :=
    common_le_one_of_not_containsC4 hfree r x hrx
  have hY : (G.neighborFinset r ∩ G.neighborFinset y).card ≤ 1 :=
    common_le_one_of_not_containsC4 hfree r y hry
  have hdAB := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hab
  have hdAX := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hax
  have hdBX := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hbx
  have hdAY := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hay
  have hdBY := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hby
  have hdXY := neighborFinset_disjoint_of_secondOrderDefect_adj G hfree hxy
  have hdABX : Disjoint
      (G.neighborFinset a ∪ G.neighborFinset b) (G.neighborFinset x) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hdAX, hdBX⟩
  have hdABXY : Disjoint
      (G.neighborFinset a ∪ G.neighborFinset b ∪ G.neighborFinset x)
      (G.neighborFinset y) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨hdAY, hdBY⟩, hdXY⟩
  have hcardInterUnion (P S : Finset V) (hd : Disjoint P S) :
      (G.neighborFinset r ∩ (P ∪ S)).card =
        (G.neighborFinset r ∩ P).card +
          (G.neighborFinset r ∩ S).card := by
    rw [Finset.inter_union_distrib_left]
    apply Finset.card_union_of_disjoint
    exact hd.mono Finset.inter_subset_right Finset.inter_subset_right
  have hsum :
      (G.neighborFinset r ∩ G.neighborFinset a).card +
        (G.neighborFinset r ∩ G.neighborFinset b).card +
        (G.neighborFinset r ∩ G.neighborFinset x).card +
        (G.neighborFinset r ∩ G.neighborFinset y).card = 4 := by
    rw [← hcardInterUnion _ _ hdAB,
      ← hcardInterUnion _ _ hdABX,
      ← hcardInterUnion _ _ hdABXY]
    exact htotal
  omega

/-- Residual `K₃,₃` adjacency dictates the defect labels of the cover.
If a layer vertex `p` is attached in `G` to residual vertex `r`, then for
every residual defect neighbor `s` of `r`, exactly one defect neighbor of
`p` is the unique layer vertex attached to `s`. -/
theorem degreeSix_thirtyFour_defectKFour_layer_residual_transition_count_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y p r s : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0)
    (hp : p ∈ G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y)
    (hr : r ∈ Finset.univ \ (
      (G.neighborFinset a ∪ G.neighborFinset b ∪
        G.neighborFinset x ∪ G.neighborFinset y) ∪ {a, b, x, y}))
    (hs : s ∈ Finset.univ \ (
      (G.neighborFinset a ∪ G.neighborFinset b ∪
        G.neighborFinset x ∪ G.neighborFinset y) ∪ {a, b, x, y}))
    (hDs : (secondOrderDefectGraph G).neighborFinset s ⊆
      Finset.univ \ (
        (G.neighborFinset a ∪ G.neighborFinset b ∪
          G.neighborFinset x ∪ G.neighborFinset y) ∪ {a, b, x, y}))
    (hpr : G.Adj p r)
    (hrsD : (secondOrderDefectGraph G).Adj r s) :
    (((secondOrderDefectGraph G).neighborFinset p).filter
      (fun z => G.Adj z s)).card = 1 := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let Q : Finset V := {a, b, x, y}
  let R := Finset.univ \ (B ∪ Q)
  have hpB : p ∈ B := by simpa [B] using hp
  have hrR : r ∈ R := by simpa [B, Q, R] using hr
  have _hsR : s ∈ R := by simpa [B, Q, R] using hs
  have hDsR : (secondOrderDefectGraph G).neighborFinset s ⊆ R := by
    simpa [B, Q, R] using hDs
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = 3 := by
    intro z
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) z
  have hcontact :=
    degreeSix_thirtyFour_defectKFour_blockVertex_residual_inter_card_eq_one
      G hfree hreg hcard hDreg hab hax hbx hay hby hxy hzero hpB
  have hcontactR : (G.neighborFinset p ∩ R).card = 1 := by
    simpa [B, Q, R, Finset.union_assoc] using hcontact
  have hunique : ∀ z ∈ R, G.Adj p z → z = r := by
    intro z hzR hpz
    apply Finset.card_le_one.mp (by omega : (G.neighborFinset p ∩ R).card ≤ 1)
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p z).mpr hpz, hzR⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p r).mpr hpr, hrR⟩
  exact card_defectNeighbors_adj_eq_one_of_unique_closed_contact
    G hfree hreg R hDsR hpr hunique hrsD.symm

/-- The corresponding original-graph label law: a layer vertex attached to
`r` has exactly one common neighbor outside the residual with every residual
vertex `s` on the opposite (`D`-adjacent) side.  In the block decomposition
that common neighbor is the unique layer neighbor carrying label `s`. -/
theorem degreeSix_thirtyFour_defectKFour_layer_oppositeResidual_common_outside_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y p r s : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0)
    (hp : p ∈ G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y)
    (hr : r ∈ Finset.univ \ (
      (G.neighborFinset a ∪ G.neighborFinset b ∪
        G.neighborFinset x ∪ G.neighborFinset y) ∪ {a, b, x, y}))
    (hs : s ∈ Finset.univ \ (
      (G.neighborFinset a ∪ G.neighborFinset b ∪
        G.neighborFinset x ∪ G.neighborFinset y) ∪ {a, b, x, y}))
    (hDs : (secondOrderDefectGraph G).neighborFinset s ⊆
      Finset.univ \ (
        (G.neighborFinset a ∪ G.neighborFinset b ∪
          G.neighborFinset x ∪ G.neighborFinset y) ∪ {a, b, x, y}))
    (hpr : G.Adj p r)
    (hrsD : (secondOrderDefectGraph G).Adj r s) :
    ((G.neighborFinset p ∩ G.neighborFinset s) ∩
      (Finset.univ \ (Finset.univ \ (
        (G.neighborFinset a ∪ G.neighborFinset b ∪
          G.neighborFinset x ∪ G.neighborFinset y) ∪
            {a, b, x, y})))).card = 1 := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let Q : Finset V := {a, b, x, y}
  let R := Finset.univ \ (B ∪ Q)
  have hpB : p ∈ B := by simpa [B] using hp
  have hpOut : p ∉ R := by
    intro hpR
    exact (Finset.mem_sdiff.mp hpR).2 (Finset.mem_union_left Q hpB)
  have hrR : r ∈ R := by simpa [B, Q, R] using hr
  have hsR : s ∈ R := by simpa [B, Q, R] using hs
  have hDsR : (secondOrderDefectGraph G).neighborFinset s ⊆ R := by
    simpa [B, Q, R] using hDs
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = 3 := by
    intro z
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) z
  have hcontact :=
    degreeSix_thirtyFour_defectKFour_blockVertex_residual_inter_card_eq_one
      G hfree hreg hcard hDreg hab hax hbx hay hby hxy hzero hpB
  have hcontactR : (G.neighborFinset p ∩ R).card = 1 := by
    simpa [B, Q, R, Finset.union_assoc] using hcontact
  have hunique : ∀ z ∈ R, G.Adj p z → z = r := by
    intro z hzR hpz
    apply Finset.card_le_one.mp (by omega : (G.neighborFinset p ∩ R).card ≤ 1)
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p z).mpr hpz, hzR⟩
    · exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset p r).mpr hpr, hrR⟩
  have hDeq :=
    degreeSix_thirtyFour_secondOrderDefectGraph_eq_antipodalGraph_of_colorOrder_zero
      G hfree hreg hcard hzero
  have hrsNotG : ¬ G.Adj r s := by
    have hrsC := hrsD
    rw [hDeq] at hrsC
    exact ((mem_antipodalNeighbors G r s).mp
      ((antipodalGraph_adj G r s).mp hrsC)).2.1
  simpa [B, Q, R] using
    card_common_outside_eq_one_of_unique_contact_defectAdj
      G hfree R hpOut hsR hDsR hpr hrR hunique hrsD hrsNotG

/-- Every original-graph edge inside the residual six-set has a common
neighbor inside that same residual.  A layer witness would have two residual
neighbors, contradicting its exact residual degree one; a center witness is
excluded by the definition of the residual. -/
theorem degreeSix_thirtyFour_defectKFour_residual_edge_has_internal_witness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    let R := Finset.univ \ (B ∪ {a, b, x, y})
    ∀ r ∈ R, ∀ s ∈ R, G.Adj r s →
      ∃ t ∈ R, G.Adj r t ∧ G.Adj s t := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let Q : Finset V := {a, b, x, y}
  let R := Finset.univ \ (B ∪ Q)
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = 3 := by
    intro z
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) z
  have htriEq := degreeSix_thirtyFour_triangularEdgeGraph_eq_of_colorOrder_zero
    G hfree hreg hcard hzero
  dsimp only
  intro r hr s hs hrs
  have htri : (triangularEdgeGraph G).Adj r s := by
    rw [htriEq]
    exact hrs
  have hnonzero := (triangularEdgeGraph_adj G r s).mp htri |>.2
  obtain ⟨t, ht⟩ := Finset.card_ne_zero.mp hnonzero
  have htParts := Finset.mem_inter.mp ht
  have hrt : G.Adj r t := (G.mem_neighborFinset r t).mp htParts.1
  have hst : G.Adj s t := (G.mem_neighborFinset s t).mp htParts.2
  have htR : t ∈ R := by
    by_contra htNotR
    have htU : t ∈ B ∪ Q := by
      by_contra htNotU
      exact htNotR (Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, htNotU⟩)
    rcases Finset.mem_union.mp htU with htB | htQ
    · have hone :=
        degreeSix_thirtyFour_defectKFour_blockVertex_residual_inter_card_eq_one
          G hfree hreg hcard hDreg hab hax hbx hay hby hxy hzero htB
      have hrsNe : r ≠ s := G.ne_of_adj hrs
      have hpair : ({r, s} : Finset V) ⊆ G.neighborFinset t ∩ R := by
        simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
          Finset.mem_inter, G.mem_neighborFinset]
        exact ⟨⟨hrt.symm, hr⟩, ⟨hst.symm, hs⟩⟩
      have hpairCard : ({r, s} : Finset V).card = 2 := by
        simp [hrsNe]
      have hle := Finset.card_le_card hpair
      have honeR : (G.neighborFinset t ∩ R).card = 1 := by
        simpa only [B, Q, R, Finset.union_comm, Finset.union_left_comm,
          Finset.union_assoc] using hone
      rw [hpairCard, honeR] at hle
      omega
    · have hrNotU := (Finset.mem_sdiff.mp hr).2
      apply hrNotU
      apply Finset.mem_union_left Q
      simp only [B, Finset.mem_union, G.mem_neighborFinset]
      simp only [Q, Finset.mem_insert, Finset.mem_singleton] at htQ
      rcases htQ with hta | htb | htx | hty
      · exact Or.inl (Or.inl (Or.inl (hta ▸ hrt.symm)))
      · exact Or.inl (Or.inl (Or.inr (htb ▸ hrt.symm)))
      · exact Or.inl (Or.inr (htx ▸ hrt.symm))
      · exact Or.inr (hty ▸ hrt.symm)
  exact ⟨t, htR, hrt, hst⟩

/-- Each residual edge lies in an internal triangle, and because the
residual internal degree is exactly two, its endpoint's full residual
neighborhood is precisely the other two vertices of that triangle. -/
theorem degreeSix_thirtyFour_defectKFour_residual_edge_closes_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    let R := Finset.univ \ (B ∪ {a, b, x, y})
    ∀ r ∈ R, ∀ s ∈ R, G.Adj r s →
      ∃ t ∈ R, t ≠ s ∧ G.Adj s t ∧
        G.neighborFinset r ∩ R = {s, t} := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let R := Finset.univ \ (B ∪ {a, b, x, y})
  have hprofile := degreeSix_thirtyFour_defectKFour_residual_G_degree_profile
    G hfree hreg hcard hab hax hbx hay hby hxy hzero
  have hwitness :=
    degreeSix_thirtyFour_defectKFour_residual_edge_has_internal_witness
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  dsimp only at hprofile hwitness ⊢
  intro r hr s hs hrs
  obtain ⟨t, ht, hrt, hst⟩ := hwitness r hr s hs hrs
  have hts : t ≠ s := by
    intro h
    exact G.loopless.irrefl s (h ▸ hst)
  have hsub : ({s, t} : Finset V) ⊆ G.neighborFinset r ∩ R := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
      Finset.mem_inter, G.mem_neighborFinset]
    exact ⟨⟨hrs, hs⟩, ⟨hrt, ht⟩⟩
  have hpairCard : ({s, t} : Finset V).card = 2 := by
    simp [hts.symm]
  have hinterCard : (G.neighborFinset r ∩ R).card = 2 :=
    (hprofile.2 r hr).1
  refine ⟨t, ht, hts, hst, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hinterCard, hpairCard]

/-- Local classification of the residual graph: the two residual neighbors
of every vertex are adjacent, so the residual is locally a union of
triangles (and, at order six, is therefore `2 K₃`). -/
theorem degreeSix_thirtyFour_defectKFour_residual_locally_triangle_union
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    let R := Finset.univ \ (B ∪ {a, b, x, y})
    ∀ r ∈ R, ∀ s ∈ R, ∀ t ∈ R,
      G.Adj r s → G.Adj r t → s ≠ t → G.Adj s t := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let R := Finset.univ \ (B ∪ {a, b, x, y})
  have hclose := degreeSix_thirtyFour_defectKFour_residual_edge_closes_triangle
    G hfree hreg hcard hab hax hbx hay hby hxy hzero
  dsimp only at hclose ⊢
  intro r hr s hs t ht hrs hrt hst
  obtain ⟨u, hu, hus, hsu, hN⟩ := hclose r hr s hs hrs
  have htN : t ∈ G.neighborFinset r ∩ R :=
    Finset.mem_inter.mpr ⟨(G.mem_neighborFinset r t).mpr hrt, ht⟩
  rw [hN] at htN
  simp only [Finset.mem_insert, Finset.mem_singleton] at htN
  rcases htN with hts | htu
  · exact (hst hts.symm).elim
  · exact htu ▸ hsu

/-- Explicit first half of the residual `2K₃` partition: there is an
internal triangle whose complement in the residual has exactly three
vertices. -/
theorem degreeSix_thirtyFour_defectKFour_residual_exists_triangle_compl_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    let R := Finset.univ \ (B ∪ {a, b, x, y})
    ∃ r s t : V, r ∈ R ∧ s ∈ R ∧ t ∈ R ∧
      r ≠ s ∧ r ≠ t ∧ s ≠ t ∧
      G.Adj r s ∧ G.Adj r t ∧ G.Adj s t ∧
      (R \ {r, s, t}).card = 3 := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let R := Finset.univ \ (B ∪ {a, b, x, y})
  have hprofile := degreeSix_thirtyFour_defectKFour_residual_G_degree_profile
    G hfree hreg hcard hab hax hbx hay hby hxy hzero
  have hclose := degreeSix_thirtyFour_defectKFour_residual_edge_closes_triangle
    G hfree hreg hcard hab hax hbx hay hby hxy hzero
  dsimp only at hprofile hclose ⊢
  have hRcard := hprofile.1
  change R.card = 6 at hRcard
  have hRnonempty : R.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨r, hr⟩ := hRnonempty
  have hNrCard : (G.neighborFinset r ∩ R).card = 2 := (hprofile.2 r hr).1
  have hNrNonempty : (G.neighborFinset r ∩ R).Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨s, hsN⟩ := hNrNonempty
  have hsParts := Finset.mem_inter.mp hsN
  have hrs : G.Adj r s := (G.mem_neighborFinset r s).mp hsParts.1
  have hs : s ∈ R := hsParts.2
  obtain ⟨t, ht, hts, hst, hN⟩ := hclose r hr s hs hrs
  have hrt : G.Adj r t := by
    have : t ∈ G.neighborFinset r ∩ R := by
      rw [hN]
      simp
    exact (G.mem_neighborFinset r t).mp (Finset.mem_inter.mp this).1
  have hrsNe : r ≠ s := G.ne_of_adj hrs
  have hrtNe : r ≠ t := G.ne_of_adj hrt
  have hPsub : ({r, s, t} : Finset V) ⊆ R := by
    simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hr, hs, ht⟩
  have hPcard : ({r, s, t} : Finset V).card = 3 := by
    simp [hrsNe, hrtNe, hts.symm]
  have hcompl : (R \ {r, s, t}).card = 3 := by
    rw [Finset.card_sdiff_of_subset hPsub, hRcard, hPcard]
  exact ⟨r, s, t, hr, hs, ht, hrsNe, hrtNe, hts.symm,
    hrs, hrt, hst, hcompl⟩

/-- For an isolated cubic defect `K₄`, being an outside vertex with zero
original-graph contact to the four centers is preserved across every defect
edge. -/
theorem defectKFour_zero_contact_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y v w : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hvOutside : v ∉ ({a, b, x, y} : Finset V))
    (hvZero : ∀ z ∈ ({a, b, x, y} : Finset V), ¬ G.Adj z v)
    (hvwD : (secondOrderDefectGraph G).Adj v w) :
    w ∉ ({a, b, x, y} : Finset V) ∧
      ∀ z ∈ ({a, b, x, y} : Finset V), ¬ G.Adj z w := by
  let D := secondOrderDefectGraph G
  have hK := cubic_defectKFour_neighborFinsets D hregD
    hab hax hbx hay hby hxy
  rcases hK with ⟨hKa, hKb, hKx, hKy⟩
  have hwOutside : w ∉ ({a, b, x, y} : Finset V) := by
    intro hw
    have hvInside : v ∈ ({a, b, x, y} : Finset V) := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hwa | hwb | hwx | hwy
      · have hav : D.Adj a v := by simpa [hwa] using hvwD.symm
        have hv := (D.mem_neighborFinset a v).mpr hav
        rw [hKa] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
        aesop
      · have hbv : D.Adj b v := by simpa [hwb] using hvwD.symm
        have hv := (D.mem_neighborFinset b v).mpr hbv
        rw [hKb] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
        aesop
      · have hxv : D.Adj x v := by simpa [hwx] using hvwD.symm
        have hv := (D.mem_neighborFinset x v).mpr hxv
        rw [hKx] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
        aesop
      · have hyv : D.Adj y v := by simpa [hwy] using hvwD.symm
        have hv := (D.mem_neighborFinset y v).mpr hyv
        rw [hKy] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
        aesop
    exact hvOutside hvInside
  refine ⟨hwOutside, ?_⟩
  have haZero : ¬ G.Adj a w :=
    no_adj_of_defect_adj_of_zero_block_contact G hfree hreg
      {a, b, x, y} (by rw [hKa]; simp) hvZero hvwD
  have hbZero : ¬ G.Adj b w :=
    no_adj_of_defect_adj_of_zero_block_contact G hfree hreg
      {a, b, x, y} (by rw [hKb]; simp) hvZero hvwD
  have hxZero : ¬ G.Adj x w :=
    no_adj_of_defect_adj_of_zero_block_contact G hfree hreg
      {a, b, x, y} (by rw [hKx]; simp) hvZero hvwD
  have hyZero : ¬ G.Adj y w :=
    no_adj_of_defect_adj_of_zero_block_contact G hfree hreg
      {a, b, x, y} (by rw [hKy]; simp) hvZero hvwD
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with hza | hzb | hzx | hzy
  · simpa [hza] using haZero
  · simpa [hzb] using hbZero
  · simpa [hzx] using hxZero
  · simpa [hzy] using hyZero

/-- In the pure antipodal branch, a closed defect `K₄` and its four
pairwise-disjoint degree-six neighborhoods occupy exactly 28 vertices. -/
theorem degreeSix_thirtyFour_antipodal_defectKFour_centered_footprint_card_eq_twentyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ v, G.degree v = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    (G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y ∪ {a, b, x, y}).card = 28 := by
  let F := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  have hFcard : F.card = 24 :=
    degreeSix_defectKFour_four_neighborhood_union_card_eq_twentyFour
      G hfree hreg hab hax hbx hay hby hxy
  have hDeq :=
    degreeSix_thirtyFour_secondOrderDefectGraph_eq_antipodalGraph_of_colorOrder_zero
      G hfree hreg hcard hzero
  have hnotG_of_D : ∀ {u v : V},
      (secondOrderDefectGraph G).Adj u v → ¬ G.Adj u v := by
    intro u v huv
    rw [hDeq] at huv
    exact ((mem_antipodalNeighbors G u v).mp
      ((antipodalGraph_adj G u v).mp huv)).2.1
  have haNotF : a ∉ F := by
    simp only [F, Finset.mem_union, G.mem_neighborFinset]
    push Not
    exact ⟨⟨⟨G.loopless.irrefl a, fun h => hnotG_of_D hab h.symm⟩,
      fun h => hnotG_of_D hax h.symm⟩,
      fun h => hnotG_of_D hay h.symm⟩
  have hbNotF : b ∉ F := by
    simp only [F, Finset.mem_union, G.mem_neighborFinset]
    push Not
    exact ⟨⟨⟨hnotG_of_D hab, G.loopless.irrefl b⟩,
      fun h => hnotG_of_D hbx h.symm⟩,
      fun h => hnotG_of_D hby h.symm⟩
  have hxNotF : x ∉ F := by
    simp only [F, Finset.mem_union, G.mem_neighborFinset]
    push Not
    exact ⟨⟨⟨hnotG_of_D hax, hnotG_of_D hbx⟩,
      G.loopless.irrefl x⟩, fun h => hnotG_of_D hxy h.symm⟩
  have hyNotF : y ∉ F := by
    simp only [F, Finset.mem_union, G.mem_neighborFinset]
    push Not
    exact ⟨⟨⟨hnotG_of_D hay, hnotG_of_D hby⟩,
      hnotG_of_D hxy⟩, G.loopless.irrefl y⟩
  have hcenter : ∀ z ∈ ({a, b, x, y} : Finset V), z ∉ F := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz | hz
    · exact hz ▸ haNotF
    · exact hz ▸ hbNotF
    · exact hz ▸ hxNotF
    · exact hz ▸ hyNotF
  have hdisj : Disjoint F ({a, b, x, y} : Finset V) := by
    rw [Finset.disjoint_left]
    exact fun z hzF hzQ => hcenter z hzQ hzF
  have hQcard : ({a, b, x, y} : Finset V).card = 4 := by
    have habNe := (secondOrderDefectGraph G).ne_of_adj hab
    have haxNe := (secondOrderDefectGraph G).ne_of_adj hax
    have hbxNe := (secondOrderDefectGraph G).ne_of_adj hbx
    have hayNe := (secondOrderDefectGraph G).ne_of_adj hay
    have hbyNe := (secondOrderDefectGraph G).ne_of_adj hby
    have hxyNe := (secondOrderDefectGraph G).ne_of_adj hxy
    simp [habNe, haxNe, hbxNe, hayNe, hbyNe, hxyNe]
  change (F ∪ {a, b, x, y}).card = 28
  rw [Finset.card_union_of_disjoint hdisj, hFcard, hQcard]

/-- Complement form of the centered defect-`K₄` count: exactly six vertices
remain outside the four centers and all four of their neighborhoods. -/
theorem degreeSix_thirtyFour_antipodal_defectKFour_exists_residual_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ v, G.degree v = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    ∃ R : Finset V, R.card = 6 ∧
      R = Finset.univ \ (G.neighborFinset a ∪ G.neighborFinset b ∪
        G.neighborFinset x ∪ G.neighborFinset y ∪ {a, b, x, y}) := by
  let U := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y ∪ {a, b, x, y}
  have hUcard : U.card = 28 :=
    degreeSix_thirtyFour_antipodal_defectKFour_centered_footprint_card_eq_twentyEight
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  let R := Finset.univ \ U
  have hRcard : R.card = 6 := by
    change (Finset.univ \ U).card = 6
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ U),
      Finset.card_univ, hcard, hUcard]
  exact ⟨R, hRcard, rfl⟩

/-- The six vertices outside a closed defect `K₄` and its four original
neighborhoods form a defect-closed set. -/
theorem defectKFour_residual_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y v w : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hv : v ∈ Finset.univ \ (G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y ∪ {a, b, x, y}))
    (hvwD : (secondOrderDefectGraph G).Adj v w) :
    w ∈ Finset.univ \ (G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y ∪ {a, b, x, y}) := by
  have hvNotU := (Finset.mem_sdiff.mp hv).2
  have hvOutside : v ∉ ({a, b, x, y} : Finset V) := by
    intro hvQ
    apply hvNotU
    exact Finset.mem_union_right _ hvQ
  have hvZero : ∀ z ∈ ({a, b, x, y} : Finset V), ¬ G.Adj z v := by
    intro z hzQ hzv
    apply hvNotU
    simp only [Finset.mem_union, G.mem_neighborFinset,
      Finset.mem_insert, Finset.mem_singleton] at hzQ ⊢
    aesop
  have hclosed := defectKFour_zero_contact_closed G hfree hreg hregD
    hab hax hbx hay hby hxy hvOutside hvZero hvwD
  rcases hclosed with ⟨hwOutside, hwZero⟩
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ w, ?_⟩
  intro hwU
  simp only [Finset.mem_union, G.mem_neighborFinset,
    Finset.mem_insert, Finset.mem_singleton] at hwU
  have haZero := hwZero a (by simp)
  have hbZero := hwZero b (by simp)
  have hxZero := hwZero x (by simp)
  have hyZero := hwZero y (by simp)
  have hwNeA : w ≠ a := by
    intro hwa
    apply hwOutside
    simp [hwa]
  have hwNeB : w ≠ b := by
    intro hwb
    apply hwOutside
    simp [hwb]
  have hwNeX : w ≠ x := by
    intro hwx
    apply hwOutside
    simp [hwx]
  have hwNeY : w ≠ y := by
    intro hwy
    apply hwOutside
    simp [hwy]
  aesop

/-- Plateau-facing closed-residual package: in the pure antipodal closed
defect-`K₄` branch there is an exact six-element finset closed under all
defect neighbors. -/
theorem degreeSix_thirtyFour_antipodal_defectKFour_exists_closed_residual_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ v, G.degree v = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    ∃ R : Finset V, R.card = 6 ∧
      ∀ v ∈ R, ∀ w, (secondOrderDefectGraph G).Adj v w → w ∈ R := by
  obtain ⟨R, hRcard, hReq⟩ :=
    degreeSix_thirtyFour_antipodal_defectKFour_exists_residual_six
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = 3 := by
    intro z
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) z
  refine ⟨R, hRcard, ?_⟩
  intro v hv w hvw
  rw [hReq] at hv ⊢
  exact defectKFour_residual_closed G hfree hreg hDreg
    hab hax hbx hay hby hxy hv hvw

/-- Finset-facing cubic form of the closed residual package: every residual
vertex has all three of its defect neighbors inside the six-set. -/
theorem degreeSix_thirtyFour_antipodal_defectKFour_exists_cubic_residual_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ v, G.degree v = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    ∃ R : Finset V, R.card = 6 ∧
      ∀ v ∈ R, (secondOrderDefectGraph G).neighborFinset v ⊆ R ∧
        ((secondOrderDefectGraph G).neighborFinset v).card = 3 := by
  obtain ⟨R, hRcard, hclosed⟩ :=
    degreeSix_thirtyFour_antipodal_defectKFour_exists_closed_residual_six
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = 3 := by
    intro z
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) z
  refine ⟨R, hRcard, ?_⟩
  intro v hv
  refine ⟨?_, ?_⟩
  · intro w hvw
    have hvwAdj : (secondOrderDefectGraph G).Adj v w := by
      simpa using hvw
    exact hclosed v hv w hvwAdj
  · rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree, hDreg v]

/-- In the pure antipodal branch the two twins themselves lie outside the
four-neighborhood footprint.  Adding them to the preceding 23-vertex union
therefore certifies at least 25 distinct vertices. -/
theorem degreeSix_thirtyFour_adjacent_defect_twins_centered_footprint_twentyFive_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ v, G.degree v = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : x ≠ y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    25 ≤ (G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y ∪ {a, b}).card := by
  let F := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  have hFcard : 23 ≤ F.card := by
    exact degreeSix_adjacent_defect_twins_four_neighborhood_union_twentyThree_le
      G hfree hreg hab hax hbx hay hby hxy
  have hDeq :=
    degreeSix_thirtyFour_secondOrderDefectGraph_eq_antipodalGraph_of_colorOrder_zero
      G hfree hreg hcard hzero
  have hnotG_of_D : ∀ {u v : V},
      (secondOrderDefectGraph G).Adj u v → ¬ G.Adj u v := by
    intro u v huv
    rw [hDeq] at huv
    exact ((mem_antipodalNeighbors G u v).mp
      ((antipodalGraph_adj G u v).mp huv)).2.1
  have haNotF : a ∉ F := by
    simp only [F, Finset.mem_union, G.mem_neighborFinset]
    push Not
    exact ⟨⟨⟨G.loopless.irrefl a, fun h => hnotG_of_D hab h.symm⟩,
      fun h => hnotG_of_D hax h.symm⟩,
      fun h => hnotG_of_D hay h.symm⟩
  have hbNotF : b ∉ F := by
    simp only [F, Finset.mem_union, G.mem_neighborFinset]
    push Not
    exact ⟨⟨⟨hnotG_of_D hab, G.loopless.irrefl b⟩,
      fun h => hnotG_of_D hbx h.symm⟩,
      fun h => hnotG_of_D hby h.symm⟩
  have hdisj : Disjoint F ({a, b} : Finset V) := by
    rw [Finset.disjoint_left]
    intro z hzF hzQ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzQ
    rcases hzQ with rfl | rfl
    · exact haNotF hzF
    · exact hbNotF hzF
  have hQcard : ({a, b} : Finset V).card = 2 := by
    simp [(secondOrderDefectGraph G).ne_of_adj hab]
  change 25 ≤ (F ∪ {a, b}).card
  rw [Finset.card_union_of_disjoint hdisj, hQcard]
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

set_option maxHeartbeats 600000 in
/-- Explicit `K₃,₃` certificate for the six-vertex residual: a named
triangle `P` and its three-vertex complement `T`, with every defect row on
one side equal to the other side. -/
theorem degreeSix_thirtyFour_defectKFour_residual_exists_K33_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    let R := Finset.univ \ (B ∪ {a, b, x, y})
    ∃ P T : Finset V, P.card = 3 ∧ T.card = 3 ∧
      Disjoint P T ∧ P ∪ T = R ∧
      (∀ p ∈ P, (secondOrderDefectGraph G).neighborFinset p = T) ∧
      ∀ u ∈ T, (secondOrderDefectGraph G).neighborFinset u = P := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let R := Finset.univ \ (B ∪ {a, b, x, y})
  obtain ⟨r, s, t, hr, hs, ht, hrsNe, hrtNe, hstNe,
      hrs, hrt, hst, hcompl⟩ :=
    degreeSix_thirtyFour_defectKFour_residual_exists_triangle_compl_three
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  let P : Finset V := {r, s, t}
  let T : Finset V := R \ P
  have hprofile := degreeSix_thirtyFour_defectKFour_residual_G_degree_profile
    G hfree hreg hcard hab hax hbx hay hby hxy hzero
  dsimp only at hprofile
  have hRcard := hprofile.1
  change R.card = 6 at hRcard
  have hPcard : P.card = 3 := by
    simp [P, hrsNe, hrtNe, hstNe]
  have hPsub : P ⊆ R := by
    simp only [P, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hr, hs, ht⟩
  have hTcard : T.card = 3 := by
    change (R \ P).card = 3
    rw [Finset.card_sdiff_of_subset hPsub, hRcard, hPcard]
  have hdPT : Disjoint P T := Finset.disjoint_sdiff
  have hPT : P ∪ T = R := Finset.union_sdiff_of_subset hPsub
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = 3 := by
    intro z
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) z
  have hDeq :=
    degreeSix_thirtyFour_secondOrderDefectGraph_eq_antipodalGraph_of_colorOrder_zero
      G hfree hreg hcard hzero
  have hGrow (p q u : V) (hp : p ∈ R) (hq : q ∈ R) (hu : u ∈ R)
      (hpq : G.Adj p q) (hpu : G.Adj p u) (hqu : q ≠ u) :
      G.neighborFinset p ∩ R = {q, u} := by
    have hsub : ({q, u} : Finset V) ⊆ G.neighborFinset p ∩ R := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff,
        Finset.mem_inter, G.mem_neighborFinset]
      exact ⟨⟨hpq, hq⟩, ⟨hpu, hu⟩⟩
    have hpairCard : ({q, u} : Finset V).card = 2 := by simp [hqu]
    have hinterCard := (hprofile.2 p hp).1
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hinterCard, hpairCard]
  have hGr := hGrow r s t hr hs ht hrs hrt hstNe
  have hGs := hGrow s r t hs hr ht hrs.symm hst hrtNe
  have hGt := hGrow t r s ht hr hs hrt.symm hst.symm hrsNe
  have hEraseR : P.erase r = {s, t} := by
    ext z
    simp only [P, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzrNe, hzr | hzs | hzt⟩
      · exact (hzrNe hzr).elim
      · exact Or.inl hzs
      · exact Or.inr hzt
    · intro hz
      refine ⟨?_, Or.inr hz⟩
      intro hzr
      rcases hz with hzs | hzt
      · exact hrsNe (hzr.symm.trans hzs)
      · exact hrtNe (hzr.symm.trans hzt)
  have hEraseS : P.erase s = {r, t} := by
    ext z
    simp only [P, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hzsNe, hzr | hzs | hzt⟩
      · exact Or.inl hzr
      · exact (hzsNe hzs).elim
      · exact Or.inr hzt
    · intro hz
      refine ⟨?_, ?_⟩
      · intro hzs
        rcases hz with hzr | hzt
        · exact hrsNe (hzr.symm.trans hzs)
        · exact hstNe (hzs.symm.trans hzt)
      · rcases hz with hzr | hzt
        · exact Or.inl hzr
        · exact Or.inr (Or.inr hzt)
  have hEraseT : P.erase t = {r, s} := by
    ext z
    simp only [P, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hztNe, hzr | hzs | hzt⟩
      · exact Or.inl hzr
      · exact Or.inr hzs
      · exact (hztNe hzt).elim
    · intro hz
      refine ⟨?_, ?_⟩
      · intro hzt
        rcases hz with hzr | hzs
        · exact hrtNe (hzr.symm.trans hzt)
        · exact hstNe (hzs.symm.trans hzt)
      · rcases hz with hzr | hzs
        · exact Or.inl hzr
        · exact Or.inr (Or.inl hzs)
  have hGP : ∀ p ∈ P, G.neighborFinset p ∩ R = P.erase p := by
    intro p hp
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hpr | hps | hpt
    · subst p
      rw [hEraseR]
      exact hGr
    · subst p
      rw [hEraseS]
      exact hGs
    · subst p
      rw [hEraseT]
      exact hGt
  have hDP : ∀ p ∈ P,
      (secondOrderDefectGraph G).neighborFinset p = T := by
    intro p hp
    have hpR := hPsub hp
    have hDsub : (secondOrderDefectGraph G).neighborFinset p ⊆ R := by
      intro w hpw
      have hpwAdj : (secondOrderDefectGraph G).Adj p w := by simpa using hpw
      exact defectKFour_residual_closed G hfree hreg hDreg
        hab hax hbx hay hby hxy hpR hpwAdj
    have hDcard : ((secondOrderDefectGraph G).neighborFinset p).card = 3 := by
      rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree, hDreg p]
    have hrow :=
      internal_G_union_defect_neighbors_eq_erase_of_closed_cubic_antipodal_six
        G hDeq R hRcard hpR hDsub hDcard (hprofile.2 p hpR).1
    have hG := hGP p hp
    ext w
    constructor
    · intro hwD
      apply Finset.mem_sdiff.mpr
      refine ⟨hDsub hwD, ?_⟩
      intro hwP
      have hpwNe : w ≠ p := by
        intro hwp
        exact (secondOrderDefectGraph G).loopless.irrefl p
          (hwp ▸ ((secondOrderDefectGraph G).mem_neighborFinset p w).mp hwD)
      have hwErase : w ∈ P.erase p := Finset.mem_erase.mpr ⟨hpwNe, hwP⟩
      rw [← hG] at hwErase
      have hpwG := (G.mem_neighborFinset p w).mp
        (Finset.mem_inter.mp hwErase).1
      have hpwD := ((secondOrderDefectGraph G).mem_neighborFinset p w).mp hwD
      rw [hDeq] at hpwD
      exact ((mem_antipodalNeighbors G p w).mp
        ((antipodalGraph_adj G p w).mp hpwD)).2.1 hpwG
    · intro hwT
      have hwParts := Finset.mem_sdiff.mp hwT
      have hpwNe : w ≠ p := by
        intro hwp
        exact hwParts.2 (hwp ▸ hp)
      have hwEraseR : w ∈ R.erase p :=
        Finset.mem_erase.mpr ⟨hpwNe, hwParts.1⟩
      rw [← hrow] at hwEraseR
      rcases Finset.mem_union.mp hwEraseR with hwG | hwD
      · have hwPErase : w ∈ P.erase p := by
          rw [← hG]
          exact hwG
        exact (hwParts.2 (Finset.mem_of_mem_erase hwPErase)).elim
      · exact hwD
  have hDT : ∀ u ∈ T,
      (secondOrderDefectGraph G).neighborFinset u = P := by
    intro u hu
    have hsub : P ⊆ (secondOrderDefectGraph G).neighborFinset u := by
      intro p hp
      have hup : u ∈ (secondOrderDefectGraph G).neighborFinset p := by
        rw [hDP p hp]
        exact hu
      have hpu := ((secondOrderDefectGraph G).mem_neighborFinset p u).mp hup
      exact ((secondOrderDefectGraph G).mem_neighborFinset u p).mpr hpu.symm
    symm
    apply Finset.eq_of_subset_of_card_le hsub
    rw [hPcard, (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
      hDreg u]
  exact ⟨P, T, hPcard, hTcard, hdPT, hPT, hDP, hDT⟩

/-- The signed bipartition indicator of a cubic `K₃,₃` component is a
`-3` adjacency eigenvector, extended by zero off the component. -/
theorem adjMatrix_mulVec_K33_bipartitionSign
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (P T : Finset V) (hPcard : P.card = 3) (hTcard : T.card = 3)
    (hdPT : Disjoint P T)
    (hDP : ∀ p ∈ P, D.neighborFinset p = T)
    (hDT : ∀ t ∈ T, D.neighborFinset t = P) :
    (D.adjMatrix ℚ).mulVec
        (fun z => if z ∈ P then (1 : ℚ) else if z ∈ T then -1 else 0) =
      (-3 : ℚ) •
        (fun z => if z ∈ P then (1 : ℚ) else if z ∈ T then -1 else 0) := by
  funext z
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  by_cases hzP : z ∈ P
  · rw [hDP z hzP]
    have hsum : (∑ w ∈ T,
        (if w ∈ P then (1 : ℚ) else if w ∈ T then -1 else 0)) = -3 := by
      calc
        (∑ w ∈ T,
            (if w ∈ P then (1 : ℚ) else if w ∈ T then -1 else 0)) =
            ∑ _w ∈ T, (-1 : ℚ) := by
              apply Finset.sum_congr rfl
              intro w hw
              have hwP : w ∉ P := fun hwP =>
                Finset.disjoint_left.mp hdPT hwP hw
              simp [hwP, hw]
        _ = -3 := by simp [hTcard]
    rw [hsum]
    simp [hzP]
  · by_cases hzT : z ∈ T
    · rw [hDT z hzT]
      have hsum : (∑ w ∈ P,
          (if w ∈ P then (1 : ℚ) else if w ∈ T then -1 else 0)) = 3 := by
        calc
          (∑ w ∈ P,
              (if w ∈ P then (1 : ℚ) else if w ∈ T then -1 else 0)) =
              ∑ _w ∈ P, (1 : ℚ) := by
                apply Finset.sum_congr rfl
                intro w hw
                simp [hw]
          _ = 3 := by simp [hPcard]
      rw [hsum]
      simp [hzP, hzT]
    · have hzero : ∀ w ∈ D.neighborFinset z,
          (if w ∈ P then (1 : ℚ) else if w ∈ T then -1 else 0) = 0 := by
        intro w hw
        have hwP : w ∉ P := by
          intro hwP
          have hzw := (D.mem_neighborFinset z w).mp hw
          have hzIn : z ∈ D.neighborFinset w :=
            (D.mem_neighborFinset w z).mpr hzw.symm
          rw [hDP w hwP] at hzIn
          exact hzT hzIn
        have hwT : w ∉ T := by
          intro hwT
          have hzw := (D.mem_neighborFinset z w).mp hw
          have hzIn : z ∈ D.neighborFinset w :=
            (D.mem_neighborFinset w z).mpr hzw.symm
          rw [hDT w hwT] at hzIn
          exact hzP hzIn
        simp [hwP, hwT]
      rw [Finset.sum_congr rfl hzero]
      simp [hzP, hzT]

/-- The `-3` eigenspace supported on a named `K₃,₃` component is
one-dimensional, spanned by its signed bipartition indicator. -/
theorem negThree_eigenvector_eq_smul_K33_bipartitionSign_of_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (P T : Finset V) (hPcard : P.card = 3) (hTcard : T.card = 3)
    (hdPT : Disjoint P T)
    (hDP : ∀ p ∈ P, D.neighborFinset p = T)
    (hDT : ∀ t ∈ T, D.neighborFinset t = P)
    (v : V → ℚ)
    (hv : (D.adjMatrix ℚ).mulVec v = (-3 : ℚ) • v)
    (hsupp : ∀ z, z ∉ P ∪ T → v z = 0) :
    ∃ c : ℚ, v = c •
      (fun z => if z ∈ P then (1 : ℚ) else if z ∈ T then -1 else 0) := by
  have hPnonempty : P.Nonempty := by
    apply Finset.card_pos.mp
    omega
  have hTnonempty : T.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨p₀, hp₀⟩ := hPnonempty
  obtain ⟨t₀, ht₀⟩ := hTnonempty
  have hPconst : ∀ p ∈ P, v p = v p₀ := by
    intro p hp
    have hpEq := congrFun hv p
    have hp₀Eq := congrFun hv p₀
    rw [SimpleGraph.adjMatrix_mulVec_apply, hDP p hp] at hpEq
    rw [SimpleGraph.adjMatrix_mulVec_apply, hDP p₀ hp₀] at hp₀Eq
    simp only [Pi.smul_apply, smul_eq_mul] at hpEq hp₀Eq
    linarith
  have hTconst : ∀ t ∈ T, v t = v t₀ := by
    intro t ht
    have htEq := congrFun hv t
    have ht₀Eq := congrFun hv t₀
    rw [SimpleGraph.adjMatrix_mulVec_apply, hDT t ht] at htEq
    rw [SimpleGraph.adjMatrix_mulVec_apply, hDT t₀ ht₀] at ht₀Eq
    simp only [Pi.smul_apply, smul_eq_mul] at htEq ht₀Eq
    linarith
  have hsumT : (∑ t ∈ T, v t) = 3 * v t₀ := by
    calc
      (∑ t ∈ T, v t) = ∑ _t ∈ T, v t₀ := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hTconst t ht
      _ = 3 * v t₀ := by
        rw [Finset.sum_const, hTcard]
        norm_num
  have hsign : v t₀ = -v p₀ := by
    have hpEq := congrFun hv p₀
    rw [SimpleGraph.adjMatrix_mulVec_apply, hDP p₀ hp₀, hsumT] at hpEq
    simp only [Pi.smul_apply, smul_eq_mul] at hpEq
    linarith
  refine ⟨v p₀, ?_⟩
  funext z
  by_cases hzP : z ∈ P
  · rw [hPconst z hzP]
    simp [hzP]
  · by_cases hzT : z ∈ T
    · rw [hTconst z hzT, hsign]
      have hzNotP : z ∉ P := hzP
      simp [hzNotP, hzT]
    · have hzOut : z ∉ P ∪ T := by simp [hzP, hzT]
      rw [hsupp z hzOut]
      simp [hzP, hzT]

/-- The closed residual branch therefore supplies a concrete nonzero
`-3` defect eigenvector. -/
theorem degreeSix_thirtyFour_defectKFour_exists_nonzero_negThree_defectEigenvector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    ∃ v : V → ℚ, v ≠ 0 ∧
      v ∈ defectEigenspace
        ((secondOrderDefectGraph G).adjMatrix ℚ) (-3 : ℚ) := by
  obtain ⟨P, T, hPcard, hTcard, hdPT, _hPT, hDP, hDT⟩ :=
    degreeSix_thirtyFour_defectKFour_residual_exists_K33_partition
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  let v : V → ℚ :=
    fun z => if z ∈ P then (1 : ℚ) else if z ∈ T then -1 else 0
  have hmul := adjMatrix_mulVec_K33_bipartitionSign
    (secondOrderDefectGraph G) P T hPcard hTcard hdPT hDP hDT
  have hPnonempty : P.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨p, hp⟩ := hPnonempty
  have hvNonzero : v ≠ 0 := by
    intro hv
    have hpv := congrFun hv p
    simp [v, hp] at hpv
  refine ⟨v, hvNonzero, ?_⟩
  apply mem_defectEigenspace_iff.mpr
  exact hmul

/-- Combining the explicit residual eigenvector with quadratic parity, the
global `-3` defect eigenspace has dimension at least two.  Hence the residual
direction cannot be the only `-3` direction. -/
theorem degreeSix_thirtyFour_defectKFour_two_le_negThree_defectEigenspace_finrank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    2 ≤ Module.finrank ℚ
      (defectEigenspace
        ((secondOrderDefectGraph G).adjMatrix ℚ) (-3 : ℚ)) := by
  let E := defectEigenspace
    ((secondOrderDefectGraph G).adjMatrix ℚ) (-3 : ℚ)
  have hDreg : ∀ z, (secondOrderDefectGraph G).degree z = 3 := by
    intro z
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) z
  have heven : Even (Module.finrank ℚ E) := by
    simpa [E] using degreeSix_thirtyFour_negThree_defectEigenspace_even
      G hfree hreg hDreg
  obtain ⟨v, hvNonzero, hvE⟩ :=
    degreeSix_thirtyFour_defectKFour_exists_nonzero_negThree_defectEigenvector
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  have hsubNonzero : (⟨v, hvE⟩ : E) ≠ 0 := by
    intro h
    apply hvNonzero
    exact congrArg Subtype.val h
  letI : Nontrivial E := ⟨⟨⟨v, hvE⟩, 0, hsubNonzero⟩⟩
  have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
  rcases heven with ⟨k, hk⟩
  change 2 ≤ Module.finrank ℚ E
  omega

/-- The forced second `-3` direction cannot also be supported on the
six-vertex residual, whose supported `-3` eigenspace is one-dimensional.
Hence some `-3` eigenvector is nonzero on the complementary 28 vertices
(and, since the isolated center `K₄` has no `-3` eigenvalue, ultimately on
the 24-vertex cover layer). -/
theorem degreeSix_thirtyFour_defectKFour_exists_negThree_eigenvector_nonzero_off_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    let R := Finset.univ \ (B ∪ {a, b, x, y})
    ∃ w : defectEigenspace
        ((secondOrderDefectGraph G).adjMatrix ℚ) (-3 : ℚ),
      ∃ z, z ∉ R ∧ w.1 z ≠ 0 := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let R := Finset.univ \ (B ∪ {a, b, x, y})
  let E := defectEigenspace
    ((secondOrderDefectGraph G).adjMatrix ℚ) (-3 : ℚ)
  obtain ⟨P, T, hPcard, hTcard, hdPT, hPT, hDP, hDT⟩ :=
    degreeSix_thirtyFour_defectKFour_residual_exists_K33_partition
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  let sign : V → ℚ :=
    fun z => if z ∈ P then (1 : ℚ) else if z ∈ T then -1 else 0
  have hsignMul := adjMatrix_mulVec_K33_bipartitionSign
    (secondOrderDefectGraph G) P T hPcard hTcard hdPT hDP hDT
  have hsignE : sign ∈ E := by
    apply mem_defectEigenspace_iff.mpr
    exact hsignMul
  let e : E := ⟨sign, hsignE⟩
  have hPnonempty : P.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨p, hp⟩ := hPnonempty
  have heNonzero : e ≠ 0 := by
    intro he
    have hpv := congrFun (congrArg Subtype.val he) p
    simp [e, sign, hp] at hpv
  have hfin : 2 ≤ Module.finrank ℚ E := by
    simpa [E] using
      degreeSix_thirtyFour_defectKFour_two_le_negThree_defectEigenspace_finrank
        G hfree hreg hcard hab hax hbx hay hby hxy hzero
  dsimp only
  by_contra hnone
  push Not at hnone
  have hall : ∀ w : E, w ∈ ℚ ∙ e := by
    intro w
    have hwEig : ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec w.1 =
        (-3 : ℚ) • w.1 := mem_defectEigenspace_iff.mp w.2
    have hwSupp : ∀ z, z ∉ P ∪ T → w.1 z = 0 := by
      intro z hz
      have hzR : z ∉ R := by
        intro hzR
        exact hz (by rwa [hPT])
      exact hnone w z hzR
    obtain ⟨c, hc⟩ :=
      negThree_eigenvector_eq_smul_K33_bipartitionSign_of_support
        (secondOrderDefectGraph G) P T hPcard hTcard hdPT hDP hDT
          w.1 hwEig hwSupp
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa [e, sign] using hc.symm
  have htop : ℚ ∙ e = ⊤ := eq_top_iff.mpr (by
    intro w _hw
    exact hall w)
  have hfinOne : Module.finrank ℚ E = 1 := by
    have hf := finrank_span_singleton (K := ℚ) (V := E) heNonzero
    rw [htop, finrank_top] at hf
    exact hf
  omega

/-- A `-3` eigenvector vanishes on an isolated cubic `K₄`, since `-3` is
not an eigenvalue of `K₄`. -/
theorem negThree_eigenvector_zero_on_cubicKFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hregD : ∀ z, D.degree z = 3)
    {a b x y : V}
    (hab : D.Adj a b) (hax : D.Adj a x) (hbx : D.Adj b x)
    (hay : D.Adj a y) (hby : D.Adj b y) (hxy : D.Adj x y)
    (v : V → ℚ) (hv : (D.adjMatrix ℚ).mulVec v = (-3 : ℚ) • v) :
    v a = 0 ∧ v b = 0 ∧ v x = 0 ∧ v y = 0 := by
  rcases cubic_defectKFour_neighborFinsets D hregD
      hab hax hbx hay hby hxy with ⟨hKa, hKb, hKx, hKy⟩
  have ha := congrFun hv a
  have hb := congrFun hv b
  have hx := congrFun hv x
  have hy := congrFun hv y
  rw [SimpleGraph.adjMatrix_mulVec_apply, hKa] at ha
  rw [SimpleGraph.adjMatrix_mulVec_apply, hKb] at hb
  rw [SimpleGraph.adjMatrix_mulVec_apply, hKx] at hx
  rw [SimpleGraph.adjMatrix_mulVec_apply, hKy] at hy
  have habNe := D.ne_of_adj hab
  have haxNe := D.ne_of_adj hax
  have hbxNe := D.ne_of_adj hbx
  have hayNe := D.ne_of_adj hay
  have hbyNe := D.ne_of_adj hby
  have hxyNe := D.ne_of_adj hxy
  simp [habNe, haxNe, hbxNe, hayNe, hbyNe, hxyNe] at ha hb hx hy
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Commutation makes the original adjacency image of a defect `-3`
eigenvector another defect `-3` eigenvector.  Since such a vector vanishes
on an isolated cubic defect `K₄`, the original-neighborhood sum of the
starting vector is zero at each of the four centers. -/
theorem negThree_eigenvector_centerBlock_sums_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hregD : ∀ z, (secondOrderDefectGraph G).degree z = 3)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (v : V → ℚ)
    (hv : ((secondOrderDefectGraph G).adjMatrix ℚ).mulVec v =
      (-3 : ℚ) • v) :
    (∑ z ∈ G.neighborFinset a, v z) = 0 ∧
      (∑ z ∈ G.neighborFinset b, v z) = 0 ∧
      (∑ z ∈ G.neighborFinset x, v z) = 0 ∧
      (∑ z ∈ G.neighborFinset y, v z) = 0 := by
  let A := G.adjMatrix ℚ
  let D := (secondOrderDefectGraph G).adjMatrix ℚ
  let f := A.mulVec v
  have hcomm : A * D = D * A :=
    adjMatrix_comm_secondOrderDefect_of_regular_rat G hfree hreg
  have hf : D.mulVec f = (-3 : ℚ) • f := by
    change D.mulVec (A.mulVec v) = _
    rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_smul]
  have hfzero := negThree_eigenvector_zero_on_cubicKFour
    (secondOrderDefectGraph G) hregD hab hax hbx hay hby hxy f hf
  have hfa : f a = ∑ z ∈ G.neighborFinset a, v z := by
    change (G.adjMatrix ℚ).mulVec v a = _
    rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hfb : f b = ∑ z ∈ G.neighborFinset b, v z := by
    change (G.adjMatrix ℚ).mulVec v b = _
    rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hfx : f x = ∑ z ∈ G.neighborFinset x, v z := by
    change (G.adjMatrix ℚ).mulVec v x = _
    rw [SimpleGraph.adjMatrix_mulVec_apply]
  have hfy : f y = ∑ z ∈ G.neighborFinset y, v z := by
    change (G.adjMatrix ℚ).mulVec v y = _
    rw [SimpleGraph.adjMatrix_mulVec_apply]
  rw [hfa] at hfzero
  rw [hfb] at hfzero
  rw [hfx] at hfzero
  rw [hfy] at hfzero
  exact hfzero

/-- At a vertex where the absolute value of a `-3` eigenvector is at least
that at every neighbor of a cubic graph, all three neighboring values have
the opposite sign and the same magnitude.  This is the equality case in the
bottom-eigenvalue bound for a cubic graph. -/
theorem negThree_eigenvector_neighbor_eq_neg_of_local_abs_max
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hregD : ∀ z, D.degree z = 3)
    (v : V → ℚ) (hv : (D.adjMatrix ℚ).mulVec v = (-3 : ℚ) • v)
    {a : V}
    (hmax : ∀ b, D.Adj a b → |v b| ≤ |v a|) :
    ∀ b, D.Adj a b → v b = -v a := by
  intro b hab
  have hsum : (∑ u ∈ D.neighborFinset a, v u) = -3 * v a := by
    have ha := congrFun hv a
    rw [SimpleGraph.adjMatrix_mulVec_apply] at ha
    simpa only [Pi.smul_apply, smul_eq_mul] using ha
  have hcard : (D.neighborFinset a).card = 3 := by
    rw [D.card_neighborFinset_eq_degree, hregD a]
  by_cases hva : 0 ≤ v a
  · have hlower : ∀ u ∈ D.neighborFinset a, -v a ≤ v u := by
      intro u hu
      have huAbs := hmax u ((D.mem_neighborFinset a u).mp hu)
      rw [abs_of_nonneg hva] at huAbs
      exact (abs_le.mp huAbs).1
    by_contra hne
    have hstrict : -v a < v b := lt_of_le_of_ne
      (hlower b ((D.mem_neighborFinset a b).mpr hab)) (Ne.symm hne)
    have hlt : (∑ _u ∈ D.neighborFinset a, -v a) <
        ∑ u ∈ D.neighborFinset a, v u :=
      Finset.sum_lt_sum hlower
        ⟨b, (D.mem_neighborFinset a b).mpr hab, hstrict⟩
    rw [Finset.sum_const, hcard, nsmul_eq_mul, hsum] at hlt
    norm_num at hlt
  · have hvaNeg : v a ≤ 0 := le_of_lt (lt_of_not_ge hva)
    have hupper : ∀ u ∈ D.neighborFinset a, v u ≤ -v a := by
      intro u hu
      have huAbs := hmax u ((D.mem_neighborFinset a u).mp hu)
      rw [abs_of_nonpos hvaNeg] at huAbs
      exact (abs_le.mp huAbs).2
    by_contra hne
    have hstrict : v b < -v a := lt_of_le_of_ne
      (hupper b ((D.mem_neighborFinset a b).mpr hab)) hne
    have hlt : (∑ u ∈ D.neighborFinset a, v u) <
        ∑ _u ∈ D.neighborFinset a, -v a :=
      Finset.sum_lt_sum hupper
        ⟨b, (D.mem_neighborFinset a b).mpr hab, hstrict⟩
    rw [Finset.sum_const, hcard, nsmul_eq_mul, hsum] at hlt
    norm_num at hlt

/-- Every edge in a cubic graph reverses a rational eigenvector for the
bottom eigenvalue `-3`.  The proof chooses an absolute-value maximum in the
edge's connected component and propagates the equality case along a walk. -/
theorem negThree_eigenvector_eq_neg_of_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hregD : ∀ z, D.degree z = 3)
    (v : V → ℚ) (hv : (D.adjMatrix ℚ).mulVec v = (-3 : ℚ) • v)
    {a b : V} (hab : D.Adj a b) :
    v b = -v a := by
  let s : Finset V := Finset.univ.filter (fun z => D.Reachable a z)
  have has : a ∈ s := by simp [s]
  obtain ⟨x, hxS, hxMax⟩ :=
    Finset.exists_max_image s (fun z => |v z|) ⟨a, has⟩
  have hxReach : D.Reachable a x := by
    simpa [s] using hxS
  have hbound : ∀ z, D.Reachable a z → |v z| ≤ |v x| := by
    intro z hz
    apply hxMax z
    simp [s, hz]
  have hwalk : ∀ (c d : V) (p : D.Walk c d),
      D.Reachable a c → |v c| = |v x| → |v d| = |v x| := by
    intro c d p
    induction p with
    | nil => exact fun _ hc => hc
    | @cons c e d hce q ih =>
        intro hcReach hcAbs
        have hcLocal : ∀ u, D.Adj c u → |v u| ≤ |v c| := by
          intro u hcu
          rw [hcAbs]
          exact hbound u (hcReach.trans hcu.reachable)
        have heFlip : v e = -v c :=
          negThree_eigenvector_neighbor_eq_neg_of_local_abs_max
            D hregD v hv hcLocal e hce
        have heAbs : |v e| = |v x| := by
          rw [heFlip, abs_neg, hcAbs]
        exact ih (hcReach.trans hce.reachable) heAbs
  have haAbs : |v a| = |v x| := by
    obtain ⟨p⟩ := hxReach.symm
    exact hwalk x a p hxReach rfl
  apply negThree_eigenvector_neighbor_eq_neg_of_local_abs_max
    D hregD v hv
  · intro z haz
    rw [haAbs]
    exact hbound z haz.reachable
  · exact hab

/-- The extra `-3` direction forced by parity is genuinely visible on the
24-vertex cover layer. -/
theorem degreeSix_thirtyFour_defectKFour_exists_negThree_eigenvector_nonzero_on_blockLayer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    ∃ w : defectEigenspace
        ((secondOrderDefectGraph G).adjMatrix ℚ) (-3 : ℚ),
      ∃ z ∈ B, w.1 z ≠ 0 := by
  let B := G.neighborFinset a ∪ G.neighborFinset b ∪
    G.neighborFinset x ∪ G.neighborFinset y
  let Q : Finset V := {a, b, x, y}
  let R := Finset.univ \ (B ∪ Q)
  obtain ⟨w, z, hzNotR, hwz⟩ :=
    degreeSix_thirtyFour_defectKFour_exists_negThree_eigenvector_nonzero_off_residual
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  have hDreg : ∀ q, (secondOrderDefectGraph G).degree q = 3 := by
    intro q
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) q
  have hcenterZero := negThree_eigenvector_zero_on_cubicKFour
    (secondOrderDefectGraph G) hDreg hab hax hbx hay hby hxy w.1
      (mem_defectEigenspace_iff.mp w.2)
  have hzU : z ∈ B ∪ Q := by
    by_contra hzU
    exact hzNotR (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hzU⟩)
  rcases Finset.mem_union.mp hzU with hzB | hzQ
  · exact ⟨w, z, hzB, hwz⟩
  · exfalso
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hzQ
    rcases hzQ with hza | hzb | hzx | hzy
    · exact hwz (hza ▸ hcenterZero.1)
    · exact hwz (hzb ▸ hcenterZero.2.1)
    · exact hwz (hzx ▸ hcenterZero.2.2.1)
    · exact hwz (hzy ▸ hcenterZero.2.2.2)

/-- In the closed defect-`K₄` branch there is a nonzero alternating defect
eigenvector visible on the 24-vertex cover layer: its value reverses across
every defect edge. -/
theorem degreeSix_thirtyFour_defectKFour_exists_alternating_vector_on_blockLayer
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    ∃ w : defectEigenspace
        ((secondOrderDefectGraph G).adjMatrix ℚ) (-3 : ℚ),
      ∃ z ∈ B, w.1 z ≠ 0 ∧
        ∀ u v, (secondOrderDefectGraph G).Adj u v → w.1 v = -w.1 u := by
  obtain ⟨w, z, hzB, hwz⟩ :=
    degreeSix_thirtyFour_defectKFour_exists_negThree_eigenvector_nonzero_on_blockLayer
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  have hDreg : ∀ q, (secondOrderDefectGraph G).degree q = 3 := by
    intro q
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) q
  refine ⟨w, z, hzB, hwz, ?_⟩
  intro u v huv
  exact negThree_eigenvector_eq_neg_of_adj
    (secondOrderDefectGraph G) hDreg w.1
      (mem_defectEigenspace_iff.mp w.2) huv

/-- The alternating cover-layer vector can be chosen with zero signed sum
on every one of the four six-element fibers.  These four balance equations
are forced by commutation and the absence of `-3` on the center `K₄`. -/
theorem degreeSix_thirtyFour_defectKFour_exists_balanced_alternating_vector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ z, G.degree z = 6)
    (hcard : Fintype.card V = 34)
    {a b x y : V}
    (hab : (secondOrderDefectGraph G).Adj a b)
    (hax : (secondOrderDefectGraph G).Adj a x)
    (hbx : (secondOrderDefectGraph G).Adj b x)
    (hay : (secondOrderDefectGraph G).Adj a y)
    (hby : (secondOrderDefectGraph G).Adj b y)
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hzero : (Finset.univ.filter fun z : V =>
      (triangleFreeEdgeGraph G).degree z = 2).card = 0) :
    let B := G.neighborFinset a ∪ G.neighborFinset b ∪
      G.neighborFinset x ∪ G.neighborFinset y
    ∃ w : defectEigenspace
        ((secondOrderDefectGraph G).adjMatrix ℚ) (-3 : ℚ),
      (∃ z ∈ B, w.1 z ≠ 0) ∧
      (∀ u v, (secondOrderDefectGraph G).Adj u v → w.1 v = -w.1 u) ∧
      (∑ z ∈ G.neighborFinset a, w.1 z) = 0 ∧
      (∑ z ∈ G.neighborFinset b, w.1 z) = 0 ∧
      (∑ z ∈ G.neighborFinset x, w.1 z) = 0 ∧
      (∑ z ∈ G.neighborFinset y, w.1 z) = 0 := by
  obtain ⟨w, z, hzB, hwz, halt⟩ :=
    degreeSix_thirtyFour_defectKFour_exists_alternating_vector_on_blockLayer
      G hfree hreg hcard hab hax hbx hay hby hxy hzero
  have hDreg : ∀ q, (secondOrderDefectGraph G).degree q = 3 := by
    intro q
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) q
  have hbal := negThree_eigenvector_centerBlock_sums_zero
    G hfree hreg hDreg hab hax hbx hay hby hxy w.1
      (mem_defectEigenspace_iff.mp w.2)
  exact ⟨w, ⟨z, hzB, hwz⟩, halt, hbal⟩

end

end Erdos85
