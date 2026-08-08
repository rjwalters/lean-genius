import Proofs.Erdos85GlobalCycleFactorization
import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic

/-!
# Color-sensitive traces for the even second-order defect graph

The uncolored defect two-factor controls `A^2`, but its two colors retain
additional information: antipodal defect edges are nonedges of the original
graph, whereas triangle-free defect edges are original edges.  The mixed
trace `tr(A D)` detects exactly the latter color.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A `C₄`-free graph has edge-disjoint triangles.  This is the exact
combinatorial content needed when the cubic adjacency trace is interpreted as
six oriented copies of every triangle. -/
theorem edgeDisjointTriangles_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) :
    G.EdgeDisjointTriangles := by
  rw [edgeDisjointTriangles_iff_mem_sym2_subsingleton, Sym2.forall]
  intro x y hxy
  simp only [Sym2.mk_isDiag_iff] at hxy
  have hdesc :
      {s ∈ (G.cliqueSet 3 : Set (Finset V)) |
          s(x, y) ∈ (s : Finset V).sym2} =
        {s | G.Adj x y ∧ ∃ z, G.Adj x z ∧ G.Adj y z ∧
          s = {x, y, z}} := by
    ext s
    simp only [Finset.mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp,
      forall_eq, mem_cliqueSet_iff, Set.mem_setOf_eq, is3Clique_iff]
    constructor
    · rintro ⟨⟨a, b, c, hab, hac, hbc, rfl⟩, hmem⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      obtain ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ := hmem
      any_goals simp only [*, adj_comm, true_and, Ne, not_true] at *
      any_goals
        first
        | exact ⟨a, by aesop⟩
        | exact ⟨b, by aesop⟩
        | exact ⟨c, by aesop⟩
        | simp only [*, true_and] at *; exact ⟨a, by aesop⟩
        | simp only [*, true_and] at *; exact ⟨b, by aesop⟩
        | simp only [*, true_and] at *; exact ⟨c, by aesop⟩
    · rintro ⟨hxy', z, hxz, hyz, rfl⟩
      refine ⟨⟨x, y, z, ?_⟩, ?_⟩ <;> simp [*]
  rw [hdesc]
  rintro _ ⟨hxy', z, hxz, hyz, rfl⟩ _ ⟨_, w, hxw, hyw, rfl⟩
  have hz : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by simp [hxz, hyz]
  have hw : w ∈ G.neighborFinset x ∩ G.neighborFinset y := by simp [hxw, hyw]
  have hcard := common_le_one_of_not_containsC4 hfree x y hxy
  rw [Finset.card_le_one] at hcard
  rw [hcard z hz w hw]

/-- Delete precisely the edges lying in no triangle. -/
def triangularEdgeGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph V :=
  G \ triangleFreeEdgeGraph G

theorem triangularEdgeGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) :
    (triangularEdgeGraph G).Adj x y ↔
      G.Adj x y ∧
        (G.neighborFinset x ∩ G.neighborFinset y).card ≠ 0 := by
  constructor
  · intro h
    have hs := (sdiff_adj G (triangleFreeEdgeGraph G) x y).mp h
    refine ⟨hs.1, ?_⟩
    intro hzero
    exact hs.2 ((triangleFreeEdgeGraph_adj G x y).mpr
      ((mem_triangleFreeNeighbors G x y).mpr ⟨hs.1, hzero⟩))
  · rintro ⟨hxy, hnonzero⟩
    apply (sdiff_adj G (triangleFreeEdgeGraph G) x y).mpr
    refine ⟨hxy, ?_⟩
    intro htf
    exact hnonzero ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp htf)).2

/-- In a `C₄`-free graph, the subgraph of edges lying in triangles is locally
linear: every retained edge lies in exactly one triangle. -/
theorem triangularEdgeGraph_locallyLinear_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    (triangularEdgeGraph G).LocallyLinear := by
  constructor
  · exact (edgeDisjointTriangles_of_not_containsC4 G hfree).mono
      (by intro x y h; exact (triangularEdgeGraph_adj G x y).mp h |>.1)
  · intro x y hxy
    have hxyH : (triangularEdgeGraph G).Adj x y := hxy
    rw [triangularEdgeGraph_adj] at hxy
    have hnonempty :
        (G.neighborFinset x ∩ G.neighborFinset y).Nonempty :=
      Finset.card_ne_zero.mp hxy.2
    obtain ⟨z, hz⟩ := hnonempty
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz
    have hxz : (triangularEdgeGraph G).Adj x z := by
      rw [triangularEdgeGraph_adj]
      refine ⟨hz.1, Finset.card_ne_zero.mpr ⟨y, ?_⟩⟩
      simp [hxy.1, hz.2.symm]
    have hyz : (triangularEdgeGraph G).Adj y z := by
      rw [triangularEdgeGraph_adj]
      refine ⟨hz.2, Finset.card_ne_zero.mpr ⟨x, ?_⟩⟩
      simp [hxy.1.symm, hz.1.symm]
    exact ⟨{x, y, z}, is3Clique_triple_iff.mpr ⟨hxyH, hxz, hyz⟩,
      by simp, by simp⟩

/-- Arithmetic form of the cubic color congruence.  If `T` is the number of
triangles and `s` the total order of triangle-free defect components, then
`6T+2s=nd` implies `s ≡ n(d/2) (mod 3)` for even `d`. -/
theorem colorOrder_mod_three_of_triangle_partition
    {n d T s : ℕ} (heven : Even d)
    (hpartition : 6 * T + 2 * s = n * d) :
    s % 3 = (n * (d / 2)) % 3 := by
  obtain ⟨e, rfl⟩ := heven
  have hleft : 6 * T + 2 * s = 2 * (3 * T + s) := by ring
  have hright : n * (e + e) = 2 * (n * e) := by ring
  rw [hleft, hright] at hpartition
  have heq : 3 * T + s = n * e :=
    Nat.mul_left_cancel (by decide : 0 < 2) hpartition
  rw [show (e + e) / 2 = e by omega]
  calc
    s % 3 = (3 * T + s) % 3 := by simp [Nat.add_mod, Nat.mul_mod]
    _ = (n * e) % 3 := congrArg (· % 3) heq

/-- In degree six the correct color target is zero modulo three. -/
theorem degreeSix_colorOrder_mod_three
    {n T s : ℕ} (hpartition : 6 * T + 2 * s = n * 6) :
    s % 3 = 0 := by
  have h := colorOrder_mod_three_of_triangle_partition
    (n := n) (d := 6) (T := T) (s := s) (by norm_num) hpartition
  simpa using h

/-- The mixed trace of the original adjacency matrix with the second-order
defect matrix is the total degree of the triangle-free-edge summand.  The
antipodal summand contributes zero because all of its edges are nonedges of
the original graph. -/
theorem trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix.trace (G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) =
      ∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  change (G.adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) x x = _
  rw [(secondOrderDefectGraph G).mul_adjMatrix_apply,
    secondOrderDefectGraph_neighborFinset G x,
    Finset.sum_union (disjoint_antipodal_triangleFreeNeighbors G x)]
  have hanti : ∑ z ∈ antipodalNeighbors G x, G.adjMatrix ℤ x z = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    rw [SimpleGraph.adjMatrix_apply, if_neg]
    exact ((mem_antipodalNeighbors G x z).mp hz).2.1
  rw [hanti, zero_add]
  calc
    (∑ z ∈ triangleFreeNeighbors G x, G.adjMatrix ℤ x z) =
        ∑ _z ∈ triangleFreeNeighbors G x, (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [SimpleGraph.adjMatrix_apply, if_pos]
      exact ((mem_triangleFreeNeighbors G x z).mp hz).1
    _ = ((triangleFreeNeighbors G x).card : ℤ) := by simp
    _ = ((triangleFreeEdgeGraph G).degree x : ℤ) := by
      rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
        triangleFreeEdgeGraph_neighborFinset]

/-- In the even second-order template every vertex has triangle-free defect
degree either zero or two.  Thus the mixed trace is an explicitly colored
vertex count, with weight two on the triangle-free-cycle components. -/
theorem trace_adjMatrix_mul_secondOrderDefect_eq_two_mul_filter_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    Matrix.trace (G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) =
      2 * ((Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) := by
  rw [trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees]
  calc
    (∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ)) =
        ∑ x : V, if (triangleFreeEdgeGraph G).degree x = 2
          then (2 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rcases secondOrder_defect_local_monochromatic
          G hfree hd heven hmin hcard x with h | h
      · have hzero : (triangleFreeEdgeGraph G).degree x = 2 := by
          rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
            triangleFreeEdgeGraph_neighborFinset]
          exact h.2
        simp [hzero]
      · have hzero : (triangleFreeEdgeGraph G).degree x = 0 := by
          rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
            triangleFreeEdgeGraph_neighborFinset]
          exact h.2
        simp [hzero]
    _ = 2 * ((Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 2).card : ℤ) := by
      rw [← Finset.sum_filter]
      simp
      ring

/-- The graph-theoretic triangle/color partition behind the cubic trace.
For an even second-order Moore template, twice the three-edges-per-triangle
count plus twice the number of triangle-free defect edges accounts for every
oriented edge.  The colored vertex count equals the latter edge count because
that summand is a disjoint union of cycles. -/
theorem six_mul_triangularCliqueCount_add_two_mul_colorOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    6 * ((triangularEdgeGraph G).cliqueFinset 3).card +
        2 * ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 2).card) =
      Fintype.card V * d := by
  let H := triangularEdgeGraph G
  let T := triangleFreeEdgeGraph G
  let s := (Finset.univ.filter fun x : V => T.degree x = 2).card
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
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
        rcases secondOrder_defect_local_monochromatic
            G hfree hd heven hmin hcard x with h | h
        · have htwo : (triangleFreeEdgeGraph G).degree x = 2 := by
            rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
              triangleFreeEdgeGraph_neighborFinset]
            exact h.2
          simp [htwo]
        · have hzero : (triangleFreeEdgeGraph G).degree x = 0 := by
            rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
              triangleFreeEdgeGraph_neighborFinset]
            exact h.2
          simp [hzero]
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

/-- The corrected color congruence as an actual graph theorem (rather than an
arithmetic implication with the triangle partition supplied as a premise). -/
theorem secondOrder_colorOrder_mod_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    ((Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 2).card) % 3 =
      (Fintype.card V * (d / 2)) % 3 := by
  apply colorOrder_mod_three_of_triangle_partition heven
  exact six_mul_triangularCliqueCount_add_two_mul_colorOrder
    G hfree hd heven hmin hcard

/-- In degree six, the total order of the triangle-free-colored defect cycles
is divisible by three. -/
theorem degreeSix_secondOrder_colorOrder_mod_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : 6 ≤ G.minDegree)
    (hcard : Fintype.card V = 6 * (6 - 1) + 3) :
    ((Finset.univ.filter fun x : V =>
        (triangleFreeEdgeGraph G).degree x = 2).card) % 3 = 0 := by
  simpa using secondOrder_colorOrder_mod_three
    G hfree (d := 6) (by norm_num) (by norm_num) hmin hcard

/-- The first genuinely color-sensitive cubic identity.  In the even
second-order template, every oriented edge is accounted for either by a
triangle (the `A³` term) or by a triangle-free defect edge (the `AD` term).
The matrix equation proves the partition without choosing triangles. -/
theorem trace_adjMatrix_cube_add_colorTrace_eq_card_mul_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    Matrix.trace
        (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) +
      Matrix.trace (G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) =
      (Fintype.card V : ℤ) * d := by
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let C := (↑d - 1 : ℤ) • (1 : Matrix V V ℤ)
  have hsq : A * A = C + J - D :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_even
      G hfree hd heven hmin hcard
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hJA : J * A = (d : ℤ) • J :=
    onesMatrix_mul_adjMatrix_of_regular G d hreg
  have hcube : A * A * A = C * A + (d : ℤ) • J - D * A := by
    rw [hsq, sub_mul, add_mul, hJA]
  change Matrix.trace (A * A * A) + Matrix.trace (A * D) = _
  rw [hcube, Matrix.trace_sub, Matrix.trace_add]
  have htraceA : Matrix.trace A = 0 := by
    change Matrix.trace (G.adjMatrix ℤ) = 0
    exact SimpleGraph.trace_adjMatrix ℤ G
  have hCA : Matrix.trace (C * A) = 0 := by
    simp only [C, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
      htraceA, smul_zero]
  rw [hCA, zero_add, Matrix.trace_smul]
  rw [Matrix.trace_mul_comm D A]
  have htraceJ : Matrix.trace J = (Fintype.card V : ℤ) := by
    exact FriendshipTheoremOQ01.trace_onesMatrix
  rw [htraceJ]
  ring

end

end Erdos85
