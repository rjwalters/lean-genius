import Proofs.Erdos85GadgetExtension
import Proofs.Erdos85DistanceLayers

/-!
# A 32-vertex witness for Erdős Problem 85

An exhaustive search through the exact gadget budgets found the following
construction.  Start with the order-five orthogonal polarity graph, delete
four absolute points, and attach a five-cycle.  Each cycle vertex has three
old neighbours.  The explicit edge list below is the resulting certificate;
the common-neighbour matrix is checked directly.
-/

namespace Erdos85

open SimpleGraph

def polarityCycle32Edges : List (Fin 32 × Fin 32) :=
  [(0,1), (0,4), (0,7), (0,12), (0,17), (0,22),
   (1,4), (1,5), (1,6), (2,3), (2,4), (2,11), (2,15), (2,19), (2,23),
   (3,4), (3,8), (3,14), (3,20), (3,26),
   (5,6), (5,11), (5,16), (5,21), (5,26),
   (6,8), (6,13), (6,18), (6,23),
   (7,22), (7,23), (7,24), (7,25), (7,26),
   (8,10), (8,14), (8,18), (8,22),
   (9,11), (9,13), (9,20), (9,22),
   (10,16), (10,19), (10,22),
   (11,15), (11,21), (11,22),
   (12,13), (12,14), (12,15), (12,16),
   (13,20), (13,23), (14,21), (14,25),
   (15,18), (15,24), (16,19), (16,26),
   (17,18), (17,19), (17,20), (17,21),
   (18,24), (19,23), (20,26), (21,25), (23,25), (24,26),
   -- The attached five-cycle on vertices 27,...,31.
   (27,30), (27,31), (28,29), (28,31), (29,30),
   -- Its five three-element old-neighbour selectors.
   (1,27), (14,27), (9,27),
   (25,28), (4,28), (18,28),
   (20,29), (25,29), (10,29),
   (1,30), (24,30), (10,30),
   (16,31), (9,31), (18,31)]

/-- The delete-four/add-five polarity-cycle witness. -/
def polarityCycle32 : SimpleGraph (Fin 32) where
  Adj i j := (i, j) ∈ polarityCycle32Edges ∨ (j, i) ∈ polarityCycle32Edges
  symm.symm := fun _ _ h => Or.symm h
  loopless.irrefl := by native_decide

instance : DecidableRel polarityCycle32.Adj := fun i j =>
  decidable_of_iff
    ((i, j) ∈ polarityCycle32Edges ∨ (j, i) ∈ polarityCycle32Edges) Iff.rfl

/-- Every vertex has degree at least five (in fact the degree sequence consists
of degrees five, six, and one degree seven). -/
theorem polarityCycle32_five_le_degree :
    ∀ v : Fin 32, 5 ≤ polarityCycle32.degree v := by native_decide

/-- Every distinct pair has at most one common neighbour. -/
theorem polarityCycle32_common_le_one :
    ∀ x y : Fin 32, x ≠ y →
      (polarityCycle32.neighborFinset x ∩
        polarityCycle32.neighborFinset y).card ≤ 1 := by native_decide

theorem polarityCycle32_not_containsC4 :
    ¬ containsC4 (Fin 32) polarityCycle32 :=
  not_containsC4_of_forall_common_le_one polarityCycle32_common_le_one

theorem polarityCycle32_five_le_minDegree :
    5 ≤ polarityCycle32.minDegree := by
  apply SimpleGraph.le_minDegree_of_forall_le_degree
  exact polarityCycle32_five_le_degree

/-- Any hypothetical `C₄`-free graph on 32 vertices with minimum degree six
is forced to be exactly 6-regular.  A degree-seven vertex would already have
at least `1 + 7 + 7(6-2) = 36` vertices in its first two distance layers. -/
theorem degree_eq_six_of_thirtytwo_minDegree_six
    (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 32) G) (hmin : 6 ≤ G.minDegree) :
    ∀ v : Fin 32, G.degree v = 6 := by
  intro v
  have hlower : 6 ≤ G.degree v :=
    le_trans hmin (G.minDegree_le_degree v)
  have hmoore := one_add_degree_add_mul_sub_two_le_card_of_minDegree
    G hfree hmin v
  norm_num at hmoore
  omega

/-- In the same hypothetical graph, every edge lies in exactly one triangle.
Equivalently, adjacent vertices have exactly one common neighbour. -/
theorem card_common_eq_one_of_thirtytwo_minDegree_six
    (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 32) G) (hmin : 6 ≤ G.minDegree)
    {x y : Fin 32} (hxy : G.Adj x y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
  classical
  have hreg := degree_eq_six_of_thirtytwo_minDegree_six G hfree hmin
  let I := {z : Fin 32 // z ∈ G.neighborSet x}
  let L := G.induce (G.neighborSet x)
  let c : I → ℕ := fun z =>
    (G.neighborFinset x ∩ G.neighborFinset z.1).card
  have hIcard : Fintype.card I = 6 := by
    change Fintype.card {z : Fin 32 // z ∈ G.neighborSet x} = 6
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
        G.neighborFinset x := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hreg x]
  have hbranchsum :
      (secondLayer G x).card + (∑ z : I, c z) = 30 := by
    have hdisj := secondLayerBranch_pairwiseDisjoint G hfree x
    have hpoint : ∀ z : I,
        (secondLayerBranch G x z).card + c z + 1 = 6 := by
      intro z
      simpa [c, I, hreg z.1] using
        card_secondLayerBranch_add_common_add_one G x z
    have hsum := Finset.sum_congr rfl (fun z (_ : z ∈ (Finset.univ : Finset I)) =>
      hpoint z)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    simp [hIcard] at hsum
    rw [secondLayer, Finset.card_biUnion hdisj]
    omega
  have hsecondUpper : (secondLayer G x).card ≤ 25 := by
    let C : Finset (Fin 32) := insert x (G.neighborFinset x)
    have hCD : Disjoint C (secondLayer G x) := by
      rw [Finset.disjoint_left]
      intro z hzC hzD
      rw [secondLayer, Finset.mem_biUnion] at hzD
      obtain ⟨w, _, hzw⟩ := hzD
      exact (Finset.mem_sdiff.mp hzw).2 hzC
    have hu := Finset.card_le_univ (C ∪ secondLayer G x)
    rw [Finset.card_union_of_disjoint hCD] at hu
    have hC : C.card = 7 := by
      change (insert x (G.neighborFinset x)).card = 7
      rw [Finset.card_insert_of_notMem]
      · rw [G.card_neighborFinset_eq_degree, hreg x]
      · simp
    norm_num [hC] at hu
    omega
  have hsumLower : 5 ≤ ∑ z : I, c z := by omega
  have hc_le : ∀ z : I, c z ≤ 1 := by
    intro z
    exact common_le_one_of_not_containsC4 hfree x z.1
      (G.ne_of_adj z.2)
  have hsumUpper : (∑ z : I, c z) ≤ 6 := by
    calc
      (∑ z : I, c z) ≤ ∑ _z : I, 1 := Finset.sum_le_sum fun z _ => hc_le z
      _ = 6 := by simp [hIcard]
  have hsumEven : Even (∑ z : I, c z) := by
    have hdegrees : (∑ z : I, c z) = ∑ z : I, L.degree z := by
      apply Finset.sum_congr rfl
      intro z _
      simpa [c, I, L] using
        (degree_induce_neighborSet_eq_card_common G x z).symm
    rw [hdegrees, L.sum_degrees_eq_twice_card_edges]
    exact ⟨L.edgeFinset.card, by omega⟩
  have hsumEq : (∑ z : I, c z) = 6 := by
    obtain ⟨k, hk⟩ := hsumEven
    omega
  let yy : I := ⟨y, hxy⟩
  have hcy : c yy ≤ 1 := hc_le yy
  by_contra hne
  have hcyne : c yy ≠ 1 := by simpa [c, yy] using hne
  have hcy0 : c yy = 0 := by omega
  have herase : (∑ z ∈ (Finset.univ.erase yy : Finset I), c z) ≤ 5 := by
    calc
      (∑ z ∈ (Finset.univ.erase yy : Finset I), c z) ≤
          ∑ _z ∈ (Finset.univ.erase yy : Finset I), 1 :=
        Finset.sum_le_sum fun z _ => hc_le z
      _ = 5 := by simp [hIcard]
  have hsplit := Finset.sum_erase_add (s := (Finset.univ : Finset I))
    (f := c) (Finset.mem_univ yy)
  change (∑ z ∈ (Finset.univ.erase yy : Finset I), c z) + c yy =
      ∑ z : I, c z at hsplit
  omega

/-- The second distance layer around every vertex has exactly 24 vertices. -/
theorem card_secondLayer_eq_twentyfour_of_thirtytwo_minDegree_six
    (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 32) G) (hmin : 6 ≤ G.minDegree)
    (x : Fin 32) :
    (secondLayer G x).card = 24 := by
  classical
  have hreg := degree_eq_six_of_thirtytwo_minDegree_six G hfree hmin
  have hdisj := secondLayerBranch_pairwiseDisjoint G hfree x
  rw [secondLayer, Finset.card_biUnion hdisj]
  have hbranch : ∀ y : {z : Fin 32 // z ∈ G.neighborSet x},
      (secondLayerBranch G x y).card = 4 := by
    intro y
    have hcount := card_secondLayerBranch_add_common_add_one G x y
    have hcommon := card_common_eq_one_of_thirtytwo_minDegree_six
      G hfree hmin y.2
    rw [hreg y.1, hcommon] at hcount
    omega
  simp_rw [hbranch]
  have hcard : Fintype.card {z : Fin 32 // z ∈ G.neighborSet x} = 6 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
        G.neighborFinset x := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hreg x]
  rw [Finset.sum_const, Finset.card_univ]
  change Fintype.card {z : Fin 32 // G.Adj x z} * 4 = 24
  let e : {z : Fin 32 // z ∈ G.neighborSet x} ≃
      {z : Fin 32 // G.Adj x z} := Equiv.subtypeEquivRight (fun _ => Iff.rfl)
  rw [← Fintype.card_congr e, hcard]

/-- Vertices outside the closed first layer and the second layer.  At order 32
this set will be the singleton antipode of `x`. -/
def thirtyTwoAntipodes (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    (x : Fin 32) : Finset (Fin 32) :=
  Finset.univ \ (insert x (G.neighborFinset x) ∪ secondLayer G x)

/-- Every vertex in a hypothetical counterexample has a unique antipode. -/
theorem card_thirtyTwoAntipodes_eq_one
    (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 32) G) (hmin : 6 ≤ G.minDegree)
    (x : Fin 32) :
    (thirtyTwoAntipodes G x).card = 1 := by
  classical
  have hreg := degree_eq_six_of_thirtytwo_minDegree_six G hfree hmin
  have hsecond := card_secondLayer_eq_twentyfour_of_thirtytwo_minDegree_six
    G hfree hmin x
  let C : Finset (Fin 32) := insert x (G.neighborFinset x)
  have hCD : Disjoint C (secondLayer G x) := by
    rw [Finset.disjoint_left]
    intro z hzC hzD
    rw [secondLayer, Finset.mem_biUnion] at hzD
    obtain ⟨w, _, hzw⟩ := hzD
    exact (Finset.mem_sdiff.mp hzw).2 hzC
  have hC : C.card = 7 := by
    change (insert x (G.neighborFinset x)).card = 7
    rw [Finset.card_insert_of_notMem]
    · rw [G.card_neighborFinset_eq_degree, hreg x]
    · simp
  rw [thirtyTwoAntipodes, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  change 32 - (C ∪ secondLayer G x).card = 1
  rw [Finset.card_union_of_disjoint hCD, hC, hsecond]

/-- An antipode is distinct from and nonadjacent to its center. -/
theorem thirtyTwoAntipode_ne_and_not_adj
    (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    {x a : Fin 32} (ha : a ∈ thirtyTwoAntipodes G x) :
    a ≠ x ∧ ¬ G.Adj x a := by
  rw [thirtyTwoAntipodes, Finset.mem_sdiff] at ha
  have hout := ha.2
  rw [Finset.mem_union, Finset.mem_insert] at hout
  refine ⟨fun h => hout (Or.inl (Or.inl h)), fun h => ?_⟩
  exact hout (Or.inl (Or.inr ((G.mem_neighborFinset x a).mpr h)))

/-- An antipode has no common neighbour with its center. -/
theorem thirtyTwoAntipode_common_eq_zero
    (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    {x a : Fin 32} (ha : a ∈ thirtyTwoAntipodes G x) :
    (G.neighborFinset x ∩ G.neighborFinset a).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  have hzx : G.Adj x z := (G.mem_neighborFinset x z).mp
    (Finset.mem_inter.mp hz).1
  have hza : G.Adj z a := ((G.mem_neighborFinset a z).mp
    (Finset.mem_inter.mp hz).2).symm
  have hasecond : a ∈ secondLayer G x := by
    rw [secondLayer, Finset.mem_biUnion]
    let y : {w : Fin 32 // w ∈ G.neighborSet x} := ⟨z, hzx⟩
    refine ⟨y, Finset.mem_univ _, ?_⟩
    rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨(G.mem_neighborFinset z a).mpr hza, ?_⟩
    intro haClosed
    rcases Finset.mem_insert.mp haClosed with hax | haN
    · exact (thirtyTwoAntipode_ne_and_not_adj G ha).1 hax
    · exact (thirtyTwoAntipode_ne_and_not_adj G ha).2
        ((G.mem_neighborFinset x a).mp haN)
  rw [thirtyTwoAntipodes, Finset.mem_sdiff] at ha
  exact ha.2 (Finset.mem_union_right _ hasecond)

/-- Exact intrinsic characterization of the singleton antipode set. -/
theorem mem_thirtyTwoAntipodes_iff
    (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 32) G) (hmin : 6 ≤ G.minDegree)
    (x a : Fin 32) :
    a ∈ thirtyTwoAntipodes G x ↔
      a ≠ x ∧
        (G.neighborFinset x ∩ G.neighborFinset a).card = 0 := by
  constructor
  · intro ha
    exact ⟨(thirtyTwoAntipode_ne_and_not_adj G ha).1,
      thirtyTwoAntipode_common_eq_zero G ha⟩
  · rintro ⟨hax, hcommon⟩
    rw [thirtyTwoAntipodes, Finset.mem_sdiff]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.mem_union, Finset.mem_insert]
    push Not
    refine ⟨⟨hax, ?_⟩, ?_⟩
    · intro haN
      have hxa : G.Adj x a := (G.mem_neighborFinset x a).mp haN
      have hone := card_common_eq_one_of_thirtytwo_minDegree_six
        G hfree hmin hxa
      omega
    · intro hsecond
      rw [secondLayer, Finset.mem_biUnion] at hsecond
      obtain ⟨y, _, hay⟩ := hsecond
      have hya : G.Adj y.1 a := (G.mem_neighborFinset y.1 a).mp
        (Finset.mem_sdiff.mp hay).1
      have hyx : G.Adj y.1 x := y.2.symm
      have hymem : y.1 ∈ G.neighborFinset x ∩ G.neighborFinset a :=
        Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x y.1).mpr hyx.symm,
          (G.mem_neighborFinset a y.1).mpr hya.symm⟩
      rw [Finset.card_eq_zero.mp hcommon] at hymem
      exact Finset.notMem_empty _ hymem

/-- Antipodality is symmetric; the singleton sets therefore pair all 32
vertices into 16 unordered fibers. -/
theorem mem_thirtyTwoAntipodes_comm
    (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 32) G) (hmin : 6 ≤ G.minDegree)
    (x a : Fin 32) :
    a ∈ thirtyTwoAntipodes G x ↔ x ∈ thirtyTwoAntipodes G a := by
  rw [mem_thirtyTwoAntipodes_iff G hfree hmin,
    mem_thirtyTwoAntipodes_iff G hfree hmin]
  constructor
  · rintro ⟨hne, hzero⟩
    exact ⟨hne.symm, by simpa [Finset.inter_comm] using hzero⟩
  · rintro ⟨hne, hzero⟩
    exact ⟨hne.symm, by simpa [Finset.inter_comm] using hzero⟩

/-- **New lower bound at order 32:** `f(32) ≥ 6`. -/
theorem six_le_minDegreeForC4_thirtytwo :
    6 ≤ minDegreeForC4 32 := by
  have hw : C4FreeMinDegreeWitness 32 5 :=
    ⟨polarityCycle32, inferInstance, polarityCycle32_five_le_minDegree,
      polarityCycle32_not_containsC4⟩
  have hlt := (c4FreeMinDegreeWitness_iff_lt_minDegreeForC4
    (n := 32) (d := 5) (by norm_num)).1 hw
  omega

/-- **A new verified monotonicity step:** `f(31) ≤ f(32)`.  The universal
tight-point bound gives `f(31) ≤ 6`, while the explicit witness gives
`6 ≤ f(32)`. -/
theorem minDegreeForC4_thirtyone_le_thirtytwo :
    minDegreeForC4 31 ≤ minDegreeForC4 32 :=
  le_trans minDegreeForC4_thirtyone_le six_le_minDegreeForC4_thirtytwo

end Erdos85
