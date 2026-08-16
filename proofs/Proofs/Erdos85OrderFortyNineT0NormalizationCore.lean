import Proofs.Erdos85OrderFortyNineT0GlobalPermutation
import Proofs.Erdos85OrderFortyNineT0CubeResidualTransport
import Proofs.Erdos85OrderFortyNineSevenHighT0CubeSelector

/-!
# Relation-level normalization of the seven-high empty-triple representative
-/

namespace Erdos85

theorem sevenHighT0_matching0_of_coordinates :
    ∀ a b : Fin 8,
      decide (b = oneHighStandardMate a) =
        sevenHighT0CubeMatching0
          (min (a.val + 7) (b.val + 7))
          (max (a.val + 7) (b.val + 7)) := by
  native_decide

def sevenHighT0TargetN1Vertex (k : Fin 8) : Nat :=
  if k = 0 then 7 else k.val + 14

theorem sevenHighT0_matching1_of_coordinates :
    ∀ a b : Fin 8,
      decide (b = oneHighStandardMate a) =
        sevenHighT0CubeMatching1
          (min (sevenHighT0TargetN1Vertex a)
            (sevenHighT0TargetN1Vertex b))
          (max (sevenHighT0TargetN1Vertex a)
            (sevenHighT0TargetN1Vertex b)) := by
  native_decide

theorem sevenHighT0TargetN0_mem_iff (v : Fin 49) :
    v ∈ sevenHighT0TargetN0 ↔ 7 ≤ v.val ∧ v.val < 15 := by
  simp [sevenHighT0TargetN0]

theorem sevenHighT0TargetN1Only_mem_iff (v : Fin 49) :
    v ∈ sevenHighT0TargetN1Only ↔ 15 ≤ v.val ∧ v.val < 22 := by
  simp [sevenHighT0TargetN1Only]

theorem sevenHighT0_partitionNeighbors_zero_iff (v : Fin 49) :
    v.val ∈ sevenHighT0CubePartitionNeighbors 0 ↔
      v ∈ sevenHighT0TargetN0 := by
  native_decide +revert

theorem sevenHighT0_partitionNeighbors_one_iff (v : Fin 49) :
    v.val ∈ sevenHighT0CubePartitionNeighbors 1 ↔
      (v.val = 7 ∨ (15 ≤ v.val ∧ v.val < 22)) := by
  native_decide +revert

theorem sevenHighT0GlobalPerm_matching0
    (edges : BitVec 1176)
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (he₀ : ∀ x y, sevenHighT0FiberAdj edges 0 x y =
      decide (e₀ y = oneHighStandardMate (e₀ x)))
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (a b : Fin 49) (ha : a ∈ sevenHighT0TargetN0)
    (hb : b ∈ sevenHighT0TargetN0) :
    orderFortyNineBitAdj edges
        (sevenHighT0GlobalPerm e₀ e₁ hroot₁ a)
        (sevenHighT0GlobalPerm e₀ e₁ hroot₁ b) =
      sevenHighT0CubeMatching0 (min a.val b.val) (max a.val b.val) := by
  let ea : SevenHighT0Fiber 0 :=
    ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ a,
      sevenHighT0GlobalPerm_targetN0_mem_source e₀ e₁ hroot₁ a ha⟩
  let eb : SevenHighT0Fiber 0 :=
    ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ b,
      sevenHighT0GlobalPerm_targetN0_mem_source e₀ e₁ hroot₁ b hb⟩
  change sevenHighT0FiberAdj edges 0 ea eb = _
  rw [he₀ ea eb]
  have hea := sevenHighT0GlobalPerm_targetN0_coord e₀ e₁ hroot₁ a ha
  have heb := sevenHighT0GlobalPerm_targetN0_coord e₀ e₁ hroot₁ b hb
  change e₀ ea = _ at hea
  change e₀ eb = _ at heb
  rw [hea, heb, sevenHighT0_matching0_of_coordinates]
  have hav := (sevenHighT0TargetN0_mem_iff a).mp ha
  have hbv := (sevenHighT0TargetN0_mem_iff b).mp hb
  have hca : (sevenHighT0TargetN0Coord ⟨a, ha⟩).val + 7 = a.val := by
    rw [sevenHighT0TargetN0Coord_val]
    change a.val - 7 + 7 = a.val
    omega
  have hcb : (sevenHighT0TargetN0Coord ⟨b, hb⟩).val + 7 = b.val := by
    rw [sevenHighT0TargetN0Coord_val]
    change b.val - 7 + 7 = b.val
    omega
  rw [hca, hcb]

def sevenHighT0TargetN1Coord (v : Fin 49)
    (hv : v.val = 7 ∨ (15 ≤ v.val ∧ v.val < 22)) : Fin 8 :=
  if h7 : v.val = 7 then 0 else ⟨v.val - 14, by omega⟩

theorem sevenHighT0TargetN1Vertex_coord
    (v : Fin 49) (hv : v.val = 7 ∨ (15 ≤ v.val ∧ v.val < 22)) :
    sevenHighT0TargetN1Vertex (sevenHighT0TargetN1Coord v hv) = v.val := by
  by_cases h7 : v.val = 7
  · simp [sevenHighT0TargetN1Coord, sevenHighT0TargetN1Vertex, h7]
  · have hvonly := hv.resolve_left h7
    let k : Fin 8 := ⟨v.val - 14, by omega⟩
    have hk : k ≠ 0 := by
      intro hk0
      have hkval := congrArg Fin.val hk0
      simp [k] at hkval
      omega
    rw [show sevenHighT0TargetN1Coord v hv = k by
      simp [sevenHighT0TargetN1Coord, h7, k]]
    change sevenHighT0TargetN1Vertex k = v.val
    rw [show sevenHighT0TargetN1Vertex k = k.val + 14 by
      simp [sevenHighT0TargetN1Vertex, hk]]
    change v.val - 14 + 14 = v.val
    omega

theorem sevenHighT0GlobalPerm_targetN1_coord
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (hroot₀ : e₀ ⟨7, sevenHighT0SupportFiber_zero_mem_seven⟩ = 0)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) (hv : v.val = 7 ∨ (15 ≤ v.val ∧ v.val < 22)) :
    e₁ ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ v,
      (sevenHighT0GlobalPerm_targetN1_iff_sourceN1
        e₀ hroot₀ e₁ hroot₁ v).mp hv⟩ =
      sevenHighT0TargetN1Coord v hv := by
  by_cases h7 : v.val = 7
  · have hveq : v = 7 := Fin.ext h7
    subst v
    simpa [sevenHighT0TargetN1Coord,
      sevenHighT0GlobalPerm_root e₀ hroot₀ e₁ hroot₁] using hroot₁
  · have hvonly : v ∈ sevenHighT0TargetN1Only :=
      (sevenHighT0TargetN1Only_mem_iff v).mpr (hv.resolve_left h7)
    have hc := sevenHighT0GlobalPerm_targetN1Only_coord
      e₀ e₁ hroot₁ v hvonly
    rw [hc]
    apply Fin.ext
    simp [sevenHighT0TargetN1Coord, h7]

theorem sevenHighT0GlobalPerm_matching1
    (edges : BitVec 1176)
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (hroot₀ : e₀ ⟨7, sevenHighT0SupportFiber_zero_mem_seven⟩ = 0)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (he₁ : ∀ x y, sevenHighT0FiberAdj edges 1 x y =
      decide (e₁ y = oneHighStandardMate (e₁ x)))
    (a b : Fin 49)
    (ha : a.val = 7 ∨ (15 ≤ a.val ∧ a.val < 22))
    (hb : b.val = 7 ∨ (15 ≤ b.val ∧ b.val < 22)) :
    orderFortyNineBitAdj edges
        (sevenHighT0GlobalPerm e₀ e₁ hroot₁ a)
        (sevenHighT0GlobalPerm e₀ e₁ hroot₁ b) =
      sevenHighT0CubeMatching1 (min a.val b.val) (max a.val b.val) := by
  let ea : SevenHighT0Fiber 1 :=
    ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ a,
      (sevenHighT0GlobalPerm_targetN1_iff_sourceN1
        e₀ hroot₀ e₁ hroot₁ a).mp ha⟩
  let eb : SevenHighT0Fiber 1 :=
    ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ b,
      (sevenHighT0GlobalPerm_targetN1_iff_sourceN1
        e₀ hroot₀ e₁ hroot₁ b).mp hb⟩
  change sevenHighT0FiberAdj edges 1 ea eb = _
  rw [he₁ ea eb]
  have hea := sevenHighT0GlobalPerm_targetN1_coord
    e₀ hroot₀ e₁ hroot₁ a ha
  have heb := sevenHighT0GlobalPerm_targetN1_coord
    e₀ hroot₀ e₁ hroot₁ b hb
  change e₁ ea = _ at hea
  change e₁ eb = _ at heb
  rw [hea, heb, sevenHighT0_matching1_of_coordinates,
    sevenHighT0TargetN1Vertex_coord a ha,
    sevenHighT0TargetN1Vertex_coord b hb]

set_option maxHeartbeats 0 in
theorem sevenHighT0_exists_normalized_relationCore
    (edges : BitVec 1176)
    (h : orderFortyNineBooleanConstraints 7 sevenHighT0Masks edges) :
    ∃ cube : Fin 7, ∃ normalizedEdges : BitVec 1176,
      SevenHighT0CubeRelationCore cube.val
        (orderFortyNineBitAdj normalizedEdges) := by
  obtain ⟨e₀, hroot₀, he₀, e₁, hroot₁, he₁⟩ :=
    sevenHighT0_exists_rooted_fiber_matchings edges h
  have hfields := h
  rcases hfields with ⟨_, _, hdegreesSource, hc4source, _, hpartitionSource⟩
  let e := sevenHighT0GlobalPerm e₀ e₁ hroot₁
  let adj := orderFortyNineBitAdj edges
  let normalizedEdges := orderFortyNineRelabelEdges edges e
  have hadj : orderFortyNineBitAdj normalizedEdges =
      fun i j => adj (e i) (e j) := by
    funext i j
    exact orderFortyNineBitAdj_relabelEdges edges e i j
  have efix : ∀ i : Fin 49, i.val < 7 → e i = i :=
    sevenHighT0GlobalPerm_fix_high e₀ e₁ hroot₁
  have eprefix : ∀ i : Fin 49, (e i).val < 7 ↔ i.val < 7 :=
    sevenHighT0GlobalPerm_preserves_high_prefix e₀ e₁ hroot₁
  have hind : ∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j →
      adj (e i) (e j) = false :=
    orderFortyNineHighIndependent_relabel adj e efix
      (sevenHighT0_source_highIndependent edges h)
  have hn0 : ∀ x : Fin 49, 7 ≤ x.val →
      adj (e 0) (e x) = decide (x.val < 15) := by
    have hs0 := orderFortyNine_source_supportColumn 7 sevenHighT0Masks adj h 0
      (by omega)
    intro x hx
    rw [efix 0 (by omega)]
    rw [show adj 0 (e x) = adj (e x) 0 by
      exact orderFortyNineBitAdj_comm edges 0 (e x)]
    have hs := hs0 (e x)
    change adj (e x) 0 = _ at hs
    rw [hs]
    apply decide_eq_decide.mpr
    change e x ∈ sevenHighT0SupportFiber 0 ↔ x.val < 15
    rw [← sevenHighT0GlobalPerm_targetN0_iff_sourceN0 e₀ e₁ hroot₁ x]
    rw [sevenHighT0TargetN0_mem_iff]
    omega
  have hm0 : ∀ a b : Fin 49, 7 ≤ a.val → a.val < 15 →
      7 ≤ b.val → b.val < 15 → a ≠ b →
      adj (e a) (e b) = sevenHighT0CubeMatching0
        (min a.val b.val) (max a.val b.val) := by
    intro a b ha7 ha15 hb7 hb15 _
    exact sevenHighT0GlobalPerm_matching0 edges e₀ he₀ e₁ hroot₁ a b
      ((sevenHighT0TargetN0_mem_iff a).mpr ⟨ha7, ha15⟩)
      ((sevenHighT0TargetN0_mem_iff b).mpr ⟨hb7, hb15⟩)
  have hn1 : ∀ x : Fin 49, 7 ≤ x.val →
      adj (e 1) (e x) =
        decide (x.val = 7 ∨ (15 ≤ x.val ∧ x.val < 22)) := by
    have hs1 := orderFortyNine_source_supportColumn 7 sevenHighT0Masks adj h 1
      (by omega)
    intro x hx
    rw [efix 1 (by omega)]
    rw [show adj 1 (e x) = adj (e x) 1 by
      exact orderFortyNineBitAdj_comm edges 1 (e x)]
    have hs := hs1 (e x)
    change adj (e x) 1 = _ at hs
    rw [hs]
    exact decide_eq_decide.mpr
      (sevenHighT0GlobalPerm_targetN1_iff_sourceN1
        e₀ hroot₀ e₁ hroot₁ x).symm
  have hm1 : ∀ a b : Fin 49,
      (a.val = 7 ∨ (15 ≤ a.val ∧ a.val < 22)) →
      (b.val = 7 ∨ (15 ≤ b.val ∧ b.val < 22)) → a ≠ b →
      adj (e a) (e b) = sevenHighT0CubeMatching1
        (min a.val b.val) (max a.val b.val) := by
    intro a b ha hb _
    exact sevenHighT0GlobalPerm_matching1 edges e₀ hroot₀ e₁ hroot₁ he₁
      a b ha hb
  have hcommon : ∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j →
      ∃ w : Fin 49, 7 ≤ w.val ∧
        adj (e i) (e w) = true ∧ adj (e j) (e w) = true :=
    orderFortyNineHighCommonWitness_relabel adj e efix eprefix
      (sevenHighT0_source_high_commonWitness edges h)
  have hc4 : ∀ i j : Fin 49, i ≠ j →
      (Finset.univ.filter fun w =>
        adj (e i) (e w) && adj (e j) (e w)).card ≤ 1 :=
    orderFortyNineC4Constraints_relabel adj e hc4source
  have hdegrees : ∀ i : Fin 49,
      (Finset.univ.filter fun j => adj (e i) (e j)).card =
        if i.val < 7 then 8 else 7 :=
    orderFortyNineDegreeConstraints_relabel adj e hdegreesSource eprefix
  have hpartition : ∀ y : Fin 49, 7 ≤ y.val → ∀ high : Fin 2,
      ∃ x : Fin 49,
        x.val ∈ sevenHighT0CubePartitionNeighbors high.val ∧
        x ≠ y ∧ adj (e y) (e x) = true := by
    intro y hy high
    have hey : 7 ≤ (e y).val := by
      exact Nat.le_of_not_gt (fun hehigh =>
        (Nat.not_lt_of_ge hy) ((eprefix y).mp hehigh))
    have hp := hpartitionSource (e y) hey
      ⟨high.val, Nat.lt_trans high.isLt (by omega)⟩
      (Nat.lt_trans high.isLt (by omega))
    have hcardpos : 0 < (Finset.univ.filter fun k =>
        adj (e y) k &&
          (orderFortyNineSupportMask sevenHighT0Masks k).getLsbD high.val).card := by
      rw [hp]
      decide
    obtain ⟨sx, hsx⟩ := Finset.card_pos.mp hcardpos
    have hsx' := (Finset.mem_filter.mp hsx).2
    simp only [Bool.and_eq_true] at hsx'
    have hadjsx : adj (e y) sx = true := hsx'.1
    have hbitsx :
        (orderFortyNineSupportMask sevenHighT0Masks sx).getLsbD
          high.val = true := hsx'.2
    let x := e.symm sx
    have hex : e x = sx := e.apply_symm_apply sx
    have hsxfiber : sx ∈ sevenHighT0SupportFiber ⟨high.val, by omega⟩ := by
      simp [sevenHighT0SupportFiber, hbitsx]
    have hxmem : x.val ∈ sevenHighT0CubePartitionNeighbors high.val := by
      fin_cases high
      · apply (sevenHighT0_partitionNeighbors_zero_iff x).mpr
        apply (sevenHighT0GlobalPerm_targetN0_iff_sourceN0
          e₀ e₁ hroot₁ x).mpr
        rw [show sevenHighT0GlobalPerm e₀ e₁ hroot₁ x = sx by
          exact e.apply_symm_apply sx]
        exact hsxfiber
      · apply (sevenHighT0_partitionNeighbors_one_iff x).mpr
        apply (sevenHighT0GlobalPerm_targetN1_iff_sourceN1
          e₀ hroot₀ e₁ hroot₁ x).mpr
        rw [show sevenHighT0GlobalPerm e₀ e₁ hroot₁ x = sx by
          exact e.apply_symm_apply sx]
        exact hsxfiber
    refine ⟨x, hxmem, ?_, ?_⟩
    · intro hxy
      have hsxeq : sx = e y := by rw [← hex, hxy]
      have : adj (e y) (e y) = true := by simpa [hsxeq] using hadjsx
      simpa [adj, orderFortyNineBitAdj] using this
    · rw [hex]
      exact hadjsx
  have h97 : adj (e 7) (e 9) = false := by
    have := hm0 7 9 (by omega) (by omega) (by omega) (by omega) (by decide)
    simpa [sevenHighT0CubeMatching0] using this
  have hselectorPartition : ∃ x : Fin 49,
      (x.val = 7 ∨ (15 ≤ x.val ∧ x.val < 22)) ∧
      x ≠ (9 : Fin 49) ∧ adj (e 9) (e x) = true := by
    obtain ⟨x, hxmem, hxne, hxadj⟩ := hpartition 9 (by omega) 1
    refine ⟨x, ?_, hxne, hxadj⟩
    exact (sevenHighT0_partitionNeighbors_one_iff x).mp (by simpa using hxmem)
  obtain ⟨cube, hcubes⟩ := sevenHighT0_exists_unique_cube_selector
    (fun i j => adj (e i) (e j))
    (fun i j => by simpa [adj] using orderFortyNineBitAdj_comm edges (e i) (e j))
    h97 hn1 hc4 hselectorPartition
  have hcubesVal : ∀ index : Fin 7,
      adj (e 9) (e ⟨index.val + 15, by omega⟩) =
        decide (index.val = cube.val) := by
    intro index
    rw [hcubes index]
    exact decide_eq_decide.mpr Fin.ext_iff
  refine ⟨cube, normalizedEdges, ?_⟩
  rw [hadj]
  exact ⟨cube.isLt, hind, hn0, hm0, hn1, hm1, hcommon, hc4,
    hdegrees, hpartition, hcubesVal⟩

/-- After residual symmetry, only cube zero and cube one remain. -/
theorem sevenHighT0_exists_normalized_relationCore_zero_or_one
    (edges : BitVec 1176)
    (h : orderFortyNineBooleanConstraints 7 sevenHighT0Masks edges) :
    ∃ cube : Fin 2, ∃ normalizedEdges : BitVec 1176,
      SevenHighT0CubeRelationCore cube.val
        (orderFortyNineBitAdj normalizedEdges) := by
  obtain ⟨cube, normalizedEdges, hcube⟩ :=
    sevenHighT0_exists_normalized_relationCore edges h
  by_cases hc0 : cube = 0
  · subst cube
    exact ⟨0, normalizedEdges, hcube⟩
  · let residualEdges := orderFortyNineRelabelEdges normalizedEdges
      (sevenHighT0ResidualVertexPerm cube)
    refine ⟨1, residualEdges, ?_⟩
    exact sevenHighT0_nonzero_cube_bit_relation_transport
      cube hc0 normalizedEdges hcube

end Erdos85
