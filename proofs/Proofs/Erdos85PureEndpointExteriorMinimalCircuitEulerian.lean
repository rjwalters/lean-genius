import Proofs.Erdos85PureEndpointExteriorMinimalCircuitConnectedCut
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationCutParity

/-! # Connected even-degree structure of a minimal exterior circuit -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Every row has even internal intersection degree in any pointwise-even
exterior configuration when the uniform row size `m` is even. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_internalDegreeEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      ∀ w ∈ T,
        Even (((T.erase w).filter fun u =>
          (row w ∩ row u).Nonempty).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  let Inc : W → P → Prop := fun w y => G.Adj w.1 y.1
  intro T heven w hwT
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have huniform : ((univ : Finset P).filter fun y => Inc w y).card = m := by
    have himage : (((univ : Finset P).filter fun y => Inc w y).image
        fun y => y.1) = row w := by
      ext y
      constructor
      · intro hy
        obtain ⟨yy, hyy, rfl⟩ := mem_image.mp hy
        exact mem_inter.mpr ⟨
          (G.mem_neighborFinset w.1 yy.1).mpr (mem_filter.mp hyy).2, yy.2⟩
      · intro hy
        let yy : P := ⟨y, (mem_inter.mp hy).2⟩
        exact mem_image.mpr ⟨yy, mem_filter.mpr ⟨mem_univ _,
          (G.mem_neighborFinset w.1 y).mp (mem_inter.mp hy).1⟩, rfl⟩
    calc
      ((univ : Finset P).filter fun y => Inc w y).card =
          ((((univ : Finset P).filter fun y => Inc w y).image
            fun y => y.1).card) :=
        (card_image_of_injective _ Subtype.val_injective).symm
      _ = (row w).card := congrArg card himage
      _ = m := hdesign.1 w.1 (by
        simpa [F] using (mem_compl.mp w.2))
  have hlinear : ∀ u ∈ T.erase w,
      ((univ : Finset P).filter fun y => Inc w y ∧ Inc u y).card ≤ 1 := by
    intro u hu
    have huT := mem_of_mem_erase hu
    have hwu : w.1 ≠ u.1 := fun h =>
      (ne_of_mem_erase hu) (Subtype.ext h).symm
    have hbase := hdesign.2.1 w.1
      (by simpa [F] using (mem_compl.mp w.2)) u.1
      (by simpa [F] using (mem_compl.mp u.2)) hwu
    have himage : (((univ : Finset P).filter fun y =>
        Inc w y ∧ Inc u y).image fun y => y.1) = row w ∩ row u := by
      ext y
      constructor
      · intro hy
        obtain ⟨yy, hyy, rfl⟩ := mem_image.mp hy
        have hd := (mem_filter.mp hyy).2
        exact mem_inter.mpr ⟨mem_inter.mpr ⟨
          (G.mem_neighborFinset w.1 yy.1).mpr hd.1, yy.2⟩,
          mem_inter.mpr ⟨(G.mem_neighborFinset u.1 yy.1).mpr hd.2, yy.2⟩⟩
      · intro hy
        have hd := mem_inter.mp hy
        let yy : P := ⟨y, (mem_inter.mp hd.1).2⟩
        exact mem_image.mpr ⟨yy, mem_filter.mpr ⟨mem_univ _, ⟨
          (G.mem_neighborFinset w.1 y).mp (mem_inter.mp hd.1).1,
          (G.mem_neighborFinset u.1 y).mp (mem_inter.mp hd.2).1⟩⟩, rfl⟩
    calc
      ((univ : Finset P).filter fun y => Inc w y ∧ Inc u y).card =
          ((((univ : Finset P).filter fun y =>
            Inc w y ∧ Inc u y).image fun y => y.1).card) :=
        (card_image_of_injective _ Subtype.val_injective).symm
      _ = (row w ∩ row u).card := congrArg card himage
      _ ≤ 1 := hbase
  have hinter := linear_even_configuration_internal_meeting_add_uniform_even
    Inc T (univ : Finset P) w m hwT huniform
      (by intro y _hy; exact heven y) hlinear
  have hsame : ((T.erase w).filter fun u =>
      ((univ : Finset P).filter fun y => Inc w y ∧ Inc u y).Nonempty) =
      (T.erase w).filter fun u => (row w ∩ row u).Nonempty := by
    ext u
    simp only [mem_filter]
    apply and_congr_right
    intro _hu
    constructor
    · rintro ⟨y, hy⟩
      have hd := (mem_filter.mp hy).2
      exact ⟨y.1, mem_inter.mpr ⟨mem_inter.mpr ⟨
        (G.mem_neighborFinset w.1 y.1).mpr hd.1, y.2⟩,
        mem_inter.mpr ⟨(G.mem_neighborFinset u.1 y.1).mpr hd.2, y.2⟩⟩⟩
    · rintro ⟨y, hy⟩
      have hd := mem_inter.mp hy
      let yy : P := ⟨y, (mem_inter.mp hd.1).2⟩
      exact ⟨yy, mem_filter.mpr ⟨mem_univ _, ⟨
        (G.mem_neighborFinset w.1 y).mp (mem_inter.mp hd.1).1,
        (G.mem_neighborFinset u.1 y).mp (mem_inter.mp hd.2).1⟩⟩⟩
  rw [hsame] at hinter
  exact (Nat.even_add.mp hinter).mp hmEven

/-- The extracted minimal circuit crosses every nontrivial cut and has even
intersection degree at every row. -/
theorem c4Free_binarySquare_pureEndpoint_exists_minimal_even_configuration_eulerianCuts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∃ T : Finset W, T.Nonempty ∧ m + 1 ≤ T.card ∧
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) ∧
      (∀ U : Finset W, U ⊂ T → U.Nonempty →
        ∃ w ∈ U, ∃ z ∈ T \ U, (row w ∩ row z).Nonempty) ∧
      ∀ w ∈ T, Even (((T.erase w).filter fun u =>
        (row w ∩ row u).Nonempty).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  obtain ⟨T, hT, hlarge, heven, _hminimal, _hodd, hconnected⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_minimal_even_configuration_connectedCut
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hdegree :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_internalDegreeEven
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven
  exact ⟨T, hT, hlarge, heven, hconnected, hdegree⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_internalDegreeEven
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_minimal_even_configuration_eulerianCuts
