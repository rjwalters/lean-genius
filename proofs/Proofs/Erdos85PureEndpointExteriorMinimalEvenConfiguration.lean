import Proofs.Erdos85PureEndpointExteriorEvenConfigurationGirth

/-! # A genuine minimal exterior circuit -/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Any nonempty finite set satisfying a property contains a nonempty
cardinality-minimal subset satisfying it. -/
theorem exists_minimal_nonempty_subfinset
    {α : Type*} [DecidableEq α] (T₀ : Finset α) (P : Finset α → Prop)
    (hT₀ : T₀.Nonempty) (hP₀ : P T₀) :
    ∃ T : Finset α, T ⊆ T₀ ∧ T.Nonempty ∧ P T ∧
      ∀ U : Finset α, U ⊂ T → U.Nonempty → ¬ P U := by
  classical
  let Q : ℕ → Prop := fun n =>
    ∃ T : Finset α, T ⊆ T₀ ∧ T.Nonempty ∧ P T ∧ T.card = n
  have hQ : ∃ n, Q n :=
    ⟨T₀.card, T₀, subset_rfl, hT₀, hP₀, rfl⟩
  obtain ⟨T, hsub, hT, hPT, hcard⟩ := Nat.find_spec hQ
  refine ⟨T, hsub, hT, hPT, ?_⟩
  intro U hUT hU hPU
  have hQU : Q U.card :=
    ⟨U, hUT.1.trans hsub, hU, hPU, rfl⟩
  have hle : Nat.find hQ ≤ U.card := Nat.find_min' hQ hQU
  have hlt : U.card < Nat.find hQ := by
    rw [← hcard]
    exact card_lt_card hUT
  omega

/-- The endpoint incidence kernel contains a genuine binary circuit: a
nonempty pointwise-even configuration of size at least `m+1` with no proper
nonempty pointwise-even subconfiguration. -/
theorem c4Free_binarySquare_pureEndpoint_exists_minimal_even_exteriorRowConfiguration
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
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
    ∃ T : Finset W, T.Nonempty ∧ m + 1 ≤ T.card ∧
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) ∧
      ∀ U : Finset W, U ⊂ T → U.Nonempty →
        ¬ ∀ y : P, Even ((U.filter fun w => G.Adj w.1 y.1).card) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let Inc : W → P → Prop := fun w y => G.Adj w.1 y.1
  obtain ⟨T₀, hT₀, heven₀⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_even_exteriorRowConfiguration
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  obtain ⟨T, _hsub, hT, heven, hminimal⟩ :=
    exists_minimal_nonempty_subfinset T₀
      (fun U => ∀ y : P, Even ((U.filter fun w => Inc w y).card))
      hT₀ heven₀
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have huniform : ∀ w ∈ T,
      ((Finset.univ : Finset P).filter fun y => Inc w y).card = m := by
    intro w hw
    have himage : (((univ : Finset P).filter fun y => Inc w y).image
        fun y => y.1) = G.neighborFinset w.1 ∩ S := by
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
      _ = (G.neighborFinset w.1 ∩ S).card := congrArg card himage
      _ = m := hdesign.1 w.1 (by
        simpa [F] using (mem_compl.mp w.2))
  have hlinear : ∀ w ∈ T, ∀ z ∈ T, w ≠ z →
      ∀ y ∈ (univ : Finset P), ∀ y' ∈ (univ : Finset P),
        Inc w y → Inc z y → Inc w y' → Inc z y' → y = y' := by
    intro w hw z hz hwz y _hy y' _hy' hwy hzy hwy' hzy'
    apply Subtype.ext
    apply card_le_one.mp
      (hdesign.2.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
        z.1 (by simpa [F] using (mem_compl.mp z.2))
        (fun h => hwz (Subtype.ext h)))
    · exact mem_inter.mpr ⟨mem_inter.mpr ⟨
        (G.mem_neighborFinset w.1 y.1).mpr hwy, y.2⟩,
        mem_inter.mpr ⟨(G.mem_neighborFinset z.1 y.1).mpr hzy, y.2⟩⟩
    · exact mem_inter.mpr ⟨mem_inter.mpr ⟨
        (G.mem_neighborFinset w.1 y'.1).mpr hwy', y'.2⟩,
        mem_inter.mpr ⟨(G.mem_neighborFinset z.1 y'.1).mpr hzy', y'.2⟩⟩
  have hlarge := linear_uniform_even_configuration_card_ge
    Inc T (univ : Finset P) m hT huniform
      (by intro y _hy; exact heven y) hlinear
  exact ⟨T, hT, hlarge, heven, hminimal⟩

end

end Erdos85

#print axioms Erdos85.exists_minimal_nonempty_subfinset
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exists_minimal_even_exteriorRowConfiguration
