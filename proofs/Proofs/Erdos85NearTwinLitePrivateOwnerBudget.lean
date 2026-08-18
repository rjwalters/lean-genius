import Proofs.Erdos85NearTwinLiteOwnerDichotomy

/-! # Private-neighbor owner budgets in the λ=5 sharp boundary -/

namespace Erdos85

noncomputable section

/-- A color appearing in the image of an injective finite coloring has a
singleton fiber. -/
theorem card_filter_eq_one_of_mem_image_of_injOn
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (E : Finset R) (color : R → C) (c : C)
    (hc : c ∈ E.image color)
    (hinj : ∀ r₁ ∈ E, ∀ r₂ ∈ E,
      color r₁ = color r₂ → r₁ = r₂) :
    (E.filter fun r => color r = c).card = 1 := by
  obtain ⟨r, hrE, hrc⟩ := Finset.mem_image.mp hc
  rw [Finset.card_eq_one]
  refine ⟨r, ?_⟩
  ext z
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hzE, hzc⟩
    exact hinj z hzE r hrE (hzc.trans hrc.symm)
  · intro hzr
    subst z
    exact ⟨hrE, hrc⟩

/-- Filtering a disjoint core/private union splits cardinality additively. -/
theorem card_filter_union_eq_add_of_disjoint
    {R : Type*} [DecidableEq R]
    (S P : Finset R) (pred : R → Prop) [DecidablePred pred]
    (hdis : Disjoint S P) :
    ((S ∪ P).filter pred).card =
      (S.filter pred).card + (P.filter pred).card := by
  rw [Finset.filter_union,
    Finset.card_union_of_disjoint
      (hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

/-- If a color occurs once in the core and once in the full residual row, it
does not occur on the private pair. -/
theorem private_filter_card_zero_of_full_one_core_one
    {R : Type*} [DecidableEq R]
    (S P : Finset R) (pred : R → Prop) [DecidablePred pred]
    (hdis : Disjoint S P)
    (hfull : ((S ∪ P).filter pred).card = 1)
    (hcore : (S.filter pred).card = 1) :
    (P.filter pred).card = 0 := by
  have hsplit := card_filter_union_eq_add_of_disjoint S P pred hdis
  omega

/-- If a color already occurs twice in the core, its degree-two budget leaves
no occurrence on the private pair. -/
theorem private_filter_card_zero_of_full_two_core_two
    {R : Type*} [DecidableEq R]
    (S P : Finset R) (pred : R → Prop) [DecidablePred pred]
    (hdis : Disjoint S P)
    (hfull : ((S ∪ P).filter pred).card = 2)
    (hcore : (S.filter pred).card = 2) :
    (P.filter pred).card = 0 := by
  have hsplit := card_filter_union_eq_add_of_disjoint S P pred hdis
  omega

/-- Every other non-base color, occurring once in the core, occurs exactly
once on the private pair by the degree-two budget. -/
theorem private_filter_card_one_of_full_two_core_one
    {R : Type*} [DecidableEq R]
    (S P : Finset R) (pred : R → Prop) [DecidablePred pred]
    (hdis : Disjoint S P)
    (hfull : ((S ∪ P).filter pred).card = 2)
    (hcore : (S.filter pred).card = 1) :
    (P.filter pred).card = 1 := by
  have hsplit := card_filter_union_eq_add_of_disjoint S P pred hdis
  omega

/-- Left-side color census on the sharp five-core boundary.  The base color
appears once, the color of the right-base exception appears twice, and each
other non-base color appears once. -/
theorem fiveCore_boundary_left_color_census
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S E : Finset R) (left right : R → C) (base : C)
    (palette : Finset C) (ℓ t : R)
    (hset : S = E ∪ {ℓ, t})
    (hEdata : ∀ r ∈ E, left r = right r ∧ left r ≠ base)
    (himage : E.image left = palette)
    (hpalette : ∀ c, c ≠ base → c ∈ palette)
    (hbaseNot : base ∉ palette)
    (hinj : ∀ r₁ ∈ E, ∀ r₂ ∈ E,
      left r₁ = left r₂ → r₁ = r₂)
    (hℓ : left ℓ = base) (htleft : left t ≠ base)
    (htright : right t = base) :
    (S.filter fun r => left r = base).card = 1 ∧
      (S.filter fun r => left r = left t).card = 2 ∧
      ∀ c ∈ palette, c ≠ left t →
        (S.filter fun r => left r = c).card = 1 := by
  have hℓE : ℓ ∉ E := by
    intro h
    exact (hEdata ℓ h).2 hℓ
  have htE : t ∉ E := by
    intro h
    have hdata := hEdata t h
    exact htleft (hdata.1.trans htright)
  have hbase : (S.filter fun r => left r = base) = {ℓ} := by
    ext r
    rw [hset]
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hrE | hrℓ | hrt, hc⟩
      · exact ((hEdata r hrE).2 hc).elim
      · exact hrℓ
      · subst r
        exact (htleft hc).elim
    · intro hrℓ
      subst r
      exact ⟨Or.inr (Or.inl rfl), hℓ⟩
  have htPalette : left t ∈ palette := by
    exact hpalette (left t) htleft
  have htFiber : (E.filter fun r => left r = left t).card = 1 :=
    card_filter_eq_one_of_mem_image_of_injOn E left (left t)
      (by simpa [himage] using htPalette) hinj
  have htCore : (S.filter fun r => left r = left t).card = 2 := by
    have heq : (S.filter fun r => left r = left t) =
        insert t (E.filter fun r => left r = left t) := by
      ext r
      rw [hset]
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hrE | hrℓ | hrt, hc⟩
        · exact Or.inr ⟨hrE, hc⟩
        · subst r
          exact (htleft (hc.symm.trans hℓ)).elim
        · exact Or.inl hrt
      · rintro (hrt | ⟨hrE, hc⟩)
        · subst r
          exact ⟨Or.inr (Or.inr rfl), rfl⟩
        · exact ⟨Or.inl hrE, hc⟩
    rw [heq, Finset.card_insert_of_notMem]
    · omega
    · simp [htE]
  refine ⟨by rw [hbase]; simp, htCore, ?_⟩
  intro c hcPalette hct
  have hcbase : c ≠ base := by
    intro h
    subst c
    exact hbaseNot hcPalette
  have hcImage : c ∈ E.image left := by simpa [himage] using hcPalette
  have hcFiber : (E.filter fun r => left r = c).card = 1 :=
    card_filter_eq_one_of_mem_image_of_injOn E left c hcImage hinj
  have heq : (S.filter fun r => left r = c) = E.filter fun r => left r = c := by
    ext r
    rw [hset]
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hrE | hrℓ | hrt, hc⟩
      · exact ⟨hrE, hc⟩
      · subst r
        exact (hcbase (hc.symm.trans hℓ)).elim
      · subst r
        exact (hct hc.symm).elim
    · rintro ⟨hrE, hc⟩
      exact ⟨Or.inl hrE, hc⟩
  rw [heq, hcFiber]

/-- Symmetric right-side color census. -/
theorem fiveCore_boundary_right_color_census
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S E : Finset R) (left right : R → C) (base : C)
    (palette : Finset C) (ℓ t : R)
    (hset : S = E ∪ {ℓ, t})
    (hEdata : ∀ r ∈ E, left r = right r ∧ left r ≠ base)
    (himage : E.image left = palette)
    (hpalette : ∀ c, c ≠ base → c ∈ palette)
    (hbaseNot : base ∉ palette)
    (hinj : ∀ r₁ ∈ E, ∀ r₂ ∈ E,
      left r₁ = left r₂ → r₁ = r₂)
    (hℓleft : left ℓ = base) (hℓright : right ℓ ≠ base)
    (ht : right t = base) :
    (S.filter fun r => right r = base).card = 1 ∧
      (S.filter fun r => right r = right ℓ).card = 2 ∧
      ∀ c ∈ palette, c ≠ right ℓ →
        (S.filter fun r => right r = c).card = 1 := by
  have hset' : S = E ∪ {t, ℓ} := by
    rw [hset]
    congr 1
    ext r
    simp [or_comm]
  have hEdata' : ∀ r ∈ E, right r = left r ∧ right r ≠ base := by
    intro r hr
    have h := hEdata r hr
    exact ⟨h.1.symm, h.1.symm ▸ h.2⟩
  have himage' : E.image right = palette := by
    rw [← himage]
    apply Finset.image_congr
    intro r hr
    exact (hEdata r hr).1.symm
  have hinj' : ∀ r₁ ∈ E, ∀ r₂ ∈ E,
      right r₁ = right r₂ → r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂ h
    apply hinj r₁ hr₁ r₂ hr₂
    rw [(hEdata r₁ hr₁).1, (hEdata r₂ hr₂).1]
    exact h
  exact fiveCore_boundary_left_color_census
    S E right left base palette t ℓ hset' hEdata' himage'
      hpalette hbaseNot hinj' ht hℓright hℓleft

/-- The left private pair carries neither the base color nor the color of the
right-base exception; each of the other two non-base colors occurs once. -/
theorem fiveCore_boundary_left_private_color_census
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S P E : Finset R) (left right : R → C) (base : C)
    (palette : Finset C) (ℓ t : R)
    (hdis : Disjoint S P)
    (hset : S = E ∪ {ℓ, t})
    (hEdata : ∀ r ∈ E, left r = right r ∧ left r ≠ base)
    (himage : E.image left = palette)
    (hpalette : ∀ c, c ≠ base → c ∈ palette)
    (hbaseNot : base ∉ palette)
    (hinj : ∀ r₁ ∈ E, ∀ r₂ ∈ E,
      left r₁ = left r₂ → r₁ = r₂)
    (hℓ : left ℓ = base) (htleft : left t ≠ base)
    (htright : right t = base)
    (hfullBase : (((S ∪ P).filter fun r => left r = base).card = 1))
    (hfullPalette : ∀ c ∈ palette,
      ((S ∪ P).filter fun r => left r = c).card = 2) :
    (P.filter fun r => left r = base).card = 0 ∧
      (P.filter fun r => left r = left t).card = 0 ∧
      ∀ c ∈ palette, c ≠ left t →
        (P.filter fun r => left r = c).card = 1 := by
  have hcensus := fiveCore_boundary_left_color_census
    S E left right base palette ℓ t hset hEdata himage hpalette
      hbaseNot hinj hℓ htleft htright
  have htPalette : left t ∈ palette := hpalette _ htleft
  constructor
  · exact private_filter_card_zero_of_full_one_core_one
      S P (fun r => left r = base) hdis hfullBase hcensus.1
  constructor
  · exact private_filter_card_zero_of_full_two_core_two
      S P (fun r => left r = left t) hdis
        (hfullPalette (left t) htPalette) hcensus.2.1
  · intro c hc hct
    exact private_filter_card_one_of_full_two_core_one
      S P (fun r => left r = c) hdis
        (hfullPalette c hc) (hcensus.2.2 c hc hct)

/-- Symmetric census for the right private pair. -/
theorem fiveCore_boundary_right_private_color_census
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (S P E : Finset R) (left right : R → C) (base : C)
    (palette : Finset C) (ℓ t : R)
    (hdis : Disjoint S P)
    (hset : S = E ∪ {ℓ, t})
    (hEdata : ∀ r ∈ E, left r = right r ∧ left r ≠ base)
    (himage : E.image left = palette)
    (hpalette : ∀ c, c ≠ base → c ∈ palette)
    (hbaseNot : base ∉ palette)
    (hinj : ∀ r₁ ∈ E, ∀ r₂ ∈ E,
      left r₁ = left r₂ → r₁ = r₂)
    (hℓleft : left ℓ = base) (hℓright : right ℓ ≠ base)
    (ht : right t = base)
    (hfullBase : (((S ∪ P).filter fun r => right r = base).card = 1))
    (hfullPalette : ∀ c ∈ palette,
      ((S ∪ P).filter fun r => right r = c).card = 2) :
    (P.filter fun r => right r = base).card = 0 ∧
      (P.filter fun r => right r = right ℓ).card = 0 ∧
      ∀ c ∈ palette, c ≠ right ℓ →
        (P.filter fun r => right r = c).card = 1 := by
  have hset' : S = E ∪ {t, ℓ} := by
    rw [hset]
    congr 1
    ext r
    simp [or_comm]
  have hEdata' : ∀ r ∈ E, right r = left r ∧ right r ≠ base := by
    intro r hr
    have h := hEdata r hr
    exact ⟨h.1.symm, h.1.symm ▸ h.2⟩
  have himage' : E.image right = palette := by
    rw [← himage]
    apply Finset.image_congr
    intro r hr
    exact (hEdata r hr).1.symm
  have hinj' : ∀ r₁ ∈ E, ∀ r₂ ∈ E,
      right r₁ = right r₂ → r₁ = r₂ := by
    intro r₁ hr₁ r₂ hr₂ h
    apply hinj r₁ hr₁ r₂ hr₂
    rw [(hEdata r₁ hr₁).1, (hEdata r₂ hr₂).1]
    exact h
  exact fiveCore_boundary_left_private_color_census
    S P E right left base palette t ℓ hdis hset' hEdata' himage'
      hpalette hbaseNot hinj' ht hℓright hℓleft hfullBase hfullPalette

end

end Erdos85
