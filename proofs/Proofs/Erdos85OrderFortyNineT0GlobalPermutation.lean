import Proofs.Erdos85OrderFortyNineT0TargetBlocks

/-!
# Block equivalences for the global `h = 7, t = 0` normalization

The rooted matching coordinates identify the target `N0` and `N1` blocks
with the corresponding source support fibers.  The only subtlety is deleting
the common root `7` from the second block; this is recorded explicitly here.
-/

namespace Erdos85

noncomputable section

abbrev FinEightNonzero := {k : Fin 8 // k ≠ 0}

/-- Coordinates `1,...,7` on the target block `15,...,21`. -/
def sevenHighT0TargetN1OnlyCoord :
    {v : Fin 49 // v ∈ sevenHighT0TargetN1Only} ≃ FinEightNonzero where
  toFun v :=
    ⟨⟨v.1.val - 14, by
      have hv := (Finset.mem_filter.mp v.2).2
      omega⟩, by
      intro hz
      have hzv := congrArg Fin.val hz
      have hv := (Finset.mem_filter.mp v.2).2
      simp at hzv
      omega⟩
  invFun k :=
    ⟨⟨k.1.val + 14, by omega⟩, by
      simp [sevenHighT0TargetN1Only]
      have hk : 0 < k.1.val := by
        have := k.2
        omega
      omega⟩
  left_inv v := by
    apply Subtype.ext
    apply Fin.ext
    have hv := (Finset.mem_filter.mp v.2).2
    simp
    omega
  right_inv k := by
    apply Subtype.ext
    apply Fin.ext
    have hk : 0 < k.1.val := by
      have := k.2
      omega
    simp

theorem sevenHighT0FiberOne_not_mem_zero_of_coord_ne_zero
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (x : SevenHighT0Fiber 1) (hx : e₁ x ≠ 0) :
    x.1 ∉ sevenHighT0SupportFiber 0 := by
  intro hx0
  have hinter : x.1 ∈
      sevenHighT0SupportFiber 0 ∩ sevenHighT0SupportFiber 1 :=
    Finset.mem_inter.mpr ⟨hx0, x.2⟩
  rw [sevenHighT0SupportFiber_zero_one_inter] at hinter
  have hx7 : x.1 = 7 := by simpa using hinter
  apply hx
  have hsub : x = ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ := by
    apply Subtype.ext
    exact hx7
  simpa [hsub] using hroot

/-- Non-root coordinates on source fiber one. -/
def sevenHighT0SourceN1OnlyCoord
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0) :
    {v : Fin 49 // v ∈
      sevenHighT0SupportFiber 1 \ sevenHighT0SupportFiber 0} ≃
      FinEightNonzero where
  toFun v :=
    ⟨e₁ ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩, by
      intro hz
      have heq : (⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩ :
          SevenHighT0Fiber 1) =
          ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ := by
        apply e₁.injective
        simpa [hroot] using hz
      have hv7 : v.1 = 7 := congrArg Subtype.val heq
      exact (Finset.mem_sdiff.mp v.2).2 (by simpa [hv7])⟩
  invFun k :=
    ⟨(e₁.symm k.1).1, Finset.mem_sdiff.mpr
      ⟨(e₁.symm k.1).2,
        sevenHighT0FiberOne_not_mem_zero_of_coord_ne_zero e₁ hroot
          (e₁.symm k.1) (by simpa using k.2)⟩⟩
  left_inv v := by
    apply Subtype.ext
    apply Fin.ext
    have heq := congrArg (fun z : SevenHighT0Fiber 1 => z.1.val)
      (e₁.symm_apply_apply
        ⟨v.1, (Finset.mem_sdiff.mp v.2).1⟩)
    simpa using heq
  right_inv k := by
    apply Subtype.ext
    exact e₁.apply_symm_apply k.1

/-- The first target matching block maps to source support fiber zero in the
rooted matching coordinates. -/
def sevenHighT0N0BlockEquiv
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8) :
    {v : Fin 49 // v ∈ sevenHighT0TargetN0} ≃ SevenHighT0Fiber 0 :=
  sevenHighT0TargetN0Coord.trans e₀.symm

/-- The seven non-root vertices of the second target matching block map to
the source fiber-one vertices outside fiber zero. -/
def sevenHighT0N1OnlyBlockEquiv
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0) :
    {v : Fin 49 // v ∈ sevenHighT0TargetN1Only} ≃
      {v : Fin 49 // v ∈
        sevenHighT0SupportFiber 1 \ sevenHighT0SupportFiber 0} :=
  sevenHighT0TargetN1OnlyCoord.trans
    (sevenHighT0SourceN1OnlyCoord e₁ hroot).symm

theorem sevenHighT0N0BlockEquiv_root
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (hroot : e₀ ⟨7, sevenHighT0SupportFiber_zero_mem_seven⟩ = 0) :
    (sevenHighT0N0BlockEquiv e₀
      ⟨7, by native_decide⟩).1 = 7 := by
  apply Fin.ext
  have heq : e₀.symm 0 =
      ⟨7, sevenHighT0SupportFiber_zero_mem_seven⟩ := by
    apply e₀.injective
    simpa using hroot.symm
  simpa [sevenHighT0N0BlockEquiv, sevenHighT0TargetN0Coord] using
    congrArg (fun z : SevenHighT0Fiber 0 => z.1.val) heq

/-- Lift an equivalence between two subpredicates through possibly different
ambient subtype predicates. -/
def liftEquivThroughSubtypes
    {α : Type*} (p q r s : α → Prop)
    [DecidablePred p] [DecidablePred q]
    [DecidablePred r] [DecidablePred s]
    (hrp : ∀ x, r x → p x) (hsq : ∀ x, s x → q x)
    (e : {x // r x} ≃ {x // s x}) :
    {x : {x // p x} // r x.1} ≃ {x : {x // q x} // s x.1} where
  toFun x := ⟨⟨(e ⟨x.1.1, x.2⟩).1, hsq _ (e ⟨x.1.1, x.2⟩).2⟩,
    (e ⟨x.1.1, x.2⟩).2⟩
  invFun y := ⟨⟨(e.symm ⟨y.1.1, y.2⟩).1,
      hrp _ (e.symm ⟨y.1.1, y.2⟩).2⟩,
    (e.symm ⟨y.1.1, y.2⟩).2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val
      (e.symm_apply_apply ⟨x.1.1, x.2⟩)
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    simpa using congrArg Subtype.val
      (e.apply_symm_apply ⟨y.1.1, y.2⟩)

private abbrev sevenHighT0IsLow (v : Fin 49) : Prop := ¬ v.val < 7
private abbrev sevenHighT0InTargetN0 (v : Fin 49) : Prop :=
  v ∈ sevenHighT0TargetN0
private abbrev sevenHighT0InSourceN0 (v : Fin 49) : Prop :=
  v ∈ sevenHighT0SupportFiber 0
private abbrev sevenHighT0InTargetN1Only (v : Fin 49) : Prop :=
  v ∈ sevenHighT0TargetN1Only
private abbrev sevenHighT0InSourceN1Only (v : Fin 49) : Prop :=
  v ∈ sevenHighT0SupportFiber 1 \ sevenHighT0SupportFiber 0

private theorem sevenHighT0_targetN0_isLow
    (v : Fin 49) (hv : sevenHighT0InTargetN0 v) :
    sevenHighT0IsLow v := by
  have := (Finset.mem_filter.mp hv).2.1
  omega

private theorem sevenHighT0_sourceN0_isLow
    (v : Fin 49) (hv : sevenHighT0InSourceN0 v) :
    sevenHighT0IsLow v := by
  have := sevenHighT0SupportFiber_isLow 0 hv
  omega

private theorem sevenHighT0_targetN1Only_isLow
    (v : Fin 49) (hv : sevenHighT0InTargetN1Only v) :
    sevenHighT0IsLow v := by
  have := (Finset.mem_filter.mp hv).2
  omega

private theorem sevenHighT0_sourceN1Only_isLow
    (v : Fin 49) (hv : sevenHighT0InSourceN1Only v) :
    sevenHighT0IsLow v := by
  have := sevenHighT0SupportFiber_isLow 1 (Finset.mem_sdiff.mp hv).1
  omega

private theorem sevenHighT0_target_blocks_disjoint
    (v : Fin 49) (hv : sevenHighT0InTargetN1Only v) :
    ¬ sevenHighT0InTargetN0 v := by
  simp [sevenHighT0InTargetN0, sevenHighT0InTargetN1Only,
    sevenHighT0TargetN0, sevenHighT0TargetN1Only] at hv ⊢
  omega

private theorem sevenHighT0_source_blocks_disjoint
    (v : Fin 49) (hv : sevenHighT0InSourceN1Only v) :
    ¬ sevenHighT0InSourceN0 v :=
  (Finset.mem_sdiff.mp hv).2

private def sevenHighT0N0LowEquiv
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8) :
    {x : {v : Fin 49 // sevenHighT0IsLow v} //
      sevenHighT0InTargetN0 x.1} ≃
    {x : {v : Fin 49 // sevenHighT0IsLow v} //
      sevenHighT0InSourceN0 x.1} :=
  liftEquivThroughSubtypes
    sevenHighT0IsLow sevenHighT0IsLow
    sevenHighT0InTargetN0 sevenHighT0InSourceN0
    sevenHighT0_targetN0_isLow sevenHighT0_sourceN0_isLow
    (sevenHighT0N0BlockEquiv e₀)

private def sevenHighT0N1OnlyLowEquiv
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0) :
    {x : {v : Fin 49 // sevenHighT0IsLow v} //
      sevenHighT0InTargetN1Only x.1} ≃
    {x : {v : Fin 49 // sevenHighT0IsLow v} //
      sevenHighT0InSourceN1Only x.1} :=
  liftEquivThroughSubtypes
    sevenHighT0IsLow sevenHighT0IsLow
    sevenHighT0InTargetN1Only sevenHighT0InSourceN1Only
    sevenHighT0_targetN1Only_isLow sevenHighT0_sourceN1Only_isLow
    (sevenHighT0N1OnlyBlockEquiv e₁ hroot)

private theorem sevenHighT0_remaining_nested_card :
    Fintype.card
      {x : {x : {v : Fin 49 // sevenHighT0IsLow v} //
          ¬ sevenHighT0InTargetN0 x.1} //
        ¬ sevenHighT0InTargetN1Only x.1.1} =
    Fintype.card
      {x : {x : {v : Fin 49 // sevenHighT0IsLow v} //
          ¬ sevenHighT0InSourceN0 x.1} //
        ¬ sevenHighT0InSourceN1Only x.1.1} := by
  native_decide

private noncomputable def sevenHighT0LowEquiv
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0) :
    {v : Fin 49 // sevenHighT0IsLow v} ≃
      {v : Fin 49 // sevenHighT0IsLow v} := by
  let A₀ := {x : {v : Fin 49 // sevenHighT0IsLow v} //
    ¬ sevenHighT0InTargetN0 x.1}
  let B₀ := {x : {v : Fin 49 // sevenHighT0IsLow v} //
    ¬ sevenHighT0InSourceN0 x.1}
  let e₁' :
      {x : A₀ // sevenHighT0InTargetN1Only x.1.1} ≃
      {x : B₀ // sevenHighT0InSourceN1Only x.1.1} :=
    liftEquivThroughSubtypes
      (fun x : {v : Fin 49 // sevenHighT0IsLow v} =>
        ¬ sevenHighT0InTargetN0 x.1)
      (fun x : {v : Fin 49 // sevenHighT0IsLow v} =>
        ¬ sevenHighT0InSourceN0 x.1)
      (fun x => sevenHighT0InTargetN1Only x.1)
      (fun x => sevenHighT0InSourceN1Only x.1)
      (fun x hx => sevenHighT0_target_blocks_disjoint x.1 hx)
      (fun x hx => sevenHighT0_source_blocks_disjoint x.1 hx)
      (sevenHighT0N1OnlyLowEquiv e₁ hroot₁)
  let erest :
      {x : A₀ // ¬ sevenHighT0InTargetN1Only x.1.1} ≃
      {x : B₀ // ¬ sevenHighT0InSourceN1Only x.1.1} :=
    Fintype.equivOfCardEq sevenHighT0_remaining_nested_card
  let ecompl : A₀ ≃ B₀ :=
    equivOfSubtypeAndCompl
      (fun x : A₀ => sevenHighT0InTargetN1Only x.1.1)
      (fun x : B₀ => sevenHighT0InSourceN1Only x.1.1)
      e₁' erest
  exact equivOfSubtypeAndCompl
    (fun x : {v : Fin 49 // sevenHighT0IsLow v} =>
      sevenHighT0InTargetN0 x.1)
    (fun x : {v : Fin 49 // sevenHighT0IsLow v} =>
      sevenHighT0InSourceN0 x.1)
    (sevenHighT0N0LowEquiv e₀) ecompl

/-- The complete target-to-source vertex permutation.  It fixes the seven
high vertices, sends `7..14` onto support fiber zero in `e₀` coordinates,
sends `15..21` onto fiber one minus fiber zero in `e₁` coordinates, and uses
an arbitrary equivalence on the remaining 27 low vertices. -/
noncomputable def sevenHighT0GlobalPerm
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0) :
    Fin 49 ≃ Fin 49 :=
  equivOfSubtypeAndCompl
    (fun v : Fin 49 => v.val < 7) (fun v : Fin 49 => v.val < 7)
    (Equiv.refl _) (sevenHighT0LowEquiv e₀ e₁ hroot₁)

theorem sevenHighT0GlobalPerm_fix_high
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) (hv : v.val < 7) :
    sevenHighT0GlobalPerm e₀ e₁ hroot₁ v = v := by
  exact equivOfSubtypeAndCompl_apply_pos _ _ _ _ v hv

theorem sevenHighT0GlobalPerm_apply_targetN0
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) (hv : v ∈ sevenHighT0TargetN0) :
    sevenHighT0GlobalPerm e₀ e₁ hroot₁ v =
      (sevenHighT0N0BlockEquiv e₀ ⟨v, hv⟩).1 := by
  have hlow : ¬v.val < 7 := sevenHighT0_targetN0_isLow v hv
  rw [show sevenHighT0GlobalPerm e₀ e₁ hroot₁ v =
      (sevenHighT0LowEquiv e₀ e₁ hroot₁ ⟨v, hlow⟩).1 by
    exact equivOfSubtypeAndCompl_apply_neg _ _ _ _ v hlow]
  simp [sevenHighT0LowEquiv, equivOfSubtypeAndCompl, Equiv.sumCompl,
    sevenHighT0N0LowEquiv, liftEquivThroughSubtypes, hv]

theorem sevenHighT0GlobalPerm_targetN0_mem_source
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) (hv : v ∈ sevenHighT0TargetN0) :
    sevenHighT0GlobalPerm e₀ e₁ hroot₁ v ∈
      sevenHighT0SupportFiber 0 := by
  rw [sevenHighT0GlobalPerm_apply_targetN0 e₀ e₁ hroot₁ v hv]
  exact (sevenHighT0N0BlockEquiv e₀ ⟨v, hv⟩).2

theorem sevenHighT0GlobalPerm_apply_targetN1Only
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) (hv : v ∈ sevenHighT0TargetN1Only) :
    sevenHighT0GlobalPerm e₀ e₁ hroot₁ v =
      (sevenHighT0N1OnlyBlockEquiv e₁ hroot₁ ⟨v, hv⟩).1 := by
  have hlow : ¬v.val < 7 := sevenHighT0_targetN1Only_isLow v hv
  have hn0 : ¬v ∈ sevenHighT0TargetN0 :=
    sevenHighT0_target_blocks_disjoint v hv
  rw [show sevenHighT0GlobalPerm e₀ e₁ hroot₁ v =
      (sevenHighT0LowEquiv e₀ e₁ hroot₁ ⟨v, hlow⟩).1 by
    exact equivOfSubtypeAndCompl_apply_neg _ _ _ _ v hlow]
  simp [sevenHighT0LowEquiv, equivOfSubtypeAndCompl, Equiv.sumCompl,
    sevenHighT0N1OnlyLowEquiv, liftEquivThroughSubtypes, hv, hn0]

theorem sevenHighT0GlobalPerm_targetN1Only_mem_source
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) (hv : v ∈ sevenHighT0TargetN1Only) :
    sevenHighT0GlobalPerm e₀ e₁ hroot₁ v ∈
      sevenHighT0SupportFiber 1 \ sevenHighT0SupportFiber 0 := by
  rw [sevenHighT0GlobalPerm_apply_targetN1Only e₀ e₁ hroot₁ v hv]
  exact (sevenHighT0N1OnlyBlockEquiv e₁ hroot₁ ⟨v, hv⟩).2

theorem sevenHighT0GlobalPerm_root
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (hroot₀ : e₀ ⟨7, sevenHighT0SupportFiber_zero_mem_seven⟩ = 0)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0) :
    sevenHighT0GlobalPerm e₀ e₁ hroot₁ 7 = 7 := by
  rw [sevenHighT0GlobalPerm_apply_targetN0 e₀ e₁ hroot₁ 7 (by native_decide)]
  exact sevenHighT0N0BlockEquiv_root e₀ hroot₀

theorem sevenHighT0GlobalPerm_maps_low_to_low
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) (hv : ¬v.val < 7) :
    ¬(sevenHighT0GlobalPerm e₀ e₁ hroot₁ v).val < 7 := by
  rw [show sevenHighT0GlobalPerm e₀ e₁ hroot₁ v =
      (sevenHighT0LowEquiv e₀ e₁ hroot₁ ⟨v, hv⟩).1 by
    exact equivOfSubtypeAndCompl_apply_neg _ _ _ _ v hv]
  exact (sevenHighT0LowEquiv e₀ e₁ hroot₁ ⟨v, hv⟩).2

theorem sevenHighT0GlobalPerm_preserves_high_prefix
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) :
    (sevenHighT0GlobalPerm e₀ e₁ hroot₁ v).val < 7 ↔ v.val < 7 := by
  constructor
  · intro hev
    by_contra hv
    exact sevenHighT0GlobalPerm_maps_low_to_low e₀ e₁ hroot₁ v hv hev
  · intro hv
    rw [sevenHighT0GlobalPerm_fix_high e₀ e₁ hroot₁ v hv]
    exact hv

theorem sevenHighT0GlobalPerm_targetN0_iff_sourceN0
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) :
    v ∈ sevenHighT0TargetN0 ↔
      sevenHighT0GlobalPerm e₀ e₁ hroot₁ v ∈
        sevenHighT0SupportFiber 0 := by
  constructor
  · exact sevenHighT0GlobalPerm_targetN0_mem_source e₀ e₁ hroot₁ v
  · intro hev
    let t := (sevenHighT0N0BlockEquiv e₀).symm
      ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ v, hev⟩
    have htmap := sevenHighT0GlobalPerm_apply_targetN0
      e₀ e₁ hroot₁ t.1 t.2
    have hsame : sevenHighT0GlobalPerm e₀ e₁ hroot₁ t.1 =
        sevenHighT0GlobalPerm e₀ e₁ hroot₁ v := by
      rw [htmap]
      exact congrArg Subtype.val
        ((sevenHighT0N0BlockEquiv e₀).apply_symm_apply
          ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ v, hev⟩)
    have htv : t.1 = v :=
      (sevenHighT0GlobalPerm e₀ e₁ hroot₁).injective hsame
    simpa [htv] using t.2

theorem sevenHighT0GlobalPerm_targetN1Only_iff_sourceN1Only
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) :
    v ∈ sevenHighT0TargetN1Only ↔
      sevenHighT0GlobalPerm e₀ e₁ hroot₁ v ∈
        sevenHighT0SupportFiber 1 \ sevenHighT0SupportFiber 0 := by
  constructor
  · exact sevenHighT0GlobalPerm_targetN1Only_mem_source e₀ e₁ hroot₁ v
  · intro hev
    let t := (sevenHighT0N1OnlyBlockEquiv e₁ hroot₁).symm
      ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ v, hev⟩
    have htmap := sevenHighT0GlobalPerm_apply_targetN1Only
      e₀ e₁ hroot₁ t.1 t.2
    have hsame : sevenHighT0GlobalPerm e₀ e₁ hroot₁ t.1 =
        sevenHighT0GlobalPerm e₀ e₁ hroot₁ v := by
      rw [htmap]
      exact congrArg Subtype.val
        ((sevenHighT0N1OnlyBlockEquiv e₁ hroot₁).apply_symm_apply
          ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ v, hev⟩)
    have htv : t.1 = v :=
      (sevenHighT0GlobalPerm e₀ e₁ hroot₁).injective hsame
    simpa [htv] using t.2

theorem sevenHighT0GlobalPerm_targetN1_iff_sourceN1
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (hroot₀ : e₀ ⟨7, sevenHighT0SupportFiber_zero_mem_seven⟩ = 0)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) :
    (v.val = 7 ∨ (15 ≤ v.val ∧ v.val < 22)) ↔
      sevenHighT0GlobalPerm e₀ e₁ hroot₁ v ∈
        sevenHighT0SupportFiber 1 := by
  constructor
  · rintro (hv7 | hvonly)
    · have hv : v = 7 := Fin.ext hv7
      rw [hv, sevenHighT0GlobalPerm_root e₀ hroot₀ e₁ hroot₁]
      exact sevenHighT0SupportFiber_one_mem_seven
    · have hv : v ∈ sevenHighT0TargetN1Only := by
        simp [sevenHighT0TargetN1Only, hvonly]
      exact (Finset.mem_sdiff.mp
        (sevenHighT0GlobalPerm_targetN1Only_mem_source
          e₀ e₁ hroot₁ v hv)).1
  · intro hev
    by_cases he0 : sevenHighT0GlobalPerm e₀ e₁ hroot₁ v ∈
        sevenHighT0SupportFiber 0
    · have hinter : sevenHighT0GlobalPerm e₀ e₁ hroot₁ v ∈
          sevenHighT0SupportFiber 0 ∩ sevenHighT0SupportFiber 1 :=
        Finset.mem_inter.mpr ⟨he0, hev⟩
      rw [sevenHighT0SupportFiber_zero_one_inter] at hinter
      have he7 : sevenHighT0GlobalPerm e₀ e₁ hroot₁ v = 7 := by
        simpa using hinter
      have hv7 : v = 7 := by
        apply (sevenHighT0GlobalPerm e₀ e₁ hroot₁).injective
        rw [he7, sevenHighT0GlobalPerm_root e₀ hroot₀ e₁ hroot₁]
      exact Or.inl (congrArg Fin.val hv7)
    · have hdiff : sevenHighT0GlobalPerm e₀ e₁ hroot₁ v ∈
          sevenHighT0SupportFiber 1 \ sevenHighT0SupportFiber 0 :=
        Finset.mem_sdiff.mpr ⟨hev, he0⟩
      have hv := (sevenHighT0GlobalPerm_targetN1Only_iff_sourceN1Only
        e₀ e₁ hroot₁ v).mpr hdiff
      exact Or.inr (by
        simpa [sevenHighT0TargetN1Only] using
          (Finset.mem_filter.mp hv).2)

@[simp] theorem sevenHighT0TargetN0Coord_val
    (v : {v : Fin 49 // v ∈ sevenHighT0TargetN0}) :
    (sevenHighT0TargetN0Coord v).val = v.1.val - 7 := by
  rfl

@[simp] theorem sevenHighT0TargetN1OnlyCoord_val
    (v : {v : Fin 49 // v ∈ sevenHighT0TargetN1Only}) :
    (sevenHighT0TargetN1OnlyCoord v).1.val = v.1.val - 14 := by
  rfl

theorem sevenHighT0GlobalPerm_targetN0_coord
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) (hv : v ∈ sevenHighT0TargetN0) :
    e₀ ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ v,
      sevenHighT0GlobalPerm_targetN0_mem_source e₀ e₁ hroot₁ v hv⟩ =
      sevenHighT0TargetN0Coord ⟨v, hv⟩ := by
  rw [← e₀.apply_symm_apply (sevenHighT0TargetN0Coord ⟨v, hv⟩)]
  apply congrArg e₀
  apply Subtype.ext
  exact sevenHighT0GlobalPerm_apply_targetN0 e₀ e₁ hroot₁ v hv

theorem sevenHighT0GlobalPerm_targetN1Only_coord
    (e₀ : SevenHighT0Fiber 0 ≃ Fin 8)
    (e₁ : SevenHighT0Fiber 1 ≃ Fin 8)
    (hroot₁ : e₁ ⟨7, sevenHighT0SupportFiber_one_mem_seven⟩ = 0)
    (v : Fin 49) (hv : v ∈ sevenHighT0TargetN1Only) :
    e₁ ⟨sevenHighT0GlobalPerm e₀ e₁ hroot₁ v,
      (Finset.mem_sdiff.mp
        (sevenHighT0GlobalPerm_targetN1Only_mem_source
          e₀ e₁ hroot₁ v hv)).1⟩ =
      (sevenHighT0TargetN1OnlyCoord ⟨v, hv⟩).1 := by
  rw [← e₁.apply_symm_apply
    (sevenHighT0TargetN1OnlyCoord ⟨v, hv⟩).1]
  apply congrArg e₁
  apply Subtype.ext
  exact sevenHighT0GlobalPerm_apply_targetN1Only e₀ e₁ hroot₁ v hv

end

end Erdos85
