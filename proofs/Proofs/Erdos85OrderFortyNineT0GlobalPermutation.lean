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

end

end Erdos85
