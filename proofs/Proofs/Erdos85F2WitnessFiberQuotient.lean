import Proofs.Erdos85ConnectedF2EdgeSwitchSpan

/-!
# The binary witness-fiber switch quotient

Local Baer re-pairings only join occurrences carrying the same witness.
This file identifies their exact quotient: same-witness endpoint switches
kill precisely the kernel of the witness-aggregation map.  Thus there is
one surviving binary coordinate per witness, and removing it requires a
genuinely cross-witness relation.
-/

namespace Erdos85

noncomputable section

/-- Aggregate a binary occurrence vector separately over every witness
fiber. -/
def f2WitnessFiberSum
    {O Y : Type*} [Fintype O] [DecidableEq Y] (label : O → Y) :
    (O → ZMod 2) →ₗ[ZMod 2] (Y → ZMod 2) where
  toFun z y := ∑ x with label x = y, z x
  map_add' z w := by
    ext y
    simp [Finset.sum_add_distrib]
  map_smul' a z := by
    ext y
    simp [Finset.mul_sum]

/-- Binary pair switches whose two occurrences carry the same witness. -/
def f2SameWitnessSwitches
    {O Y : Type*} [DecidableEq O] (label : O → Y) : Set (O → ZMod 2) :=
  {z | ∃ u v, label u = label v ∧ z = f2EndpointSwitch u v}

private theorem zmod2_add_self_fiber (z : ZMod 2) : z + z = 0 := by
  calc
    z + z = (2 : ZMod 2) * z := by ring
    _ = 0 := by
      have h2 : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
      rw [h2, zero_mul]

/-- Every same-witness switch has zero aggregate in every witness fiber. -/
theorem f2SameWitnessSwitches_span_le_fiberSum_ker
    {O Y : Type*} [Fintype O] [DecidableEq O] [DecidableEq Y]
    (label : O → Y) :
    Submodule.span (ZMod 2) (f2SameWitnessSwitches label) ≤
      LinearMap.ker (f2WitnessFiberSum label) := by
  apply Submodule.span_le.mpr
  intro z hz
  obtain ⟨u, v, huv, rfl⟩ := hz
  apply LinearMap.mem_ker.mpr
  ext y
  change (∑ x with label x = y,
    (f2EndpointSwitch u v) x) = 0
  have hsingle (a : O) :
      (∑ x with label x = y,
        (Pi.single a (1 : ZMod 2) : O → ZMod 2) x) =
        if label a = y then 1 else 0 := by
    by_cases hay : label a = y
    · rw [if_pos hay]
      calc
        (∑ x with label x = y,
            (Pi.single a (1 : ZMod 2) : O → ZMod 2) x) =
            (Pi.single a (1 : ZMod 2) : O → ZMod 2) a := by
              apply Finset.sum_eq_single a
              · intro x hx hxa
                simp [hxa]
              · intro ha
                exact (ha (Finset.mem_filter.mpr
                  ⟨Finset.mem_univ a, hay⟩)).elim
        _ = 1 := by simp
    · rw [if_neg hay]
      apply Finset.sum_eq_zero
      intro x hx
      apply Pi.single_eq_of_ne
      intro h
      subst x
      exact hay (Finset.mem_filter.mp hx).2
  simp only [f2EndpointSwitch, Pi.add_apply]
  rw [Finset.sum_add_distrib, hsingle u, hsingle v]
  by_cases huy : label u = y
  · have hvy : label v = y := huv ▸ huy
    rw [if_pos huy, if_pos hvy, zmod2_add_self_fiber]
  · have hvy : label v ≠ y := by
      intro h
      exact huy (huv.trans h)
    rw [if_neg huy, if_neg hvy, zero_add]

/-- **Exact witness-fiber quotient.**  If every witness labels at least one
occurrence, same-witness pair switches span exactly those occurrence vectors
whose total coefficient vanishes in every witness fiber. -/
theorem f2SameWitnessSwitches_span_eq_fiberSum_ker
    {O Y : Type*} [Fintype O] [Fintype Y]
    [DecidableEq O] [DecidableEq Y]
    (label : O → Y) (hsurj : Function.Surjective label) :
    Submodule.span (ZMod 2) (f2SameWitnessSwitches label) =
      LinearMap.ker (f2WitnessFiberSum label) := by
  apply le_antisymm (f2SameWitnessSwitches_span_le_fiberSum_ker label)
  intro z hz
  let root : Y → O := fun y => Classical.choose (hsurj y)
  have hroot : ∀ y, label (root y) = y := fun y =>
    Classical.choose_spec (hsurj y)
  have hrootInjective : Function.Injective root := by
    intro y y' h
    simpa [hroot y, hroot y'] using congrArg label h
  let w : O → ZMod 2 :=
    ∑ x, z x • f2EndpointSwitch (root (label x)) x
  have hwmem : w ∈
      Submodule.span (ZMod 2) (f2SameWitnessSwitches label) := by
    dsimp only [w]
    apply Submodule.sum_mem
    intro x _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨root (label x), x, hroot (label x), rfl⟩
  have hfiber : ∀ y, (∑ x with label x = y, z x) = 0 := by
    intro y
    have hy := congrFun (LinearMap.mem_ker.mp hz) y
    exact hy
  have hw : w = z := by
    ext o
    dsimp only [w]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      f2EndpointSwitch, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    have hsecond :
        (∑ x, z x * (Pi.single x (1 : ZMod 2) : O → ZMod 2) o) = z o := by
      simp [Pi.single_apply]
    rw [hsecond]
    have hfirst :
        (∑ x, z x *
          (Pi.single (root (label x)) (1 : ZMod 2) : O → ZMod 2) o) = 0 := by
      by_cases ho : o = root (label o)
      · calc
          (∑ x, z x *
              (Pi.single (root (label x)) (1 : ZMod 2) : O → ZMod 2)
                o) =
              ∑ x with label x = label o, z x := by
                rw [Finset.sum_filter]
                apply Finset.sum_congr rfl
                intro x _
                simp only [Pi.single_apply]
                by_cases hx : label x = label o
                · have hr : root (label x) = o :=
                    (congrArg root hx).trans ho.symm
                  rw [if_pos hr.symm, if_pos hx, mul_one]
                · have hne : o ≠ root (label x) := by
                    intro h
                    apply hx
                    have hh : label o = label x := by
                      simpa [hroot (label x)] using congrArg label h
                    exact hh.symm
                  rw [if_neg hne, if_neg hx, mul_zero]
          _ = 0 := hfiber (label o)
      · apply Finset.sum_eq_zero
        intro x _
        rw [Pi.single_eq_of_ne]
        simp
        intro h
        apply ho
        have hl : label o = label x := by
          simpa [hroot (label x)] using congrArg label h
        exact h.trans (congrArg root hl).symm
    rw [hfirst, zero_add]
  rw [← hw]
  exact hwmem

end

end Erdos85

#print axioms Erdos85.f2SameWitnessSwitches_span_le_fiberSum_ker
#print axioms Erdos85.f2SameWitnessSwitches_span_eq_fiberSum_ker
