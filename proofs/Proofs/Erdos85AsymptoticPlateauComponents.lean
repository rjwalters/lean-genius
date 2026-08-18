import Proofs.Erdos85PlateauDivergence
import Proofs.Erdos85QuadraticPlateauComponents

/-!
# Asymptotic component count for plateau cores

The quadratic conductor places a degree-`d` plateau core below `36d²`, while
the clean Moore bound places at least `d(d-1)+2` vertices in each connected
component.  The ratio tends to `36`.  Once `d ≥ 35`, elementary arithmetic
therefore improves the uniform component bound from 43 to 36.  Since plateau
degrees tend to infinity, this sharper bound applies eventually.
-/

namespace Erdos85

open SimpleGraph Filter

/-- Above degree 34, a plateau core admits a realization with at most 36
connected components. -/
theorem C4PlateauCore.exists_component_count_lt_thirtySeven
    {m d : ℕ} (hm : 4 ≤ m) (hd : 35 ≤ d)
    (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      Fintype.card G.ConnectedComponent < 37 := by
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  let L := d * (d - 1) + 2
  let k := Fintype.card G.ConnectedComponent
  have hcomponents : k * L ≤ m := by
    simpa [k, L] using connectedComponent_count_mul_cleanMoore_le_card
      G hfree (by omega) hmin.ge
  have hmUpper : m < 36 * d * d := by
    have h := C4PlateauCore.order_succ_lt_quadratic hm
      ⟨G, hdec, hmin, hfree, hcover, hnext⟩
    omega
  have hratio : 36 * d * d < 37 * L := by
    obtain ⟨a, rfl⟩ : ∃ a, d = a + 35 := ⟨d - 35, by omega⟩
    dsimp [L]
    nlinarith
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  by_contra hk
  have hk37 : 37 ≤ k := by omega
  have hscale : 37 * L ≤ k * L :=
    Nat.mul_le_mul_right L hk37
  have : 37 * L ≤ m := hscale.trans hcomponents
  omega

/-- Eventually, every plateau core has a representative with at most 36
connected components. -/
theorem eventually_plateauCore_exists_component_count_lt_thirtySeven :
    ∀ᶠ m in atTop, ∀ {d : ℕ}, C4PlateauCore m d →
      ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
        G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
        Fintype.card G.ConnectedComponent < 37 := by
  filter_upwards [eventually_ge_atTop 4,
    eventually_plateauCore_degree_ge 35] with m hm hdegree
  intro d hcore
  exact hcore.exists_component_count_lt_thirtySeven hm (hdegree hcore)

end Erdos85
