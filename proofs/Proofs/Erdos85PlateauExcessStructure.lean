import Proofs.Erdos85ExcessDefectRegular
import Proofs.Erdos85OddBoundaryClean

/-!
# Clean localization of a plateau core in the positive-excess band

The historical parity-free strict Moore bound imports finite computational
certificates through the even first-order classification.  For the eventual
monotonicity program we can keep that issue completely isolated.  The clean
Moore bound localizes a core below the next layer to either the single
first-order cardinality `d(d-1)+2`, or to a nonnegative second-order excess.
In the latter case the core is regular and its combined defect graph has
degree `e+2`, with the order-free defect operator identities.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A regular plateau witness at second-order excess `e`, together with the
defect regularity and operator identities needed by the spectral program. -/
def PositiveExcessPlateauData (m d e : ℕ) : Prop :=
  m = d * (d - 1) + 3 + e ∧
  e ≤ d - 4 ∧
  ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
    ¬ containsC4 (Fin m) G ∧
    (∀ x, G.degree x = d) ∧
    (∀ x, (secondOrderDefectGraph G).degree x = e + 2) ∧
    G.adjMatrix ℤ * G.adjMatrix ℤ =
      (↑d - 1 : ℤ) • (1 : Matrix (Fin m) (Fin m) ℤ) +
        FriendshipTheoremOQ01.onesMatrix (Fin m) -
          (secondOrderDefectGraph G).adjMatrix ℤ ∧
    G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ ∧
    ∀ (H : SimpleGraph (Fin (m + 1))) (_ : DecidableRel H.Adj),
      d ≤ H.minDegree → containsC4 (Fin (m + 1)) H

/-- **Clean plateau-band dichotomy.** Below `d²`, a degree-`d` plateau core
is either at the one isolated first-order cardinality, or carries the full
positive-excess defect package with `0 ≤ e ≤ d-4`.

Unlike `C4PlateauCore.second_strict_moore_lower`, this theorem uses no finite
classification of the even first-order templates. -/
theorem C4PlateauCore.firstOrder_or_positiveExcessData
    {m d : ℕ} (hm : 4 ≤ m) (hd : 4 ≤ d)
    (hcore : C4PlateauCore m d) (hsize : m < d * d) :
    m = d * (d - 1) + 2 ∨
      ∃ e, PositiveExcessPlateauData m d e := by
  have hmLower : d * (d - 1) + 2 ≤ m := by
    rcases hcore with ⟨G, hdec, hmin, hfree, _hcover, _hnext⟩
    letI : DecidableRel G.Adj := hdec
    letI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
    simpa using mul_pred_add_two_le_card_of_c4Free_minDegree
      G (by omega) hmin.ge hfree
  by_cases hfirst : m = d * (d - 1) + 2
  · exact Or.inl hfirst
  · right
    have hmSecond : d * (d - 1) + 3 ≤ m := by omega
    let e := m - (d * (d - 1) + 3)
    have hme : m = d * (d - 1) + 3 + e := by
      dsimp [e]
      omega
    have he : e ≤ d - 4 := by
      have hdcalc : d * d = d * (d - 1) + d := by
        calc
          d * d = d * ((d - 1) + 1) := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
          _ = d * (d - 1) + d := by ring
      rw [hme, hdcalc] at hsize
      omega
    have hnextLayer : m < (d + 1) * (d - 1) + 1 := by
      have hcalc : (d + 1) * (d - 1) + 1 = d * d := by
        calc
          (d + 1) * (d - 1) + 1 =
              d * (d - 1) + ((d - 1) + 1) := by ring
          _ = d * (d - 1) + d := by
            rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
          _ = d * d := by
            calc
              d * (d - 1) + d = d * ((d - 1) + 1) := by ring
              _ = d * d := by
                rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
      rwa [hcalc]
    obtain ⟨G, hdec, hfree, hreg, hnext⟩ :=
      hcore.exists_regular_core hm hnextLayer
    letI : DecidableRel G.Adj := hdec
    letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
    letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
    refine ⟨e, hme, he, G, hdec, hfree, hreg, ?_, ?_, ?_, hnext⟩
    · intro x
      exact secondOrderDefectGraph_degree_eq_excess_add_two
        G hfree hreg (by simpa using hme) x
    · exact adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
    · exact adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg

/-- Odd degree removes the first-order alternative by the clean modular
trace theorem, so every odd-degree core below `d²` lies in the genuine
second-order excess band. -/
theorem C4PlateauCore.exists_positiveExcessData_of_odd
    {m d : ℕ} (hm : 4 ≤ m) (hd : 4 ≤ d) (hodd : Odd d)
    (hcore : C4PlateauCore m d) (hsize : m < d * d) :
    ∃ e, PositiveExcessPlateauData m d e := by
  rcases hcore.firstOrder_or_positiveExcessData hm hd hsize with
    hfirst | hexcess
  · rcases hcore with ⟨G, hdec, hmin, hfree, _hcover, _hnext⟩
    letI : DecidableRel G.Adj := hdec
    exact (hfree (containsC4_of_odd_firstOrder
      G (by omega) hodd hmin.ge (by simpa using hfirst))).elim
  · exact hexcess

end

end Erdos85
