import Proofs.Erdos85EqualCycleLabeling
import Proofs.Erdos85FrequencyPairDichotomy
import Proofs.Erdos85FrequencyPairFive

/-!
# Residual arithmetic of the equal-cycle branch

Combining the equal-cycle labeling extraction with the complete
prime-frequency square/nonsquare dichotomy over `ℂ`
(`false_of_graph_frequencyPair_prime`), every prime divisor `p ≥ 7` of
the common cycle length is impossible.  Hence for an extremal even-order
graph whose defect components all have one size `r`, only the residual
arithmetic remains: `5 ∣ r` or `r` is a power of three.

The two surviving cases are exactly the special-prime terminals under
construction: the order-five branch and the `3`-primary branch (order
nine plus the `r = 3` triangle terminal).
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- **Equal-cycle residual classification.**  If every component of the
second-order defect graph has the same size `r`, then `5 ∣ r` or `r` is a
power of three: any prime divisor `p ≥ 7` is eliminated by the
frequency-pair dichotomy at a primitive complex `p`-th root of unity. -/
theorem equalCycle_five_dvd_or_three_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ}
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hlen : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r) :
    5 ∣ r ∨ ∃ k : ℕ, r = 3 ^ k := by
  classical
  obtain ⟨hr3, hrOdd, hoddC, -⟩ :=
    equalCycle_length_facts G hfree hd hdeven hmin hcard hlen
  rcases odd_cycleLength_classification hr3 hrOdd with
    ⟨p, hpPrime, hp7, hpd, hq⟩ | h5 | h3pow
  · exfalso
    haveI : NeZero r := ⟨by omega⟩
    haveI : NeZero p := ⟨by have := hpPrime.two_le; omega⟩
    obtain ⟨u, hu, huRange, huD, hsep⟩ :=
      exists_equalCycle_labeling G hfree hd hdeven hmin hcard hlen
    obtain ⟨b, hb⟩ := exists_add_self_eq_one_of_odd hrOdd
    have hζ : IsPrimitiveRoot
        (Complex.exp (2 * Real.pi * Complex.I / p)) p :=
      Complex.isPrimitiveRoot_exp p (by have := hpPrime.two_le; omega)
    have hr7 : 7 ≤ r :=
      le_trans hp7 (Nat.le_of_dvd (by omega) hpd)
    exact false_of_graph_frequencyPair_prime G hfree hd hdeven hmin hcard
      hr7 hrOdd hp7 hpPrime hpd hq u hu huRange huD (fun hce x y ↦
        hsep hce x y) hoddC b hb hζ
  · exact Or.inl h5
  · exact Or.inr h3pow

/-- **Residual reduction after the order-five norm argument.**  Under the
common-length hypothesis, the defect-cycle length is a power of three. -/
theorem equalCycle_three_pow
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ}
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hlen : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r) :
    ∃ k : ℕ, r = 3 ^ k := by
  rcases equalCycle_five_dvd_or_three_pow
      G hfree hd hdeven hmin hcard hlen with h5 | h3
  · exact (false_of_equalCycle_five_dvd
      G hfree hd hdeven hmin hcard hlen h5).elim
  · exact h3

end

end Erdos85
