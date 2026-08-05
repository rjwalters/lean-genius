import Proofs.Erdos85FrequencyPairSquareBranch
import Proofs.Erdos85GraphPrimeFourierNonsquare
import Proofs.Erdos85FrequencyScalar

/-!
# Complete prime-frequency square/nonsquare dichotomy

Over `ℂ` the frequency scalar is nonzero.  It is therefore either a
nonzero square, handled by the convolution branch, or a nonsquare, handled
by trace vanishing and prime Fourier parity.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem false_of_graph_frequencyPair_prime
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r p : ℕ} [NeZero r] [NeZero p]
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 7 ≤ r) (hrOdd : Odd r)
    (hp7 : 7 ≤ p) (hpPrime : p.Prime) (hpdiv : p ∣ r)
    (hoddQuotient : Odd (r / p))
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hsep : ∀ {c e : (secondOrderDefectGraph G).ConnectedComponent},
      c ≠ e → ∀ x y, u c x ≠ u e y)
    (hoddComponents : Odd (Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent))
    (b : ZMod r) (hb : b + b = 1)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ p) : False := by
  let scalar : ℂ := (d : ℂ) - 1 - (ζ + ζ⁻¹)
  have hscalar0 : scalar ≠ 0 := complex_frequencyScalar_ne_zero hd hζ
  by_cases hsquare : IsSquare scalar
  · obtain ⟨s, hs⟩ := hsquare
    have hκ : scalar = s * s := by simpa [pow_two] using hs
    have hs0 : s ≠ 0 := by
      intro h
      apply hscalar0
      rw [hκ, h]
      simp
    exact false_of_graph_frequencyPair_square G hfree hd hdeven hmin hcard
      hr hrOdd hp7 hpPrime hpdiv hoddQuotient u hu huRange huD hsep
        hoddComponents b hb hζ hs0 hκ
  · exact false_of_graph_frequencyPair_nonsquare G hfree hd hdeven hmin
      hcard (by omega) hrOdd (by omega) hpPrime hpdiv hoddQuotient u hu huRange huD hsep
        hoddComponents b hb hζ hsquare

end

end Erdos85
