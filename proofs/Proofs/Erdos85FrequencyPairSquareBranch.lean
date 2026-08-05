import Proofs.Erdos85FrequencyPairTransport
import Proofs.Erdos85PrimeFourierSquare
import Proofs.Erdos85GraphProjectedConvolutionTerminal

/-!
# Square-branch closure of the frequency-pair bridge

This file connects the graph-facing frequency-pair bridge
(`Erdos85FrequencyPairTransport`) to the square Fourier branch
(`Erdos85PrimeFourierSquare`) and the projected-convolution terminal
(`Erdos85GraphProjectedConvolutionTerminal`).

Given the equal-odd-cycle labeling data of the second-order defect
two-factor and a square root `s` of `d - 1 - ζ - ζ⁻¹` in a
characteristic-zero field containing a primitive `p`-th root `ζ`, the
restricted adjacency operator `T` satisfies all four hypotheses of
`cyclicConvolution_anchor_constant_of_frequencyPair_trace`:

1. `T² = s² • id`   (transported even second-order matrix equation);
2. even `finrank` of the frequency eigenspace (`= 2 · #cycles`);
3. `trace T = 2 · ∑ x, projectedMultiplicity … x · ζ^x`;
4. `s² = (d - 1) - ζ - ζ⁻¹`.

The resulting convolution constancy is exactly the `hconstant`
hypothesis of `false_of_graph_projectedAnchor_convolution_constancy`, so
the square branch terminates in `False` for every prime `p ≥ 7` dividing
the common cycle length.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Assembling total bijectivity of an equal-cycle labeling from per-cycle
injectivity, separation, and covering. -/
theorem cycleLabeling_bijective
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    {r : ℕ} [NeZero r] {u : C → ZMod r → V}
    (hu : ∀ c, Function.Injective (u c))
    (hsep : ∀ {c e : C}, c ≠ e → ∀ x y, u c x ≠ u e y)
    (hcover : ∀ v : V, ∃ c x, u c x = v) :
    Function.Bijective (cycleLabeling u) := by
  constructor
  · rintro ⟨x, c⟩ ⟨y, e⟩ h
    by_cases hce : c = e
    · subst hce
      exact Prod.ext (hu c h) rfl
    · exact absurd h (hsep hce x y)
  · intro v
    obtain ⟨c, x, hcx⟩ := hcover v
    exact ⟨(x, c), hcx⟩

/-- **Graph-facing convolution constancy from the frequency-pair square
branch.**  For a symmetric equal-cycle system carrying the even
second-order matrix equation, a primitive `p`-th root `ζ`, and a square
root `s` of `d - 1 - ζ - ζ⁻¹`, the cyclic autoconvolution of the
projected diagonal-anchor multiplicity is constant off the five special
frequencies. -/
theorem graph_projectedAnchor_convolution_constant_of_square
    {K : Type*} [Field K] [CharZero K]
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    {r p : ℕ} [NeZero r] [NeZero p]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : C → ZMod r → V) (hr3 : 3 ≤ r) (hrOdd : Odd r)
    (hpPrime : p.Prime) (hp2 : 2 < p) (hdvd : p ∣ r)
    (hbij : Function.Bijective (cycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {s : K} (hs : s ≠ 0)
    (hκ : (d : K) - 1 - (ζ + ζ⁻¹) = s * s)
    (a : ZMod p) (ha : a ∉ ({0, 1, -1} : Finset (ZMod p))) :
    ∀ g, g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) →
      cyclicConvolution
          (fun y ↦ (projectedMultiplicity (ZMod.castHom hdvd (ZMod p))
            (anchorMultiplicity
              (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) y : ℤ))
          (fun y ↦ (projectedMultiplicity (ZMod.castHom hdvd (ZMod p))
            (anchorMultiplicity
              (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) y : ℤ))
          a =
        cyclicConvolution
          (fun y ↦ (projectedMultiplicity (ZMod.castHom hdvd (ZMod p))
            (anchorMultiplicity
              (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) y : ℤ))
          (fun y ↦ (projectedMultiplicity (ZMod.castHom hdvd (ZMod p))
            (anchorMultiplicity
              (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) y : ℤ))
          g := by
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζsq : ζ ^ 2 ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by norm_num) hp2
  have hζ1 : ζ ≠ 1 := fun h ↦ hζsq (by rw [h, one_pow])
  have hr0 : (r : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hζr : ζ ^ r = 1 := pow_eq_one_of_dvd_of_pow_eq_one hdvd hζp
  have hcomm := labeledAdjMatrix_comm_cycleDefectMatrix (K := K) G D u hr3
    hbij huD hcommZ
  have hTsq := graph_defectEigenspaceRestrict_sq G D u hr3 hbij huD hsqZ
    hcomm hζr hζ1
  rw [hκ] at hTsq
  have heven : Even (Module.finrank K
      (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))) :=
    even_finrank_defectEigenspace hrOdd hζr hζsq
  have htr := graph_trace_eq_two_mul_projected_anchor_fourier G D u hr3
    hrOdd hdvd hbij huD hcommZ hcomm hζp hζsq hr0
  have htrace : LinearMap.trace K
      (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹))
      (defectEigenspaceRestrict (labeledAdjMatrix K G u) hcomm
        (ζ + ζ⁻¹)) =
      2 * ∑ x : ZMod p,
        (((projectedMultiplicity (ZMod.castHom hdvd (ZMod p))
          (anchorMultiplicity
            (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) x : ℤ) :
              K) * primitiveRootCharacter hζ x) := by
    rw [htr]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [primitiveRootCharacter_eq_pow_val hζ]
    push_cast
    ring
  exact cyclicConvolution_anchor_constant_of_frequencyPair_trace hpPrime hζ
    (defectEigenspaceRestrict (labeledAdjMatrix K G u) hcomm (ζ + ζ⁻¹)) s
    (fun y ↦ (projectedMultiplicity (ZMod.castHom hdvd (ZMod p))
      (anchorMultiplicity
        (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))) y : ℤ))
    ((d : ℤ) - 1) a hs hTsq heven htrace
    (by push_cast; linear_combination -hκ) ha

/-- The projected half-point anchor avoids `{0, 1, -1}` for `p ≥ 7`. -/
theorem castHom_half_not_special {r p : ℕ} [NeZero r] [NeZero p]
    (hdvd : p ∣ r) (hp7 : 7 ≤ p) (b : ZMod r) (hb : b + b = 1) :
    ZMod.castHom hdvd (ZMod p) b ∉ ({0, 1, -1} : Finset (ZMod p)) := by
  set a := ZMod.castHom hdvd (ZMod p) b with haDef
  have haa : a + a = 1 := by
    rw [haDef, ← map_add, hb, map_one]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [h] at haa
    have h1 : (1 : ZMod p) = 0 := by linear_combination -haa
    have := ZMod.one_eq_zero_iff.mp h1
    omega
  · intro h
    rw [h] at haa
    have h1 : (1 : ZMod p) = 0 := by linear_combination haa
    have := ZMod.one_eq_zero_iff.mp h1
    omega
  · intro h
    rw [h] at haa
    have h3 : ((3 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination -haa
    have hdvd3 := (ZMod.natCast_eq_zero_iff 3 p).mp h3
    have := Nat.le_of_dvd (by norm_num) hdvd3
    omega

/-- **Square-branch termination.**  For the extremal even-order graph with
equal odd defect cycles of length `r`, a prime `p ≥ 7` dividing `r` with
odd cofactor, and a square root `s` of `d - 1 - ζ - ζ⁻¹` at a primitive
`p`-th root `ζ` in a characteristic-zero field, we reach `False`. -/
theorem false_of_graph_frequencyPair_square
    {K : Type*} [Field K] [CharZero K]
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
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {s : K} (hs : s ≠ 0)
    (hκ : (d : K) - 1 - (ζ + ζ⁻¹) = s * s) : False := by
  have hbij : Function.Bijective (cycleLabeling u) := by
    apply cycleLabeling_bijective hu hsep
    intro v
    have hv : v ∈ ((secondOrderDefectGraph G).connectedComponentMk v).supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ v).mpr rfl
    rw [← huRange ((secondOrderDefectGraph G).connectedComponentMk v)] at hv
    obtain ⟨x, hx⟩ := hv
    exact ⟨_, x, hx⟩
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd hdeven hmin hcard
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree hd hdeven hmin hcard
  have ha := castHom_half_not_special hpdiv hp7 b hb
  refine false_of_graph_projectedAnchor_convolution_constancy G hfree hd
    hdeven hmin hcard hr hrOdd hp7 hpdiv hoddQuotient u hu huRange huD
    hsep hoddComponents b hb ?_
  intro _ _ _ g hg
  exact graph_projectedAnchor_convolution_constant_of_square G
    (secondOrderDefectGraph G) u (by omega) hrOdd hpPrime (by omega)
    hpdiv hbij huD hcommZ hsqZ hζ hs hκ
    (ZMod.castHom hpdiv (ZMod p) b) ha g hg

end

end Erdos85
