import Proofs.Erdos85FrequencyPairTransport
import Proofs.Erdos85PrimeFourierNonsquare
import Proofs.Erdos85GraphProjectedConvolutionTerminal

/-!
# Graph-facing nonsquare prime-frequency contradiction

This file joins the transported frequency-pair operator to the graph parity
terminal.  It is the nonsquare half of the prime-frequency dichotomy.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem false_of_graph_prime_frequency_nonsquare
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r p : ℕ} [NeZero r] [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 4 ≤ r) (hrOdd : Odd r)
    (hpPrime : p.Prime) (hp : 4 ≤ p) (hpdiv : p ∣ r)
    (hoddQuotient : Odd (r / p))
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hbij : Function.Bijective (cycleLabeling u))
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hsep : ∀ {c e : (secondOrderDefectGraph G).ConnectedComponent},
      c ≠ e → ∀ x y, u c x ≠ u e y)
    (hoddComponents : Odd (Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent))
    (hcommZ : G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ)
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V -
          (secondOrderDefectGraph G).adjMatrix ℤ)
    (b : ZMod r) (hb : b + b = 1)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hζp : ζ ^ p = 1) (hζsq : ζ ^ 2 ≠ 1)
    (hnonsquare : ¬ IsSquare ((d : K) - 1 - (ζ + ζ⁻¹))) : False := by
  let C := (secondOrderDefectGraph G).ConnectedComponent
  let D := secondOrderDefectGraph G
  let q := ZMod.castHom hpdiv (ZMod p)
  let a := q b
  let m : ZMod r → ℕ := anchorMultiplicity
    (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
  let c : ZMod p → ℤ := fun y ↦ (projectedMultiplicity q m y : ℤ)
  let M : Matrix (ZMod r × C) (ZMod r × C) K := labeledAdjMatrix K G u
  have hcomm : M * cycleDefectMatrix K C r =
      cycleDefectMatrix K C r * M :=
    labeledAdjMatrix_comm_cycleDefectMatrix G D u (by omega) hbij huD hcommZ
  let T := defectEigenspaceRestrict M hcomm (ζ + ζ⁻¹)
  have hTsq : T * T = ((d : K) - 1 - (ζ + ζ⁻¹)) • LinearMap.id :=
    graph_defectEigenspaceRestrict_sq G D u (by omega) hbij huD hsqZ
      hcomm (pow_eq_one_of_dvd_of_pow_eq_one hpdiv hζp)
      (fun hζ1 ↦ hζsq (by rw [hζ1, one_pow]))
  have hr0 : (r : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have htrace : LinearMap.trace K
      (defectEigenspace (cycleDefectMatrix K C r) (ζ + ζ⁻¹)) T =
      2 * ∑ y : ZMod p, (c y : K) * primitiveRootCharacter hζ y := by
    rw [graph_trace_eq_two_mul_projected_anchor_fourier G D u (by omega)
      hrOdd hpdiv hbij huD hcommZ hcomm hζp hζsq hr0]
    apply congrArg (fun z : K ↦ 2 * z)
    apply Finset.sum_congr rfl
    intro y _
    rw [primitiveRootCharacter_eq_pow_val]
    simp [c, m, q]
  have hbase : ∀ h, Odd (m h) ↔
      2 * h ∈ allowedCycleDifferences r := by
    intro h
    exact odd_graph_diagonalAnchorMultiplicity_iff
      G hfree hd heven hmin hcard (by omega) hrOdd u hu huRange huD
        hsep hoddComponents h
  have hparity : ∀ y, Odd (c y) ↔
      y ∉ ({0, a, -a} : Finset (ZMod p)) := by
    intro y
    have hy := odd_projectedMultiplicity_zmod_castHom_iff
      hpdiv hp hr hrOdd hoddQuotient b hb m hbase y
    dsimp only [c]
    exact_mod_cast hy
  exact false_of_nonsquare_frequencyPair_trace_and_threePoint_parity
    hpPrime hp hζ T ((d : K) - 1 - (ζ + ζ⁻¹)) c a hnonsquare
      hTsq htrace hparity

/-- Nonsquare-branch termination with only the equal-cycle graph data: the
transport equations and total labeling bijection are derived internally. -/
theorem false_of_graph_frequencyPair_nonsquare
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
    (hr : 4 ≤ r) (hrOdd : Odd r)
    (hp4 : 4 ≤ p) (hpPrime : p.Prime) (hpdiv : p ∣ r)
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
    (hnonsquare : ¬ IsSquare ((d : K) - 1 - (ζ + ζ⁻¹))) : False := by
  have hbij : Function.Bijective (cycleLabeling u) := by
    constructor
    · rintro ⟨x, c⟩ ⟨y, e⟩ h
      by_cases hce : c = e
      · subst hce
        exact Prod.ext (hu c h) rfl
      · exact absurd h (hsep hce x y)
    · intro v
      have hv : v ∈ ((secondOrderDefectGraph G).connectedComponentMk v).supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ v).mpr rfl
      rw [← huRange ((secondOrderDefectGraph G).connectedComponentMk v)] at hv
      obtain ⟨x, hx⟩ := hv
      exact ⟨(x, _), hx⟩
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd hdeven hmin hcard
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree hd hdeven hmin hcard
  exact false_of_graph_prime_frequency_nonsquare G hfree hd hdeven hmin
    hcard hr hrOdd hpPrime hp4 hpdiv hoddQuotient u hbij hu huRange huD
      hsep hoddComponents hcommZ hsqZ b hb hζ hζ.pow_eq_one
      (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by omega)) hnonsquare

end

end Erdos85
