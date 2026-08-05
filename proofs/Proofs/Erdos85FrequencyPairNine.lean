import Proofs.Erdos85OrderNineNormBridge
import Proofs.Erdos85FrequencyPairTransport
import Proofs.Erdos85GraphAnchorSymmetry
import Proofs.Erdos85FrequencyScalar

/-!
# The primitive order-nine graph frequency terminal

This file transports the corrected cubic norm bridge to an equal-cycle
second-order defect graph.  Its headline conclusion is primitive order-nine
Fourier vanishing, together with divisibility by three of the total diagonal
anchor mass.  Identification of that mass with the graph degree is kept as a
separate downstream interface.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

theorem sum_projectedMultiplicity_eq_sum
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (q : X → Y) (m : X → ℕ) :
    ∑ y : Y, projectedMultiplicity q m y = ∑ x : X, m x := by
  change (∑ y : Y, ∑ x ∈ Finset.univ.filter (fun x : X ↦ q x = y), m x) = _
  rw [← Finset.sum_fiberwise Finset.univ q m]

/-- Primitive order-nine Fourier vanishing for graph diagonal anchors. -/
theorem graph_projectedAnchor_orderNine_fourier_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 4 ≤ r) (hrOdd : Odd r) (hdiv : 9 ∣ r)
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hsep : ∀ {c e : (secondOrderDefectGraph G).ConnectedComponent},
      c ≠ e → ∀ x y, u c x ≠ u e y)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 9) :
    let q := ZMod.castHom hdiv (ZMod 9)
    let m : ZMod r → ℕ := anchorMultiplicity
      (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
    let c : ZMod 9 → ℤ := fun y ↦ (projectedMultiplicity q m y : ℤ)
    ∑ y : ZMod 9, (c y : ℂ) * primitiveRootCharacter hζ y = 0 := by
  dsimp only
  let D := secondOrderDefectGraph G
  let q := ZMod.castHom hdiv (ZMod 9)
  let m : ZMod r → ℕ := anchorMultiplicity
    (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
  let c : ZMod 9 → ℤ := fun y ↦ (projectedMultiplicity q m y : ℤ)
  have hbij : Function.Bijective (cycleLabeling u) := by
    constructor
    · rintro ⟨x, e⟩ ⟨y, f⟩ hxy
      by_cases hef : e = f
      · subst hef
        exact Prod.ext (hu e hxy) rfl
      · exact absurd hxy (hsep hef x y)
    · intro v
      have hv : v ∈ (D.connectedComponentMk v).supp :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff _ v).mpr rfl
      rw [← huRange (D.connectedComponentMk v)] at hv
      obtain ⟨x, hx⟩ := hv
      exact ⟨(x, _), hx⟩
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd hdeven hmin hcard
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree hd hdeven hmin hcard
  let scalar : ℂ := (d : ℂ) - 1 - (ζ + ζ⁻¹)
  have hscalar0 : scalar ≠ 0 := complex_frequencyScalar_ne_zero hd hζ
  obtain ⟨s, hs⟩ := Complex.isSquare scalar
  have hκ : scalar = s * s := by simpa [pow_two] using hs
  have hs0 : s ≠ 0 := by
    intro hs
    apply hscalar0
    rw [hκ, hs]
    simp
  obtain ⟨w, hw⟩ := graph_projected_anchor_fourier_eq_int_mul_of_sq
    (K := ℂ) G D u (by omega) hrOdd hdiv hbij huD hcommZ hsqZ
      hζ.pow_eq_one (hζ.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
      hs0 hκ
  have hpowerChar :
      (∑ y : ZMod 9, (c y : ℂ) * primitiveRootCharacter hζ y) =
        ∑ y : ZMod 9,
          ((projectedMultiplicity q m y : ℕ) : ℂ) * ζ ^ y.val := by
    apply Finset.sum_congr rfl
    intro y _
    rw [primitiveRootCharacter_eq_pow_val]
    simp [c, q, m]
  have hH : (∑ y : ZMod 9,
      (c y : ℂ) * primitiveRootCharacter hζ y) = (w : ℂ) * s := by
    rw [hpowerChar]
    exact hw
  have hsymm : ∀ y, c (-y) = c y := by
    intro y
    dsimp only [c]
    exact_mod_cast graph_projectedAnchorMultiplicity_neg_eq
      G hfree hd hdeven hmin hcard (by omega) hrOdd hdiv u hu huD y
  have hFourierSq :
      (∑ y : ZMod 9, (c y : ℂ) * primitiveRootCharacter hζ y) *
          (∑ y : ZMod 9, (c y : ℂ) * primitiveRootCharacter hζ y) =
        ((w * w : ℤ) : ℂ) * (((d - 1 : ℕ) : ℂ) - ζ - ζ⁻¹) := by
    rw [hH]
    have hd1 : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by
      simpa using (Nat.cast_sub (R := ℂ) (by omega : 1 ≤ d))
    rw [hd1]
    dsimp only [scalar] at hκ
    have hκ' : (d : ℂ) - 1 - ζ - ζ⁻¹ = s * s := by
      linear_combination hκ
    rw [hκ']
    push_cast
    ring
  have hodd : Odd (d - 1) := by
    obtain ⟨k, hk⟩ := hdeven
    refine ⟨k - 1, ?_⟩
    omega
  exact orderNine_fourier_eq_zero_of_square_identity hζ c hsymm
    (d - 1) hodd w hFourierSq

/-- Consequently, three divides the total diagonal-anchor mass. -/
theorem three_dvd_graph_totalAnchorMass_of_nine_dvd_cycleLength
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 4 ≤ r) (hrOdd : Odd r) (hdiv : 9 ∣ r)
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hsep : ∀ {c e : (secondOrderDefectGraph G).ConnectedComponent},
      c ≠ e → ∀ x y, u c x ≠ u e y) :
    (3 : ℤ) ∣ ∑ t : ZMod r,
      (anchorMultiplicity
        (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c)) t : ℤ) := by
  let q := ZMod.castHom hdiv (ZMod 9)
  let m : ZMod r → ℕ := anchorMultiplicity
    (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
  let c : ZMod 9 → ℤ := fun y ↦ (projectedMultiplicity q m y : ℤ)
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)
  have hζ : IsPrimitiveRoot ζ 9 :=
    Complex.isPrimitiveRoot_exp 9 (by norm_num)
  have hzero : ∑ y : ZMod 9,
      (c y : ℂ) * primitiveRootCharacter hζ y = 0 := by
    exact graph_projectedAnchor_orderNine_fourier_eq_zero
      G hfree hd hdeven hmin hcard hr hrOdd hdiv u hu huRange huD hsep hζ
  have hdvd := three_dvd_sum_of_orderNine_character_eq_zero hζ c hzero
  have hsumNat : (∑ y : ZMod 9, projectedMultiplicity q m y) =
      ∑ t : ZMod r, m t := sum_projectedMultiplicity_eq_sum q m
  have hsumInt : (∑ y : ZMod 9, c y) =
      ∑ t : ZMod r, (m t : ℤ) := by
    dsimp only [c]
    exact_mod_cast hsumNat
  rw [hsumInt] at hdvd
  exact hdvd

end

end Erdos85
