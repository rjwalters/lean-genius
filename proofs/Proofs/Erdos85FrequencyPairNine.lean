import Proofs.Erdos85OrderNineNormBridge
import Proofs.Erdos85OrderThreeNormBridge
import Proofs.Erdos85FrequencyPairTransport
import Proofs.Erdos85GraphAnchorSymmetry
import Proofs.Erdos85FrequencyScalar
import Proofs.Erdos85DifferenceArrayBoundary
import Proofs.Erdos85EqualCycleLabeling

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

theorem sum_anchorMultiplicity_eq_sum_card
    {I Z : Type*} [Fintype I] [DecidableEq I]
    [Fintype Z] [DecidableEq Z] (A : I → Finset Z) :
    ∑ z : Z, anchorMultiplicity A z = ∑ i : I, (A i).card := by
  calc
    (∑ z : Z, anchorMultiplicity A z) =
        ∑ z : Z, ∑ i : I, if z ∈ A i then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro z _
          simp only [anchorMultiplicity, Finset.card_eq_sum_ones]
          rw [Finset.sum_filter]
    _ = ∑ i : I, ∑ z : Z, if z ∈ A i then 1 else 0 :=
      Finset.sum_comm
    _ = ∑ i : I, (A i).card := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_boole]
      simp

theorem projectedMultiplicity_fourier_eq_sum_cyclePow
    {K : Type*} [Field K] {r p : ℕ} [NeZero r] [NeZero p]
    (hdiv : p ∣ r) {ξ : K} (hξp : ξ ^ p = 1) (m : ZMod r → ℕ) :
    ∑ y : ZMod p,
        ((projectedMultiplicity (ZMod.castHom hdiv (ZMod p)) m y : ℕ) : K) *
          ξ ^ y.val =
      ∑ t : ZMod r, (m t : K) * cyclePow ξ t := by
  symm
  simpa only [projectedMultiplicity, projectionFiber, Nat.cast_sum,
    Nat.cast_ofNat, Finset.sum_mul] using
    (sum_mul_cyclePow_eq_fiberwise (K := K) hdiv hξp
      (fun t : ZMod r ↦ (m t : K)))

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

/-- In the nonsquare-degree branch, the projected order-three anchor
Fourier coefficient also vanishes. -/
theorem graph_projectedAnchor_orderThree_fourier_eq_zero_of_degree_nonsquare
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 4 ≤ r) (hrOdd : Odd r) (hdiv : 3 ∣ r)
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hsep : ∀ {c e : (secondOrderDefectGraph G).ConnectedComponent},
      c ≠ e → ∀ x y, u c x ≠ u e y)
    (hnonsquare : ¬ IsSquare d)
    {η : ℂ} (hη : IsPrimitiveRoot η 3) :
    let q := ZMod.castHom hdiv (ZMod 3)
    let m : ZMod r → ℕ := anchorMultiplicity
      (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
    let c : ZMod 3 → ℤ := fun y ↦ (projectedMultiplicity q m y : ℤ)
    ∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y = 0 := by
  dsimp only
  let D := secondOrderDefectGraph G
  let q := ZMod.castHom hdiv (ZMod 3)
  let m : ZMod r → ℕ := anchorMultiplicity
    (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
  let c : ZMod 3 → ℤ := fun y ↦ (projectedMultiplicity q m y : ℤ)
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
  let scalar : ℂ := (d : ℂ) - 1 - (η + η⁻¹)
  have hscalar0 : scalar ≠ 0 := complex_frequencyScalar_ne_zero hd hη
  obtain ⟨s, hs⟩ := Complex.isSquare scalar
  have hκ : scalar = s * s := by simpa [pow_two] using hs
  have hs0 : s ≠ 0 := by
    intro hs
    apply hscalar0
    rw [hκ, hs]
    simp
  obtain ⟨w, hw⟩ := graph_projected_anchor_fourier_eq_int_mul_of_sq
    (K := ℂ) G D u (by omega) hrOdd hdiv hbij huD hcommZ hsqZ
      hη.pow_eq_one (hη.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num))
      hs0 hκ
  have hpowerChar :
      (∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y) =
        ∑ y : ZMod 3,
          ((projectedMultiplicity q m y : ℕ) : ℂ) * η ^ y.val := by
    apply Finset.sum_congr rfl
    intro y _
    rw [primitiveRootCharacter_eq_pow_val]
    simp [c, q, m]
  have hH : (∑ y : ZMod 3,
      (c y : ℂ) * primitiveRootCharacter hη y) = (w : ℂ) * s := by
    rw [hpowerChar]
    exact hw
  have hsymm : ∀ y, c (-y) = c y := by
    intro y
    dsimp only [c]
    exact_mod_cast graph_projectedAnchorMultiplicity_neg_eq
      G hfree hd hdeven hmin hcard (by omega) hrOdd hdiv u hu huD y
  have hηsum : 1 + η + η ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using
      hη.geom_sum_eq_zero (by norm_num : 1 < 3)
  have hηtrace : η + η⁻¹ = -1 := by
    have hη0 : η ≠ 0 := hη.ne_zero (by norm_num)
    field_simp [hη0]
    linear_combination hηsum
  have hscalar : scalar = (d : ℂ) := by
    dsimp only [scalar]
    rw [hηtrace]
    ring
  have hFourierSq :
      (∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y) *
          (∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y) =
        ((w * w : ℤ) : ℂ) * (d : ℂ) := by
    rw [hH]
    rw [hscalar] at hκ
    push_cast
    rw [hκ]
    ring
  exact orderThree_fourier_eq_zero_of_square_identity
    hη c hsymm d hnonsquare w hFourierSq

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

/-- If the degree is nonsquare, simultaneous ninth- and third-root
vanishing upgrades the total anchor-mass divisibility from three to nine. -/
theorem nine_dvd_graph_totalAnchorMass_of_nine_dvd_cycleLength
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
    (hnonsquare : ¬ IsSquare d) :
    (9 : ℤ) ∣ ∑ t : ZMod r,
      (anchorMultiplicity
        (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c)) t : ℤ) := by
  let q9 := ZMod.castHom hdiv (ZMod 9)
  have hdiv3 : 3 ∣ r := dvd_trans (by norm_num : 3 ∣ 9) hdiv
  let q3 := ZMod.castHom hdiv3 (ZMod 3)
  let m : ZMod r → ℕ := anchorMultiplicity
    (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
  let c9 : ZMod 9 → ℤ := fun y ↦ (projectedMultiplicity q9 m y : ℤ)
  let c3 : ZMod 3 → ℤ := fun y ↦ (projectedMultiplicity q3 m y : ℤ)
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)
  let η : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hζ : IsPrimitiveRoot ζ 9 :=
    Complex.isPrimitiveRoot_exp 9 (by norm_num)
  have hη : IsPrimitiveRoot η 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have hzero9 : ∑ y : ZMod 9,
      (c9 y : ℂ) * primitiveRootCharacter hζ y = 0 := by
    exact graph_projectedAnchor_orderNine_fourier_eq_zero
      G hfree hd hdeven hmin hcard hr hrOdd hdiv u hu huRange huD hsep hζ
  have hzero3proj : ∑ y : ZMod 3,
      (c3 y : ℂ) * primitiveRootCharacter hη y = 0 := by
    exact graph_projectedAnchor_orderThree_fourier_eq_zero_of_degree_nonsquare
      G hfree hd hdeven hmin hcard hr hrOdd hdiv3 u hu huRange huD hsep
        hnonsquare hη
  have hη9 : η ^ 9 = 1 := by
    rw [show 9 = 3 * 3 by norm_num, pow_mul, hη.pow_eq_one, one_pow]
  have hzero3 : ∑ y : ZMod 9, (c9 y : ℂ) * η ^ y.val = 0 := by
    calc
      (∑ y : ZMod 9, (c9 y : ℂ) * η ^ y.val) =
          ∑ t : ZMod r, (m t : ℂ) * cyclePow η t := by
            simpa [c9, q9] using
              (projectedMultiplicity_fourier_eq_sum_cyclePow
                (K := ℂ) hdiv hη9 m)
      _ = ∑ y : ZMod 3, (c3 y : ℂ) * η ^ y.val := by
            symm
            simpa [c3, q3] using
              (projectedMultiplicity_fourier_eq_sum_cyclePow
                (K := ℂ) hdiv3 hη.pow_eq_one m)
      _ = ∑ y : ZMod 3,
          (c3 y : ℂ) * primitiveRootCharacter hη y := by
            apply Finset.sum_congr rfl
            intro y _
            rw [primitiveRootCharacter_eq_pow_val]
      _ = 0 := hzero3proj
  have hdvd := nine_dvd_sum_of_orderNine_and_orderThree_character_eq_zero
    hζ hη c9 hzero9 hzero3
  have hsumNat : (∑ y : ZMod 9, projectedMultiplicity q9 m y) =
      ∑ t : ZMod r, m t := sum_projectedMultiplicity_eq_sum q9 m
  have hsumInt : (∑ y : ZMod 9, c9 y) =
      ∑ t : ZMod r, (m t : ℤ) := by
    dsimp only [c9]
    exact_mod_cast hsumNat
  rw [hsumInt] at hdvd
  exact hdvd

/-- Once the total diagonal-anchor mass is identified with the degree, the
order-nine/order-three dichotomy contradicts boundary divisibility by nine. -/
theorem false_of_graph_frequencyPair_nine_of_totalAnchorMass_eq_degree
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
    (hmass : (∑ t : ZMod r,
      (anchorMultiplicity
        (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c)) t : ℤ)) = d)
    (hboundary : 9 ∣ d * (d - 1) + 3) : False := by
  have hnine : 9 ∣ d := by
    by_cases hsquare : IsSquare d
    · have hthreeInt :=
        three_dvd_graph_totalAnchorMass_of_nine_dvd_cycleLength
          G hfree hd hdeven hmin hcard hr hrOdd hdiv u hu huRange huD hsep
      have hthree : 3 ∣ d := by
        rw [hmass] at hthreeInt
        exact_mod_cast hthreeInt
      exact nine_dvd_of_three_dvd_of_isSquare hthree hsquare
    · have hnineInt :=
        nine_dvd_graph_totalAnchorMass_of_nine_dvd_cycleLength
          G hfree hd hdeven hmin hcard hr hrOdd hdiv u hu huRange huD hsep
            hsquare
      rw [hmass] at hnineInt
      exact_mod_cast hnineInt
  exact nine_not_dvd_boundary_of_nine_dvd_degree hnine hboundary

/-- Complete primitive order-nine contradiction in the nonsquare quotient
branch `¬ IsSquare (d-3)`. -/
theorem false_of_graph_frequencyPair_nine_of_quotient_nonsquare
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
    (hcomp : 1 < Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent)
    (hnonsquare : ¬ IsSquare (d - 3)) : False := by
  let D := secondOrderDefectGraph G
  let A : D.ConnectedComponent → Finset (ZMod r) :=
    fun c ↦ graphCycleBlockZeroSupport G (u c) (u c)
  have hsize : ∀ c : D.ConnectedComponent, c.supp.ncard = r := by
    intro c
    rw [← huRange c, Set.ncard_range_of_injective (hu c),
      Nat.card_eq_fintype_card, ZMod.card]
  have htrace : ∑ c : D.ConnectedComponent,
      componentQuotientMatrix G D c c = d :=
    secondOrder_equalComponents_quotient_trace_eq_degree_of_nonsquare
      G hfree hd hdeven hmin hcard hsize hcomp hnonsquare
  have hmassNat : (∑ t : ZMod r, anchorMultiplicity A t) = d := by
    calc
      (∑ t : ZMod r, anchorMultiplicity A t) =
          ∑ c : D.ConnectedComponent, (A c).card :=
            sum_anchorMultiplicity_eq_sum_card A
      _ = ∑ c : D.ConnectedComponent,
          componentQuotientMatrix G D c c := by
            apply Finset.sum_congr rfl
            intro c _
            exact card_graphCycleBlockZeroSupport_eq_componentQuotient
              G hfree hd hdeven hmin hcard c c (u c) (u c) (hu c)
                (huRange c) (huRange c)
      _ = d := htrace
  have hmass : (∑ t : ZMod r, (anchorMultiplicity A t : ℤ)) = d := by
    exact_mod_cast hmassNat
  obtain ⟨-, -, -, htile⟩ :=
    equalCycle_length_facts G hfree hd hdeven hmin hcard hsize
  have hboundary : 9 ∣ d * (d - 1) + 3 := by
    rw [← htile]
    exact dvd_mul_of_dvd_right hdiv _
  exact false_of_graph_frequencyPair_nine_of_totalAnchorMass_eq_degree
    G hfree hd hdeven hmin hcard hr hrOdd hdiv u hu huRange huD hsep
      (by simpa only [A] using hmass) hboundary

/-- **Uniform primitive order-nine terminal.**  Fourier vanishing forces
`c 0 = c 3`, while the projected graph parity pattern makes the former even
and the latter odd.  This removes every square/nonsquare quotient case at
once. -/
theorem false_of_graph_frequencyPair_nine
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 9 ≤ r) (hrOdd : Odd r) (hdiv : 9 ∣ r)
    (hoddQuotient : Odd (r / 9))
    (u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hsep : ∀ {c e : (secondOrderDefectGraph G).ConnectedComponent},
      c ≠ e → ∀ x y, u c x ≠ u e y)
    (hoddComponents : Odd (Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent))
    (b : ZMod r) (hb : b + b = 1) : False := by
  let q := ZMod.castHom hdiv (ZMod 9)
  let a : ZMod 9 := q b
  let m : ZMod r → ℕ := anchorMultiplicity
    (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
  let c : ZMod 9 → ℤ := fun y ↦ (projectedMultiplicity q m y : ℤ)
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)
  have hζ : IsPrimitiveRoot ζ 9 :=
    Complex.isPrimitiveRoot_exp 9 (by norm_num)
  have hzero : ∑ y : ZMod 9,
      (c y : ℂ) * primitiveRootCharacter hζ y = 0 := by
    exact graph_projectedAnchor_orderNine_fourier_eq_zero
      G hfree hd hdeven hmin hcard (by omega) hrOdd hdiv
        u hu huRange huD hsep hζ
  have hsymm : ∀ y, c (-y) = c y := by
    intro y
    dsimp only [c]
    exact_mod_cast graph_projectedAnchorMultiplicity_neg_eq
      G hfree hd hdeven hmin hcard (by omega) hrOdd hdiv u hu huD y
  have hc03 : c 0 = c 3 :=
    orderNine_zero_implies_coeff_zero_eq_coeff_three hζ c hsymm hzero
  have hbase : ∀ h, Odd (m h) ↔
      2 * h ∈ allowedCycleDifferences r := by
    intro h
    exact odd_graph_diagonalAnchorMultiplicity_iff
      G hfree hd hdeven hmin hcard (by omega) hrOdd u hu huRange huD
        hsep hoddComponents h
  have hparity : ∀ y, Odd (c y) ↔
      y ∉ ({0, a, -a} : Finset (ZMod 9)) := by
    intro y
    have hy := odd_projectedMultiplicity_zmod_castHom_iff
      hdiv (by norm_num : 4 ≤ 9) (by omega) hrOdd hoddQuotient
        b hb m hbase y
    dsimp only [c, a, q]
    exact_mod_cast hy
  have haDouble : a + a = 1 := by
    dsimp only [a, q]
    rw [← map_add, hb, map_one]
  have h3not : (3 : ZMod 9) ∉ ({0, a, -a} : Finset (ZMod 9)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    · exact (by decide : (3 : ZMod 9) ≠ 0) h
    · rw [← h] at haDouble
      exact (by decide : (6 : ZMod 9) ≠ 1) haDouble
    · have ha : a = -(3 : ZMod 9) := by
        simpa only [neg_neg] using (congrArg Neg.neg h).symm
      rw [ha] at haDouble
      exact (by decide : (-(6 : ZMod 9)) ≠ 1) haDouble
  have hzeroEven : ¬ Odd (c 0) := by
    rw [hparity]
    simp
  have hthreeOdd : Odd (c 3) := by
    rw [hparity]
    exact h3not
  exact hzeroEven (hc03 ▸ hthreeOdd)

/-- Under the common component-length hypothesis, divisibility by nine is
impossible.  The cyclic labeling and the two parity inputs are extracted
internally. -/
theorem false_of_equalCycle_nine_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ}
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hlen : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r) (hdiv : 9 ∣ r) : False := by
  classical
  obtain ⟨hr3, hrOdd, hoddC, -⟩ :=
    equalCycle_length_facts G hfree hd hdeven hmin hcard hlen
  haveI : NeZero r := ⟨by omega⟩
  obtain ⟨u, hu, huRange, huD, hsep⟩ :=
    exists_equalCycle_labeling G hfree hd hdeven hmin hcard hlen
  obtain ⟨b, hb⟩ := exists_add_self_eq_one_of_odd hrOdd
  have hoddQuotient : Odd (r / 9) := by
    have hmul : r / 9 * 9 = r := Nat.div_mul_cancel hdiv
    have hodd' : Odd (r / 9 * 9) := by simpa [hmul] using hrOdd
    exact (odd_and_odd_of_odd_mul hodd').1
  exact false_of_graph_frequencyPair_nine G hfree hd hdeven hmin hcard
    (Nat.le_of_dvd (by omega) hdiv) hrOdd hdiv hoddQuotient
      u hu huRange huD (fun hce x y ↦ hsep hce x y) hoddC b hb

end

end Erdos85
