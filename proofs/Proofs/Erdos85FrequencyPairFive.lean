import Proofs.Erdos85OrderFiveNormBridge
import Proofs.Erdos85FrequencyPairTransport
import Proofs.Erdos85GraphAnchorSymmetry
import Proofs.Erdos85GraphPrimeFourierNonsquare
import Proofs.Erdos85FrequencyScalar
import Proofs.Erdos85EqualCycleLabeling

/-!
# The order-five frequency-pair terminal

At a primitive fifth root, negation symmetry places the projected anchor
Fourier coefficient in the real quadratic subfield.  The quadratic norm
bridge then shows that the square-operator identity already forces this
coefficient to vanish.  Prime Fourier rigidity contradicts the graph parity
pattern.  This closes the `5 ∣ r` residual branch without enumerating cycle
lengths.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The graph-facing order-five contradiction for an equal-cycle labeling. -/
theorem false_of_graph_frequencyPair_five
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 4 ≤ r) (hrOdd : Odd r) (hdiv : 5 ∣ r)
    (hoddQuotient : Odd (r / 5))
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
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 5) : False := by
  let D := secondOrderDefectGraph G
  let q := ZMod.castHom hdiv (ZMod 5)
  let m : ZMod r → ℕ := anchorMultiplicity
    (fun c ↦ graphCycleBlockZeroSupport G (u c) (u c))
  let c : ZMod 5 → ℤ := fun y ↦ (projectedMultiplicity q m y : ℤ)
  let a : ZMod 5 := q b
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
      (∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y) =
        ∑ y : ZMod 5,
          ((projectedMultiplicity q m y : ℕ) : ℂ) * ζ ^ y.val := by
    apply Finset.sum_congr rfl
    intro y _
    rw [primitiveRootCharacter_eq_pow_val]
    simp [c, q, m]
  have hH : (∑ y : ZMod 5,
      (c y : ℂ) * primitiveRootCharacter hζ y) = (w : ℂ) * s := by
    rw [hpowerChar]
    exact hw
  have hsymm : ∀ y, c (-y) = c y := by
    intro y
    dsimp only [c]
    exact_mod_cast graph_projectedAnchorMultiplicity_neg_eq
      G hfree hd hdeven hmin hcard (by omega) hrOdd hdiv u hu huD y
  have hFourierSq :
      (∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y) *
          (∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y) =
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
  have hzero : ∑ y : ZMod 5,
      (c y : ℂ) * primitiveRootCharacter hζ y = 0 :=
    orderFive_fourier_eq_zero_of_square_identity hζ c hsymm
      (d - 1) (by omega) w hFourierSq
  have hbase : ∀ h, Odd (m h) ↔
      2 * h ∈ allowedCycleDifferences r := by
    intro h
    exact odd_graph_diagonalAnchorMultiplicity_iff
      G hfree hd hdeven hmin hcard (by omega) hrOdd u hu huRange huD
        hsep hoddComponents h
  have hparity : ∀ y, Odd (c y) ↔
      y ∉ ({0, a, -a} : Finset (ZMod 5)) := by
    intro y
    have hy := odd_projectedMultiplicity_zmod_castHom_iff
      hdiv (by norm_num : 4 ≤ 5) hr hrOdd hoddQuotient b hb m hbase y
    dsimp only [c, a, q]
    exact_mod_cast hy
  exact false_of_prime_fourier_zero_and_threePoint_parity
    Nat.prime_five (by norm_num) hζ c a hzero hparity

/-- Under the common component-length hypothesis, divisibility by five is
already impossible.  All cyclic labeling and parity data are extracted
internally. -/
theorem false_of_equalCycle_five_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ}
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hlen : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r) (hdiv : 5 ∣ r) : False := by
  classical
  obtain ⟨hr3, hrOdd, hoddC, -⟩ :=
    equalCycle_length_facts G hfree hd hdeven hmin hcard hlen
  haveI : NeZero r := ⟨by omega⟩
  obtain ⟨u, hu, huRange, huD, hsep⟩ :=
    exists_equalCycle_labeling G hfree hd hdeven hmin hcard hlen
  obtain ⟨b, hb⟩ := exists_add_self_eq_one_of_odd hrOdd
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
  have hζ : IsPrimitiveRoot ζ 5 :=
    Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have hoddQuotient : Odd (r / 5) := by
    have hmul : r / 5 * 5 = r := Nat.div_mul_cancel hdiv
    have hodd' : Odd (r / 5 * 5) := by simpa [hmul] using hrOdd
    exact (odd_and_odd_of_odd_mul hodd').1
  exact false_of_graph_frequencyPair_five G hfree hd hdeven hmin hcard
    (by omega) hrOdd hdiv hoddQuotient u hu huRange huD
      (fun hce x y ↦ hsep hce x y) hoddC b hb hζ

end

end Erdos85
