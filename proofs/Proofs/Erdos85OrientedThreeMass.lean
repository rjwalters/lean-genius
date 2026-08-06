import Proofs.Erdos85OrientedFiveMass
import Proofs.Erdos85OrderThreeNormBridge

/-!
# The mixed oriented order-three mass constraint

For a primitive third root the frequency scalar is exactly `d`.  When the
degree is not a natural square, the square-trace identity and the quadratic
order-three norm force the orientation-marked Fourier coefficient to vanish.
Thus three divides the total forward-oriented anchor mass, without any
common-length or component-parity assumption.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Mixed order-three mass theorem.**  At the exact even boundary, if the
degree is nonsquare, three divides the total diagonal-anchor mass of the
canonically forward-oriented components whose orders are divisible by
three. -/
theorem three_dvd_orientedAnchorMass_forwardOriented_of_degree_nonsquare
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hℓ3 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      3 ≤ c.supp.ncard)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
      {u c (x - 1), u c (x + 1)})
    (hnonsquare : ¬ IsSquare d) :
    3 ∣ orientedAnchorMass G u (forwardOriented G u) 3 := by
  letI : NeZero 3 := ⟨by norm_num⟩
  let D := secondOrderDefectGraph G
  let η : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)
  have hη : IsPrimitiveRoot η 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  let scalar : ℂ := (d : ℂ) - 1 - (η + η⁻¹)
  have hscalar0 : scalar ≠ 0 := complex_frequencyScalar_ne_zero hd hη
  obtain ⟨s, hs⟩ := Complex.isSquare scalar
  have hscalar : scalar = s * s := by simpa [pow_two] using hs
  have hs0 : s ≠ 0 := by
    intro hs0
    apply hscalar0
    rw [hscalar, hs0]
    simp
  obtain ⟨w, hw⟩ := graph_oriented_anchor_fourier_eq_int_mul_of_square
    (K := ℂ) G D u (forwardOriented G u) hℓ3 hbij huD hcommZ hsqZ
      (forwardOriented_fwd G u)
      (forwardOriented_rev G D hfree u hℓ3 hbij huD hcommZ)
      Nat.prime_three (by norm_num) hη hs0 hscalar
  let c : ZMod 3 → ℤ := fun y ↦
    (orientedProjectedAnchor G u (forwardOriented G u) 3 y : ℤ)
  have hsymm : ∀ y, c (-y) = c y := by
    intro y
    simpa only [c] using congrArg (fun n : ℕ ↦ (n : ℤ))
      (orientedProjectedAnchor_neg_eq G u
        (forwardOriented G u) (forwardOriented_fwd G u) y)
  have hH : (∑ y : ZMod 3,
      (c y : ℂ) * primitiveRootCharacter hη y) = (w : ℂ) * s := by
    rw [← hw]
    apply Finset.sum_congr rfl
    intro y _
    rw [primitiveRootCharacter_eq_pow_val]
    simp [c]
  have hηsum : 1 + η + η ^ 2 = 0 := by
    simpa [Finset.sum_range_succ] using
      hη.geom_sum_eq_zero (by norm_num : 1 < 3)
  have hηtrace : η + η⁻¹ = -1 := by
    have hη0 : η ≠ 0 := hη.ne_zero (by norm_num)
    field_simp [hη0]
    linear_combination hηsum
  have hscalarD : scalar = (d : ℂ) := by
    dsimp only [scalar]
    rw [hηtrace]
    ring
  have hFourierSq :
      (∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y) *
          (∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y) =
        ((w * w : ℤ) : ℂ) * (d : ℂ) := by
    rw [hH]
    rw [hscalarD] at hscalar
    push_cast
    rw [hscalar]
    ring
  have hzero : ∑ y : ZMod 3,
      (c y : ℂ) * primitiveRootCharacter hη y = 0 :=
    orderThree_fourier_eq_zero_of_square_identity
      hη c hsymm d hnonsquare w hFourierSq
  let cFin : Fin 3 → ℤ := fun i ↦ c (ZMod.finEquiv 3 i)
  have hzeroFin : ∑ i : Fin 3, (cFin i : ℂ) * η ^ i.val = 0 := by
    calc
      (∑ i : Fin 3, (cFin i : ℂ) * η ^ i.val) =
          ∑ y : ZMod 3, (c y : ℂ) * primitiveRootCharacter hη y := by
        refine Fintype.sum_equiv (ZMod.finEquiv 3) _ _ ?_
        intro i
        simp [cFin]
      _ = 0 := hzero
  have hall := all_eq_of_prime_fourier_eq_zero
    Nat.prime_three hη cFin hzeroFin
  have hmass := sum_orientedProjectedAnchor_eq_mass
    (p := 3) G u (forwardOriented G u)
  set a0 := orientedProjectedAnchor G u (forwardOriented G u) 3 0
  have hconst : ∀ y : ZMod 3,
      orientedProjectedAnchor G u (forwardOriented G u) 3 y = a0 := by
    intro y
    have h := hall ((ZMod.finEquiv 3).symm y) ((ZMod.finEquiv 3).symm 0)
    dsimp only [cFin, c] at h
    rw [(ZMod.finEquiv 3).apply_symm_apply,
      (ZMod.finEquiv 3).apply_symm_apply] at h
    exact_mod_cast h
  rw [← hmass, Finset.sum_congr rfl fun y _ ↦ hconst y,
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  exact dvd_mul_right 3 a0

end

end Erdos85
