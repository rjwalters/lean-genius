import Proofs.Erdos85OrientedSquareBranch
import Proofs.Erdos85OrderFiveNormBridge
import Proofs.Erdos85MixedParityAssembly
import Proofs.Erdos85ForwardSupportClassification
import Proofs.Erdos85FrequencyScalar

/-!
# The mixed oriented order-five mass constraint

The equal-cycle order-five terminal used inverse symmetry of the ordinary
projected anchor.  The canonical orientation marking supplies the same
symmetry on the forward sector even when selected component lengths are
mixed and may be even.  At a primitive fifth root the square-trace identity
and the real quadratic norm force the oriented Fourier coefficient to
vanish.  Hence the total forward-oriented anchor mass is divisible by five.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V C : Type*} [Fintype V] [DecidableEq V]
  [Fintype C] [DecidableEq C]
variable {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)] {p : ℕ} [NeZero p]

/-- Forward-oriented projected anchors are invariant under negation.  This
uses only symmetry of each circulant diagonal support, with no parity
assumption on the component lengths. -/
theorem orientedProjectedAnchor_neg_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (o : C → Prop) [DecidablePred o]
    (hfwd : ∀ c, p ∣ ℓ c → o c → ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y + 1)) ↔ G.Adj (u c x) (u c y))
    (s : ZMod p) :
    orientedProjectedAnchor G u o p (-s) =
      orientedProjectedAnchor G u o p s := by
  classical
  unfold orientedProjectedAnchor
  apply Finset.sum_congr rfl
  intro c hc
  have hpc : p ∣ ℓ c := (Finset.mem_filter.mp hc).2.1
  have hoc : o c := (Finset.mem_filter.mp hc).2.2
  let q : ZMod (ℓ c) →+* ZMod p := ZMod.castHom hpc (ZMod p)
  let S := graphCycleBlockZeroSupport G (u c) (u c)
  have hneg : ∀ {t : ZMod (ℓ c)}, t ∈ S → -t ∈ S := by
    intro t ht
    exact neg_mem_graphCycleBlockZeroSupport_of_forward
      G (u c) (hfwd c hpc hoc) ht
  apply Finset.card_bij (fun t _ ↦ -t)
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨hneg ht.1, ?_⟩
    rw [← zmod_castHom_eq_val_cast hpc,
      map_neg, zmod_castHom_eq_val_cast hpc, ht.2]
    simp
  · intro t₁ ht₁ t₂ ht₂ h
    exact neg_injective h
  · intro w hw
    refine ⟨-w, ?_, by simp⟩
    rw [Finset.mem_filter] at hw ⊢
    refine ⟨hneg hw.1, ?_⟩
    rw [← zmod_castHom_eq_val_cast hpc,
      map_neg, zmod_castHom_eq_val_cast hpc, hw.2]

variable {K : Type*} [Field K] [CharZero K]

/-- Square-branch trace integrality in the orientation-marked mixed system:
the oriented anchor Fourier coefficient is an integral multiple of the
chosen square root of the frequency scalar. -/
theorem graph_oriented_anchor_fourier_eq_int_mul_of_square
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V)
    (o : C → Prop) [DecidablePred o]
    (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hfwdG : ∀ c : C, p ∣ ℓ c → o c → ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y + 1)) ↔ G.Adj (u c x) (u c y))
    (hrevG : ∀ c : C, p ∣ ℓ c → ¬ o c → ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y - 1)) ↔ G.Adj (u c x) (u c y))
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {s : K} (hs : s ≠ 0)
    (hscalar : (d : K) - 1 - (ζ + ζ⁻¹) = s * s) :
    ∃ w : ℤ,
      (∑ y : ZMod p,
        ((orientedProjectedAnchor G u o p y : ℕ) : K) * ζ ^ y.val) =
          (w : K) * s := by
  have hcomm := mixedLabeledAdjMatrix_comm_mixedDefectMatrix (K := K)
    G D u hℓ3 hbij huD hcommZ
  let T := defectEigenspaceRestrict (mixedLabeledAdjMatrix K G u) hcomm
    (ζ + ζ⁻¹)
  have hTsq := graph_mixed_defectEigenspaceRestrict_sq G D u hℓ3 hbij
    huD hsqZ hcomm hζ.pow_eq_one (by omega)
      (fun h ↦ hζ.pow_ne_one_of_pos_of_lt (by norm_num) hp2 (by rw [h, one_pow]))
  rw [hscalar] at hTsq
  have heven : Even (Module.finrank K
      (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹))) :=
    even_finrank_defectEigenspace_mixed hp hp2 hζ
  obtain ⟨w, hw⟩ := LinearMap.exists_int_trace_eq_two_mul_of_sq_eq_sq
    T s hs hTsq heven
  have htrace := graph_mixed_trace_eq_two_mul_oriented_anchor_fourier
    G u o hfwdG hrevG hcomm hp hp2 hζ
  refine ⟨w, ?_⟩
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  apply mul_left_cancel₀ h2
  rw [← htrace, hw]
  ring

/-- **Mixed order-five mass theorem.**  At the exact even boundary, five
divides the total diagonal-anchor mass of the canonically forward-oriented
components whose orders are divisible by five.  Component lengths may be
unequal or even. -/
theorem five_dvd_orientedAnchorMass_forwardOriented
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
      {u c (x - 1), u c (x + 1)}) :
    5 ∣ orientedAnchorMass G u (forwardOriented G u) 5 := by
  letI : NeZero 5 := ⟨by norm_num⟩
  let D := secondOrderDefectGraph G
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)
  have hζ : IsPrimitiveRoot ζ 5 :=
    Complex.isPrimitiveRoot_exp 5 (by norm_num)
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  let scalar : ℂ := (d : ℂ) - 1 - (ζ + ζ⁻¹)
  have hscalar0 : scalar ≠ 0 := complex_frequencyScalar_ne_zero hd hζ
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
      Nat.prime_five (by norm_num) hζ hs0 hscalar
  let c : ZMod 5 → ℤ := fun y ↦
    (orientedProjectedAnchor G u (forwardOriented G u) 5 y : ℤ)
  have hsymm : ∀ y, c (-y) = c y := by
    intro y
    simpa only [c] using congrArg (fun n : ℕ ↦ (n : ℤ))
      (orientedProjectedAnchor_neg_eq G u
        (forwardOriented G u) (forwardOriented_fwd G u) y)
  have hH : (∑ y : ZMod 5,
      (c y : ℂ) * primitiveRootCharacter hζ y) = (w : ℂ) * s := by
    rw [← hw]
    apply Finset.sum_congr rfl
    intro y _
    rw [primitiveRootCharacter_eq_pow_val]
    simp [c]
  have hFourierSq :
      (∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y) *
          (∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y) =
        ((w * w : ℤ) : ℂ) * (((d - 1 : ℕ) : ℂ) - ζ - ζ⁻¹) := by
    rw [hH]
    have hd1 : ((d - 1 : ℕ) : ℂ) = (d : ℂ) - 1 := by
      simpa using (Nat.cast_sub (R := ℂ) (by omega : 1 ≤ d))
    rw [hd1]
    dsimp only [scalar] at hscalar
    have hscalar' : (d : ℂ) - 1 - ζ - ζ⁻¹ = s * s := by
      linear_combination hscalar
    rw [hscalar']
    push_cast
    ring
  have hzero : ∑ y : ZMod 5,
      (c y : ℂ) * primitiveRootCharacter hζ y = 0 :=
    orderFive_fourier_eq_zero_of_square_identity hζ c hsymm
      (d - 1) (by omega) w hFourierSq
  let cFin : Fin 5 → ℤ := fun i ↦ c (ZMod.finEquiv 5 i)
  have hzeroFin : ∑ i : Fin 5, (cFin i : ℂ) * ζ ^ i.val = 0 := by
    calc
      (∑ i : Fin 5, (cFin i : ℂ) * ζ ^ i.val) =
          ∑ y : ZMod 5, (c y : ℂ) * primitiveRootCharacter hζ y := by
        refine Fintype.sum_equiv (ZMod.finEquiv 5) _ _ ?_
        intro i
        simp [cFin]
      _ = 0 := hzero
  have hall := all_eq_of_prime_fourier_eq_zero
    Nat.prime_five hζ cFin hzeroFin
  have hmass := sum_orientedProjectedAnchor_eq_mass
    (p := 5) G u (forwardOriented G u)
  set a0 := orientedProjectedAnchor G u (forwardOriented G u) 5 0
  have hconst : ∀ y : ZMod 5,
      orientedProjectedAnchor G u (forwardOriented G u) 5 y = a0 := by
    intro y
    have h := hall ((ZMod.finEquiv 5).symm y) ((ZMod.finEquiv 5).symm 0)
    dsimp only [cFin, c] at h
    rw [(ZMod.finEquiv 5).apply_symm_apply,
      (ZMod.finEquiv 5).apply_symm_apply] at h
    exact_mod_cast h
  rw [← hmass, Finset.sum_congr rfl fun y _ ↦ hconst y,
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  exact dvd_mul_right 5 a0

end

end Erdos85
