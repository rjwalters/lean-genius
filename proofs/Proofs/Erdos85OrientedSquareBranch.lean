import Proofs.Erdos85OrientationMarking
import Proofs.Erdos85PrimeFourierSquare

/-!
# The mixed oriented square branch

Reverse-oriented even components are invisible not only in the nonsquare
trace argument but also in the square branch.  The mixed frequency-pair
space always has even dimension, so a square frequency scalar forces cyclic
convolution constancy for the forward-oriented projected anchor counts,
without any common-length or component-parity hypothesis.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {K : Type*} [Field K] [CharZero K]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)] {p : ℕ} [NeZero p]

/-- The square frequency branch gives convolution constancy for the anchor
counts of precisely the forward-oriented selected components. -/
theorem graph_orientedProjectedAnchor_convolution_constant_of_square
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
    (hscalar : (d : K) - 1 - (ζ + ζ⁻¹) = s * s)
    (a : ZMod p) (ha : a ∉ ({0, 1, -1} : Finset (ZMod p))) :
    ∀ g, g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) →
      cyclicConvolution
          (fun y ↦ (orientedProjectedAnchor G u o p y : ℤ))
          (fun y ↦ (orientedProjectedAnchor G u o p y : ℤ)) a =
        cyclicConvolution
          (fun y ↦ (orientedProjectedAnchor G u o p y : ℤ))
          (fun y ↦ (orientedProjectedAnchor G u o p y : ℤ)) g := by
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζsq : ζ ^ 2 ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by norm_num) hp2
  have hζ1 : ζ ≠ 1 := fun h ↦ hζsq (by rw [h, one_pow])
  have hcomm := mixedLabeledAdjMatrix_comm_mixedDefectMatrix (K := K)
    G D u hℓ3 hbij huD hcommZ
  let T := defectEigenspaceRestrict (mixedLabeledAdjMatrix K G u) hcomm
    (ζ + ζ⁻¹)
  have hTsq := graph_mixed_defectEigenspaceRestrict_sq G D u hℓ3 hbij
    huD hsqZ hcomm hζp (by omega) hζ1
  rw [hscalar] at hTsq
  have heven : Even (Module.finrank K
      (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹))) :=
    even_finrank_defectEigenspace_mixed hp hp2 hζ
  have htr := graph_mixed_trace_eq_two_mul_oriented_anchor_fourier
    G u o hfwdG hrevG hcomm hp hp2 hζ
  have htrace : LinearMap.trace K
      (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹)) T =
      2 * ∑ x : ZMod p,
        (((orientedProjectedAnchor G u o p x : ℤ) : K) *
          primitiveRootCharacter hζ x) := by
    rw [htr]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [primitiveRootCharacter_eq_pow_val hζ]
    push_cast
    ring
  exact cyclicConvolution_anchor_constant_of_frequencyPair_trace hp hζ T s
    (fun y ↦ (orientedProjectedAnchor G u o p y : ℤ))
    ((d : ℤ) - 1) a hs hTsq heven htrace
    (by push_cast; linear_combination -hscalar) ha

/-- Canonical graph-facing square branch: C4-freeness and commutation choose
the forward/reverse marking automatically. -/
theorem graph_forwardOriented_convolution_constant_of_square
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ∀ c : C, ZMod (ℓ c) → V)
    (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {s : K} (hs : s ≠ 0)
    (hscalar : (d : K) - 1 - (ζ + ζ⁻¹) = s * s)
    (a : ZMod p) (ha : a ∉ ({0, 1, -1} : Finset (ZMod p))) :
    ∀ g, g ∉ ({0, a, -a, 1, -1} : Finset (ZMod p)) →
      cyclicConvolution
          (fun y ↦ (orientedProjectedAnchor G u
            (forwardOriented G u) p y : ℤ))
          (fun y ↦ (orientedProjectedAnchor G u
            (forwardOriented G u) p y : ℤ)) a =
        cyclicConvolution
          (fun y ↦ (orientedProjectedAnchor G u
            (forwardOriented G u) p y : ℤ))
          (fun y ↦ (orientedProjectedAnchor G u
            (forwardOriented G u) p y : ℤ)) g :=
  graph_orientedProjectedAnchor_convolution_constant_of_square G D u
    (forwardOriented G u) hℓ3 hbij huD hcommZ hsqZ
    (forwardOriented_fwd G u)
    (forwardOriented_rev G D hfree u hℓ3 hbij huD hcommZ)
    hp hp2 hζ hs hscalar a ha

end

end Erdos85
