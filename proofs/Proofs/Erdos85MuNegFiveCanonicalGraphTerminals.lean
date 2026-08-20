import Proofs.Erdos85MuNegFiveZeroThreeGraphRealization
import Proofs.Erdos85MuNegFiveCanonicalOwnerRelationsTerminal
import Proofs.Erdos85MuNegFiveCanonicalCrossProfiles

/-!
# Graph-facing fields for the remaining canonical `mu = -5` endpoints

The h504 and h512 owner CNFs share the h503 cross-variable table.  This file
first transports their exact row/column exterior profiles to the Boolean
fiber encoding.  Their owner-service geometry is kept separate: unlike h503,
it is not a formal consequence of antipode-only same-shore exterior support.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem muNegFiveZeroFourFiberBitsAllowed_of_zmodProfile
    (sigma left : Bool) (z : Fin 8)
    (bits : Fin 8 → Bool) (p : ZMod 8 → Bool)
    (hbits : ∀ w, bits w = true ↔ p (w.val : ZMod 8) = true)
    (htotal : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      p j = true).card = 4)
    (hsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      muNegFiveZeroThreeSameSign sigma
        (if left then z.val else j.val)
        (if left then j.val else z.val) = true ∧ p j = true).card = 3) :
    muNegFiveCanonicalFiberBitsAllowed 4 3 sigma left z bits = true := by
  revert sigma left z bits p
  native_decide

theorem muNegFiveOneTwoFiberBitsAllowed_of_zmodProfile
    (sigma left : Bool) (z : Fin 8)
    (bits : Fin 8 → Bool) (p : ZMod 8 → Bool)
    (hbits : ∀ w, bits w = true ↔ p (w.val : ZMod 8) = true)
    (htotal : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      p j = true).card = 6)
    (hsame : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
      muNegFiveZeroThreeSameSign sigma
        (if left then z.val else j.val)
        (if left then j.val else z.val) = true ∧ p j = true).card = 4) :
    muNegFiveCanonicalFiberBitsAllowed 6 4 sigma left z bits = true := by
  revert sigma left z bits p
  native_decide

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]
  (a b : (G.induce c.supp).ConnectedComponent)
  (u v : ZMod 8 → c.supp)

/-- A graph cross valuation inherits any exact row/column profile of the
actual exterior cross matrix. -/
theorem muNegFiveCanonicalGraphFiberBitsAllowed
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (s : V → ℤ) (sigma : Bool) (total same : Nat)
    (hphase : ∀ x y : Nat, x < 8 → y < 8 →
      (muNegFiveZeroThreeSameSign sigma x y = true ↔
        s (v (y : ZMod 8)).1 = s (u (x : ZMod 8)).1))
    (P : MuNegFiveCrossExteriorProfile
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (u i) (v j))
      (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) total same) :
    (∀ (sigma left : Bool) (z : Fin 8) (bits : Fin 8 → Bool)
        (p : ZMod 8 → Bool),
      (∀ w, bits w = true ↔ p (w.val : ZMod 8) = true) →
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦ p j = true).card = total →
      ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        muNegFiveZeroThreeSameSign sigma
          (if left then z.val else j.val)
          (if left then j.val else z.val) = true ∧ p j = true).card = same →
      muNegFiveCanonicalFiberBitsAllowed total same sigma left z bits = true) →
    ∀ left z, z < 8 →
      muNegFiveCanonicalFiberBitsAllowed total same sigma left z
        (muNegFiveZeroThreeFiberBit
          (muNegFiveZeroThreeOwnerValOfRelations
            (muNegFiveZeroThreeGraphActive G c u v)
            (muNegFiveZeroThreeGraphHit G c u v)) left z) = true := by
  intro hkernel left z hz
  let bits := muNegFiveZeroThreeFiberBit
    (muNegFiveZeroThreeOwnerValOfRelations
      (muNegFiveZeroThreeGraphActive G c u v)
      (muNegFiveZeroThreeGraphHit G c u v)) left z
  cases left
  · let p : ZMod 8 → Bool := fun i ↦ decide
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
          (u i) (v (z : ZMod 8)) ≠ 1)
    apply hkernel sigma false ⟨z, hz⟩ bits p
    · intro w
      obtain ⟨id, hidx, _⟩ :=
        muNegFiveZeroThreeCrossFiber_zipIdx false ⟨z, hz⟩ w
      have hidx' : muNegFiveZeroThreeCrossIndex? w.val z = some id := by
        simpa using hidx
      simp only [bits, muNegFiveZeroThreeFiberBit]
      simp only [Bool.false_eq_true, if_false]
      rw [hidx']
      simpa [p] using muNegFiveZeroThreeOwnerVal_cross_true_iff G c a b u v
        hfree hab huinj hvinj hurange hvrange w.2 hz hidx
    · simpa [p] using P.col_total (z : ZMod 8)
    · dsimp only [p]
      simp only [decide_eq_true_eq]
      have hphase' : ∀ i : ZMod 8,
          muNegFiveZeroThreeSameSign sigma i.val z = true ↔
            s (u i).1 = s (v (z : ZMod 8)).1 := by
        intro i
        have hp := hphase i.val z i.val_lt hz
        have hi : (i.val : ZMod 8) = i := ZMod.natCast_zmod_val i
        constructor
        · intro h; simpa only [hi] using (hp.mp h).symm
        · intro h; apply hp.mpr; simpa only [hi] using h.symm
      change ((Finset.univ : Finset (ZMod 8)).filter fun i ↦
        muNegFiveZeroThreeSameSign sigma i.val z = true ∧
          ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
            (u i) (v (z : ZMod 8)) ≠ 1).card = same
      simpa only [hphase'] using P.col_same (z : ZMod 8)
  · let p : ZMod 8 → Bool := fun j ↦ decide
        (((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
          (u (z : ZMod 8)) (v j) ≠ 1)
    apply hkernel sigma true ⟨z, hz⟩ bits p
    · intro w
      obtain ⟨id, hidx, _⟩ :=
        muNegFiveZeroThreeCrossFiber_zipIdx true ⟨z, hz⟩ w
      have hidx' : muNegFiveZeroThreeCrossIndex? z w.val = some id := by
        simpa using hidx
      simp only [bits, muNegFiveZeroThreeFiberBit]
      simp only [if_true]
      rw [hidx']
      simpa [p] using muNegFiveZeroThreeOwnerVal_cross_true_iff G c a b u v
        hfree hab huinj hvinj hurange hvrange hz w.2 hidx
    · simpa [p] using P.row_total (z : ZMod 8)
    · dsimp only [p]
      simp only [decide_eq_true_eq]
      have hphase' : ∀ j : ZMod 8,
          muNegFiveZeroThreeSameSign sigma z j.val = true ↔
            s (v j).1 = s (u (z : ZMod 8)).1 := by
        intro j
        simpa using hphase z j.val hz j.val_lt
      change ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
        muNegFiveZeroThreeSameSign sigma z j.val = true ∧
          ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
            (u (z : ZMod 8)) (v j) ≠ 1).card = same
      simpa only [hphase'] using P.row_same (z : ZMod 8)

theorem muNegFiveZeroFourGraphFiberBitsAllowed
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (s : V → ℤ) (sigma : Bool)
    (hphase : ∀ x y : Nat, x < 8 → y < 8 →
      (muNegFiveZeroThreeSameSign sigma x y = true ↔
        s (v (y : ZMod 8)).1 = s (u (x : ZMod 8)).1))
    (P : MuNegFiveCrossExteriorProfile
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (u i) (v j))
      (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) 4 3) :
    ∀ left z, z < 8 →
      muNegFiveCanonicalFiberBitsAllowed 4 3 sigma left z
        (muNegFiveZeroThreeFiberBit
          (muNegFiveZeroThreeOwnerValOfRelations
            (muNegFiveZeroThreeGraphActive G c u v)
            (muNegFiveZeroThreeGraphHit G c u v)) left z) = true := by
  apply muNegFiveCanonicalGraphFiberBitsAllowed G c a b u v hfree hab
    huinj hvinj hurange hvrange s sigma 4 3 hphase P
  exact muNegFiveZeroFourFiberBitsAllowed_of_zmodProfile

theorem muNegFiveOneTwoGraphFiberBitsAllowed
    (hfree : ¬ containsC4 V G)
    (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (s : V → ℤ) (sigma : Bool)
    (hphase : ∀ x y : Nat, x < 8 → y < 8 →
      (muNegFiveZeroThreeSameSign sigma x y = true ↔
        s (v (y : ZMod 8)).1 = s (u (x : ZMod 8)).1))
    (P : MuNegFiveCrossExteriorProfile
      (fun i j ↦ ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ
        (u i) (v j))
      (fun i ↦ s (u i).1) (fun j ↦ s (v j).1) 6 4) :
    ∀ left z, z < 8 →
      muNegFiveCanonicalFiberBitsAllowed 6 4 sigma left z
        (muNegFiveZeroThreeFiberBit
          (muNegFiveZeroThreeOwnerValOfRelations
            (muNegFiveZeroThreeGraphActive G c u v)
            (muNegFiveZeroThreeGraphHit G c u v)) left z) = true := by
  apply muNegFiveCanonicalGraphFiberBitsAllowed G c a b u v hfree hab
    huinj hvinj hurange hvrange s sigma 6 4 hphase P
  exact muNegFiveOneTwoFiberBitsAllowed_of_zmodProfile

end

end Erdos85

#print axioms Erdos85.muNegFiveCanonicalGraphFiberBitsAllowed
#print axioms Erdos85.muNegFiveZeroFourGraphFiberBitsAllowed
#print axioms Erdos85.muNegFiveOneTwoGraphFiberBitsAllowed
