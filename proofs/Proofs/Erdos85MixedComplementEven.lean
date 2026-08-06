import Proofs.Erdos85UnequalBlockFiberParity
import Proofs.Erdos85EqualBlockFiberParity

/-!
# Global parity of mixed complement fibers
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- An ordered off-diagonal sum is even whenever each unordered pair has
even combined weight. -/
theorem even_sum_erase_of_pair_even
    {C : Type*} [DecidableEq C] (S : Finset C) (F : C → C → ℕ)
    (hpair : ∀ c ∈ S, ∀ e ∈ S, c ≠ e → Even (F c e + F e c)) :
    Even (∑ c ∈ S, ∑ e ∈ S.erase c, F c e) := by
  let Q : C → C → ℕ := fun c e ↦ if c = e then 0 else F c e
  have hprincipal : Even (∑ c ∈ S, ∑ e ∈ S, Q c e) := by
    apply even_principal_sum_of_pair_even S Q
    · intro c hc
      simp [Q]
    · intro c hc e he hce
      simpa [Q, hce, hce.symm] using hpair c hc e he hce
  have heq : (∑ c ∈ S, ∑ e ∈ S, Q c e) =
      ∑ c ∈ S, ∑ e ∈ S.erase c, F c e := by
    apply Finset.sum_congr rfl
    intro c hc
    calc
      ∑ e ∈ S, Q c e = (∑ e ∈ S.erase c, Q c e) + Q c c :=
        (Finset.sum_erase_add _ _ hc).symm
      _ = ∑ e ∈ S.erase c, F c e := by
        simp only [Q, if_pos, add_zero]
        apply Finset.sum_congr rfl
        intro e he
        simp [(Finset.mem_erase.mp he).1.symm]
  rw [heq] at hprincipal
  exact hprincipal

/-- Two equal-length off-diagonal blocks contribute an even total in every
projection fiber. -/
theorem even_equalBlock_pair_fullMass_fibers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d n p : ℕ} [NeZero n] [NeZero p]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hn3 : 3 ≤ n) (hnOdd : Odd n) (hpn : p ∣ n)
    (u v : ZMod n → V)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ x, (secondOrderDefectGraph G).neighborFinset (v x) =
      {v (x - 1), v (x + 1)})
    (t : ZMod p) :
    Even (((admissibleDifferences n).filter (fun δ ↦
        ZMod.castHom hpn (ZMod p) δ = t ∧
          (∑ x : ZMod n, anchorPairMultiplicity G (u x) v δ) = n)).card +
      ((admissibleDifferences n).filter (fun δ ↦
        ZMod.castHom hpn (ZMod p) δ = t ∧
          (∑ x : ZMod n, anchorPairMultiplicity G (v x) u δ) = n)).card) := by
  let w : Bool → ZMod n → V := fun b ↦ if b then v else u
  have hw : ∀ b, Function.Injective (w b) := by
    intro b
    cases b <;> simp [w, hu, hv]
  have hwD : ∀ b x, (secondOrderDefectGraph G).neighborFinset (w b x) =
      {w b (x - 1), w b (x + 1)} := by
    intro b x
    cases b
    · change (secondOrderDefectGraph G).neighborFinset (u x) =
        {u (x - 1), u (x + 1)}
      exact huD x
    · change (secondOrderDefectGraph G).neighborFinset (v x) =
        {v (x - 1), v (x + 1)}
      exact hvD x
  have h := even_sum_equalBlock_fullMass_fiber G hfree hd heven hmin hcard
    hn3 hnOdd hpn w hw hwD Finset.univ t
  have huniv : (Finset.univ : Finset Bool) = {false, true} := by decide
  have heraseF : ({false, true} : Finset Bool).erase false = {true} := by decide
  have heraseT : ({false, true} : Finset Bool).erase true = {false} := by decide
  simp [huniv, heraseF, heraseT, w] at h
  simpa [add_comm] using h

end

end Erdos85
