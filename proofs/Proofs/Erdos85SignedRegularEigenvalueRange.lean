import Proofs.Erdos85BinarySquareSignedEigenvectorSupport

/-!
# Arithmetic range of a signed regular-graph eigenvalue

If a `k`-regular graph has a nonempty integral eigenvector with every entry
equal to `+1` or `-1`, its eigenvalue lies in `[-k,k]` and has the parity of
`k`.  Combined with the size-two support equation at `q = 8`, this reduces the
joint defect eigenvalue to six explicit odd integers without a spectral census.
-/

open SimpleGraph Matrix

namespace Erdos85

/-- A sum of signs is the cardinality minus twice the number of negative
signs. -/
theorem sum_eq_card_sub_two_mul_filter_neg_one
    {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℤ)
    (hf : ∀ x ∈ S, f x = -1 ∨ f x = 1) :
    ∑ x ∈ S, f x = (S.card : ℤ) -
      2 * ((S.filter fun x => f x = -1).card : ℤ) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hfa := hf a (by simp)
      have hfS : ∀ x ∈ S, f x = -1 ∨ f x = 1 := by
        intro x hx
        exact hf x (by simp [hx])
      rw [Finset.sum_insert ha, ih hfS, Finset.card_insert_of_notMem ha]
      rcases hfa with hfa | hfa <;>
        simp [Finset.filter_insert, ha, hfa] <;> ring

/-- Range and parity normal form for a signed eigenvalue of a regular graph. -/
theorem signed_regular_eigenvalue_range_parity
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (v : V → ℤ) (hv : ∀ x, v x = -1 ∨ v x = 1)
    (mu : ℤ)
    (heig : ∀ x, ∑ y ∈ D.neighborFinset x, v y = mu * v x)
    (x : V) :
    -(k : ℤ) ≤ mu ∧ mu ≤ (k : ℤ) ∧
      ∃ t : ℤ, mu = (k : ℤ) - 2 * t := by
  let S := D.neighborFinset x
  let n : ℤ := ((S.filter fun y => v y = -1).card : ℤ)
  have hsum : mu * v x = (k : ℤ) - 2 * n := by
    rw [← heig x, sum_eq_card_sub_two_mul_filter_neg_one S v
      (fun y _ => hv y)]
    change (S.card : ℤ) - 2 * n = _
    rw [D.card_neighborFinset_eq_degree, hreg]
  have hn0 : 0 ≤ n := by positivity
  have hnk : n ≤ (k : ℤ) := by
    change (((S.filter fun y => v y = -1).card : ℕ) : ℤ) ≤ (k : ℤ)
    have hle := Finset.card_filter_le S (fun y => v y = -1)
    have hcard : S.card = k := by
      exact D.card_neighborFinset_eq_degree x |>.trans (hreg x)
    rw [hcard] at hle
    exact_mod_cast hle
  rcases hv x with hx | hx
  · rw [hx] at hsum
    refine ⟨by linarith, by linarith, ?_⟩
    exact ⟨(k : ℤ) - n, by linarith⟩
  · rw [hx] at hsum
    refine ⟨by linarith, by linarith, ⟨n, by linarith⟩⟩

/-- Component-local form: the vector only has to be signed on an
adjacency-closed set containing the chosen vertex. -/
theorem signed_regular_eigenvalue_range_parity_on
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (C : Set V) (hclosed : ∀ x y, x ∈ C → D.Adj x y → y ∈ C)
    (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (v : V → ℤ) (hv : ∀ x, x ∈ C → v x = -1 ∨ v x = 1)
    (mu : ℤ)
    (heig : ∀ x, x ∈ C → ∑ y ∈ D.neighborFinset x, v y = mu * v x)
    (x : V) (hx : x ∈ C) :
    -(k : ℤ) ≤ mu ∧ mu ≤ (k : ℤ) ∧
      ∃ t : ℤ, mu = (k : ℤ) - 2 * t := by
  let S := D.neighborFinset x
  have hSin : ∀ y ∈ S, y ∈ C := by
    intro y hy
    exact hclosed x y hx ((D.mem_neighborFinset x y).mp hy)
  let n : ℤ := ((S.filter fun y => v y = -1).card : ℤ)
  have hsum : mu * v x = (k : ℤ) - 2 * n := by
    rw [← heig x hx, sum_eq_card_sub_two_mul_filter_neg_one S v
      (fun y hy => hv y (hSin y hy))]
    change (S.card : ℤ) - 2 * n = _
    rw [D.card_neighborFinset_eq_degree, hreg]
  have hn0 : 0 ≤ n := by positivity
  have hnk : n ≤ (k : ℤ) := by
    change (((S.filter fun y => v y = -1).card : ℕ) : ℤ) ≤ (k : ℤ)
    have hle := Finset.card_filter_le S (fun y => v y = -1)
    have hcard : S.card = k := by
      exact D.card_neighborFinset_eq_degree x |>.trans (hreg x)
    rw [hcard] at hle
    exact_mod_cast hle
  rcases hv x hx with hxv | hxv
  · rw [hxv] at hsum
    refine ⟨by linarith, by linarith, ?_⟩
    exact ⟨(k : ℤ) - n, by linarith⟩
  · rw [hxv] at hsum
    refine ⟨by linarith, by linarith, ⟨n, by linarith⟩⟩

/-- At order `64`, the support equation and signed seven-regular defect
eigenline leave only the six odd values from `-7` through `3`. -/
theorem orderSixtyFour_signed_sizeTwo_eigenvalue_candidates
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ x, D.degree x = 7)
    (v : V → ℤ) (hv : ∀ x, v x = -1 ∨ v x = 1)
    (mu : ℤ)
    (heig : ∀ x, ∑ y ∈ D.neighborFinset x, v y = mu * v x)
    (x : V) (supportCard : ℕ)
    (hsupport : 2 * (supportCard : ℤ) = 8 * (3 - mu)) :
    mu = -7 ∨ mu = -5 ∨ mu = -3 ∨ mu = -1 ∨ mu = 1 ∨ mu = 3 := by
  obtain ⟨hlow, hupp, t, ht⟩ :=
    signed_regular_eigenvalue_range_parity D 7 hreg v hv mu heig x
  have hs0 : (0 : ℤ) ≤ supportCard := by positivity
  omega

/-- Graph-facing composition with the size-two support law. -/
theorem orderSixtyFour_sizeTwo_jointEigenvalue_candidates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hDreg : ∀ x, (secondOrderDefectGraph G).degree x = 7)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ) (mu : ℤ)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hsum : ∑ x, s x = 0)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = mu * s x)
    (hA_in : ∀ x, x ∈ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 * s x)
    (hA_out : ∀ x, x ∉ c.supp →
      (G.adjMatrix ℤ).mulVec s x = -2 ∨
      (G.adjMatrix ℤ).mulVec s x = 0 ∨
      (G.adjMatrix ℤ).mulVec s x = 2)
    (x : V) (hx : x ∈ c.supp) :
    mu = -7 ∨ mu = -5 ∨ mu = -3 ∨ mu = -1 ∨ mu = 1 ∨ mu = 3 := by
  have hsupport := binarySquare_regular_signedEigenvector_outsideSupport
    G hfree hreg c hc s mu hs_in hs_out hsum hDs hA_in hA_out
  have hclosed : ∀ a b, a ∈ c.supp →
      (secondOrderDefectGraph G).Adj a b → b ∈ c.supp := by
    intro a b ha hab
    rw [ConnectedComponent.mem_supp_iff] at ha ⊢
    rw [← ha]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hab).symm
  obtain ⟨hlow, hupp, t, ht⟩ := signed_regular_eigenvalue_range_parity_on
    (secondOrderDefectGraph G) c.supp hclosed 7 hDreg s hs_in mu
    (fun y _ => hDs y) x hx
  have hs0 : (0 : ℤ) ≤
      (Finset.univ.filter fun y => y ∉ c.supp ∧
        (G.adjMatrix ℤ).mulVec s y ≠ 0).card := by positivity
  omega

end Erdos85

#print axioms Erdos85.sum_eq_card_sub_two_mul_filter_neg_one
#print axioms Erdos85.signed_regular_eigenvalue_range_parity
#print axioms Erdos85.signed_regular_eigenvalue_range_parity_on
#print axioms Erdos85.orderSixtyFour_signed_sizeTwo_eigenvalue_candidates
#print axioms Erdos85.orderSixtyFour_sizeTwo_jointEigenvalue_candidates
