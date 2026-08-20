import Proofs.Erdos85MuNegThreeZeroFiveEigenfamilyTransfer
import Proofs.Erdos85MuNegThreeZeroFiveIndependentEigenvectors

/-! # Explicit rational eigenfamilies on the two h305 C8 shores -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The two integral zero-eigenmodes of C8, distinguished by parity. -/
def h305ZeroMode (m : Fin 2) (i : ZMod 8) : ℤ :=
  if i.val % 4 = m.val then 1
  else if i.val % 4 = m.val + 2 then -1 else 0

set_option maxRecDepth 100000 in
theorem h305ZeroMode_identities :
    (∀ m : Fin 2, ∀ i : ZMod 8,
      h305ZeroMode m (i - 1) + h305ZeroMode m (i + 1) = 0) ∧
    (∀ m : Fin 2, ∑ i : ZMod 8, h305ZeroMode m i = 0) ∧
    (∀ m n : Fin 2, h305ZeroMode m (n.val : ZMod 8) =
      if m = n then 1 else 0) := by
  native_decide

/-- Four zero modes: two coordinate modes on each of the two shores. -/
def h305ZeroEigenfamily
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) :
    (Fin 2 × Fin 2) → V → ℂ := fun q x ↦
  match e.symm x with
  | Sum.inl i => if q.1 = 0 then (h305ZeroMode q.2 i : ℂ) else 0
  | Sum.inr i => if q.1 = 1 then (h305ZeroMode q.2 i : ℂ) else 0

@[simp] theorem h305ZeroEigenfamily_apply_left
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (q : Fin 2 × Fin 2) (i : ZMod 8) :
    h305ZeroEigenfamily e q (e (Sum.inl i)) =
      if q.1 = 0 then (h305ZeroMode q.2 i : ℂ) else 0 := by
  simp [h305ZeroEigenfamily]

@[simp] theorem h305ZeroEigenfamily_apply_right
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (q : Fin 2 × Fin 2) (i : ZMod 8) :
    h305ZeroEigenfamily e q (e (Sum.inr i)) =
      if q.1 = 1 then (h305ZeroMode q.2 i : ℂ) else 0 := by
  simp [h305ZeroEigenfamily]

theorem h305_zeroEigenfamily_sum_zero
    {V : Type*} [Fintype V]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V) :
    ∀ q, ∑ x, h305ZeroEigenfamily e q x = 0 := by
  intro q
  calc
    (∑ x, h305ZeroEigenfamily e q x) =
        ∑ y : ZMod 8 ⊕ ZMod 8, h305ZeroEigenfamily e q (e y) := by
      symm
      apply Fintype.sum_equiv e
      intro y
      rfl
    _ = 0 := by
      rw [Fintype.sum_sum_type]
      rcases q with ⟨q, m⟩
      fin_cases q
      · simp only [h305ZeroEigenfamily_apply_left,
          h305ZeroEigenfamily_apply_right]
        norm_num
        norm_cast
        exact h305ZeroMode_identities.2.1 m
      · simp only [h305ZeroEigenfamily_apply_left,
          h305ZeroEigenfamily_apply_right]
        norm_num
        norm_cast
        exact h305ZeroMode_identities.2.1 m

theorem h305_zeroEigenfamily_eigenvalue_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))}) :
    ∀ q, (H.adjMatrix ℂ).mulVec (h305ZeroEigenfamily e q) =
      (0 : ℂ) • h305ZeroEigenfamily e q := by
  intro q
  funext x
  obtain ⟨i | i, rfl⟩ := e.surjective x
  · rw [H.adjMatrix_mulVec_apply, hleft]
    rw [Finset.sum_pair
      (e.injective.ne (fun h ↦ h305_cycle_neighbor_coordinates_ne i
        (Sum.inl.inj h)))]
    simp only [Pi.smul_apply, zero_smul,
      h305ZeroEigenfamily_apply_left]
    by_cases hq : q.1 = 0
    · simp only [hq, if_true]
      norm_cast
      exact h305ZeroMode_identities.1 q.2 i
    · simp [hq]
  · rw [H.adjMatrix_mulVec_apply, hright]
    rw [Finset.sum_pair
      (e.injective.ne (fun h ↦ h305_cycle_neighbor_coordinates_ne i
        (Sum.inr.inj h)))]
    simp only [Pi.smul_apply, zero_smul,
      h305ZeroEigenfamily_apply_right]
    by_cases hq : q.1 = 1
    · simp only [hq, if_true]
      norm_cast
      exact h305ZeroMode_identities.1 q.2 i
    · simp [hq]

theorem h305_zeroEigenfamily_linearIndependent
    {V : Type*} [Fintype V]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V) :
    LinearIndependent ℂ (h305ZeroEigenfamily e) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  rcases q with ⟨q, m⟩
  fin_cases q
  · have h := congrFun hg (e (Sum.inl (m.val : ZMod 8)))
    rw [Fintype.sum_prod_type] at h
    simp [Fin.sum_univ_two, h305ZeroEigenfamily,
      h305ZeroMode_identities.2.2] at h
    fin_cases m <;> simpa using h
  · have h := congrFun hg (e (Sum.inr (m.val : ZMod 8)))
    rw [Fintype.sum_prod_type] at h
    simp [Fin.sum_univ_two, h305ZeroEigenfamily,
      h305ZeroMode_identities.2.2] at h
    fin_cases m <;> simpa using h

/-- The four rational zero modes transfer to four independent zero modes of
the exterior service graph. -/
theorem h305_zeroEigenfamily_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))})
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R
        (fun i ↦ e (Sum.inl i)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun i ↦ e (Sum.inl i)))
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R
        (fun j ↦ e (Sum.inr j)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun j ↦ e (Sum.inr j))) :
    (∀ q, (Cedge.adjMatrix ℂ).mulVec
        (edgeEndpointSumVector R (h305ZeroEigenfamily e q)) =
      (0 : ℂ) • edgeEndpointSumVector R (h305ZeroEigenfamily e q)) ∧
    LinearIndependent ℂ
      (fun q ↦ edgeEndpointSumVector R (h305ZeroEigenfamily e q)) := by
  simpa using h305_equiv_correctShoreModes_eigenfamily_transfer
    H R Cedge hservice e hmodeu hmodev (h305ZeroEigenfamily e) 0
      (h305_zeroEigenfamily_sum_zero e)
      (h305_zeroEigenfamily_eigenvalue_zero H e hleft hright)
      (h305_zeroEigenfamily_linearIndependent e)

/-- Package the two shore-supported alternating modes as a `Fin 2` family. -/
def h305AlternatingEigenfamily
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) : Fin 2 → V → ℂ := fun q ↦
  if q = 0 then h305FirstAlternatingVector e
  else h305SecondAlternatingVector e

theorem h305_alternatingEigenfamily_sum_zero
    {V : Type*} [Fintype V]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V) :
    ∀ q, ∑ x, h305AlternatingEigenfamily e q x = 0 := by
  intro q
  have h := h305_alternatingVectors_sum_zero e
  fin_cases q
  · simpa [h305AlternatingEigenfamily] using h.1
  · simpa [h305AlternatingEigenfamily] using h.2

theorem h305_alternatingEigenfamily_eigenvalue_neg_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))}) :
    ∀ q, (H.adjMatrix ℂ).mulVec (h305AlternatingEigenfamily e q) =
      (-2 : ℂ) • h305AlternatingEigenfamily e q := by
  intro q
  have h := h305_alternatingVectors_eigenvalue_neg_two
    H e hleft hright
  fin_cases q
  · simpa [h305AlternatingEigenfamily] using h.1
  · simpa [h305AlternatingEigenfamily] using h.2

theorem h305_alternatingEigenfamily_linearIndependent
    {V : Type*} [Fintype V]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V) :
    LinearIndependent ℂ (h305AlternatingEigenfamily e) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  fin_cases q
  · have h := congrFun hg (e (Sum.inl (0 : ZMod 8)))
    rw [Fin.sum_univ_two] at h
    simpa [h305AlternatingEigenfamily, h305FirstAlternatingVector,
      h305SecondAlternatingVector, h305AlternatingSign] using h
  · have h := congrFun hg (e (Sum.inr (0 : ZMod 8)))
    rw [Fin.sum_univ_two] at h
    simpa [h305AlternatingEigenfamily, h305FirstAlternatingVector,
      h305SecondAlternatingVector, h305AlternatingSign] using h

/-- The two alternating modes transfer to two independent service
eigenvectors at eigenvalue `2`. -/
theorem h305_alternatingEigenfamily_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))})
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R
        (fun i ↦ e (Sum.inl i)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun i ↦ e (Sum.inl i)))
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R
        (fun j ↦ e (Sum.inr j)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun j ↦ e (Sum.inr j))) :
    (∀ q, (Cedge.adjMatrix ℂ).mulVec
        (edgeEndpointSumVector R (h305AlternatingEigenfamily e q)) =
      (2 : ℂ) • edgeEndpointSumVector R
        (h305AlternatingEigenfamily e q)) ∧
    LinearIndependent ℂ
      (fun q ↦ edgeEndpointSumVector R
        (h305AlternatingEigenfamily e q)) := by
  simpa using h305_equiv_correctShoreModes_eigenfamily_transfer
    H R Cedge hservice e hmodeu hmodev (h305AlternatingEigenfamily e) (-2)
      (h305_alternatingEigenfamily_sum_zero e)
      (h305_alternatingEigenfamily_eigenvalue_neg_two H e hleft hright)
      (h305_alternatingEigenfamily_linearIndependent e)

/-- Constant `+1` on the first shore and `-1` on the second. -/
def h305ShoreDifferenceVector
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) : V → ℂ := fun x ↦
  match e.symm x with
  | Sum.inl _ => 1
  | Sum.inr _ => -1

theorem h305_shoreDifference_sum_zero
    {V : Type*} [Fintype V]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V) :
    ∑ x, h305ShoreDifferenceVector e x = 0 := by
  calc
    (∑ x, h305ShoreDifferenceVector e x) =
        ∑ y : ZMod 8 ⊕ ZMod 8, h305ShoreDifferenceVector e (e y) := by
      symm
      apply Fintype.sum_equiv e
      intro y
      rfl
    _ = 0 := by
      rw [Fintype.sum_sum_type]
      simp [h305ShoreDifferenceVector]

theorem h305_shoreDifference_eigenvalue_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))}) :
    (H.adjMatrix ℂ).mulVec (h305ShoreDifferenceVector e) =
      (2 : ℂ) • h305ShoreDifferenceVector e := by
  funext x
  obtain ⟨i | i, rfl⟩ := e.surjective x
  · rw [H.adjMatrix_mulVec_apply, hleft]
    rw [Finset.sum_pair
      (e.injective.ne (fun h ↦ h305_cycle_neighbor_coordinates_ne i
        (Sum.inl.inj h)))]
    simp [h305ShoreDifferenceVector]
    norm_num
  · rw [H.adjMatrix_mulVec_apply, hright]
    rw [Finset.sum_pair
      (e.injective.ne (fun h ↦ h305_cycle_neighbor_coordinates_ne i
        (Sum.inr.inj h)))]
    simp [h305ShoreDifferenceVector]
    norm_num

/-- Singleton family form of the shore-difference mode. -/
def h305ShoreDifferenceFamily
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) : Fin 1 → V → ℂ :=
  fun _ ↦ h305ShoreDifferenceVector e

theorem h305_shoreDifferenceFamily_linearIndependent
    {V : Type*} [Fintype V]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V) :
    LinearIndependent ℂ (h305ShoreDifferenceFamily e) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have hq : q = 0 := Subsingleton.elim _ _
  subst q
  have h := congrFun hg (e (Sum.inl (0 : ZMod 8)))
  rw [Fin.sum_univ_one] at h
  simpa [h305ShoreDifferenceFamily, h305ShoreDifferenceVector] using h

/-- The shore-difference mode transfers to a nonzero service eigenvector at
eigenvalue `-2`. -/
theorem h305_shoreDifference_transfer
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))})
    (hmodeu : MuNegThreeZeroFiveTriangleShoreMode R
        (fun i ↦ e (Sum.inl i)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun i ↦ e (Sum.inl i)))
    (hmodev : MuNegThreeZeroFiveTriangleShoreMode R
        (fun j ↦ e (Sum.inr j)) ∨
      MuNegThreeZeroFiveTfShoreMode R (fun j ↦ e (Sum.inr j))) :
    (∀ q, (Cedge.adjMatrix ℂ).mulVec
        (edgeEndpointSumVector R (h305ShoreDifferenceFamily e q)) =
      (-2 : ℂ) • edgeEndpointSumVector R
        (h305ShoreDifferenceFamily e q)) ∧
    LinearIndependent ℂ
      (fun q ↦ edgeEndpointSumVector R
        (h305ShoreDifferenceFamily e q)) := by
  apply h305_equiv_correctShoreModes_eigenfamily_transfer
    H R Cedge hservice e hmodeu hmodev (h305ShoreDifferenceFamily e) 2
  · intro q
    exact h305_shoreDifference_sum_zero e
  · intro q
    exact h305_shoreDifference_eigenvalue_two H e hleft hright
  · exact h305_shoreDifferenceFamily_linearIndependent e

end

end Erdos85

#print axioms Erdos85.h305_zeroEigenfamily_linearIndependent
#print axioms Erdos85.h305_zeroEigenfamily_transfer
#print axioms Erdos85.h305_alternatingEigenfamily_linearIndependent
#print axioms Erdos85.h305_alternatingEigenfamily_transfer
#print axioms Erdos85.h305_shoreDifferenceFamily_linearIndependent
#print axioms Erdos85.h305_shoreDifference_transfer
