import Proofs.Erdos85EdgeIndexedServiceIndependentEigenvectors

/-! # Two independent service eigenvectors from the h305 two-cycle split -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

def h305AlternatingSign (i : ZMod 8) : ℤ :=
  if i.val % 2 = 0 then 1 else -1

set_option maxRecDepth 100000 in
theorem h305AlternatingSign_identities :
    (∀ i : ZMod 8,
      h305AlternatingSign (i - 1) + h305AlternatingSign (i + 1) =
        -2 * h305AlternatingSign i) ∧
    (∑ i : ZMod 8, h305AlternatingSign i) = 0 ∧
    (∀ i : ZMod 8, h305AlternatingSign (i + 4) =
      h305AlternatingSign i) ∧
    ∀ i : ZMod 8, h305AlternatingSign i ≠ 0 := by
  native_decide

set_option maxRecDepth 100000 in
theorem h305_cycle_neighbor_coordinates_ne :
    ∀ i : ZMod 8, i - 1 ≠ i + 1 := by
  native_decide

set_option maxRecDepth 100000 in
theorem h305_antipodal_coordinates_ne_and_signSum_ne :
    (∀ i : ZMod 8, i ≠ i + 4) ∧
      ∀ i : ZMod 8,
        h305AlternatingSign i + h305AlternatingSign (i + 4) ≠ 0 := by
  native_decide

/-- Alternating vector on the first of two labeled eight-cycles. -/
def h305FirstAlternatingVector
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) : V → ℂ := fun x ↦
  match e.symm x with
  | Sum.inl i => (h305AlternatingSign i : ℂ)
  | Sum.inr _ => 0

/-- Alternating vector on the second of two labeled eight-cycles. -/
def h305SecondAlternatingVector
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) : V → ℂ := fun x ↦
  match e.symm x with
  | Sum.inl _ => 0
  | Sum.inr i => (h305AlternatingSign i : ℂ)

@[simp] theorem h305FirstAlternatingVector_apply_left
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) (i : ZMod 8) :
    h305FirstAlternatingVector e (e (Sum.inl i)) =
      (h305AlternatingSign i : ℂ) := by
  simp [h305FirstAlternatingVector]

@[simp] theorem h305FirstAlternatingVector_apply_right
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) (i : ZMod 8) :
    h305FirstAlternatingVector e (e (Sum.inr i)) = 0 := by
  simp [h305FirstAlternatingVector]

@[simp] theorem h305SecondAlternatingVector_apply_left
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) (i : ZMod 8) :
    h305SecondAlternatingVector e (e (Sum.inl i)) = 0 := by
  simp [h305SecondAlternatingVector]

@[simp] theorem h305SecondAlternatingVector_apply_right
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) (i : ZMod 8) :
    h305SecondAlternatingVector e (e (Sum.inr i)) =
      (h305AlternatingSign i : ℂ) := by
  simp [h305SecondAlternatingVector]

theorem h305_alternatingVectors_sum_zero
    {V : Type*} [Fintype V]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V) :
    (∑ x, h305FirstAlternatingVector e x) = 0 ∧
      (∑ x, h305SecondAlternatingVector e x) = 0 := by
  constructor
  · calc
      (∑ x, h305FirstAlternatingVector e x) =
          ∑ y : ZMod 8 ⊕ ZMod 8, h305FirstAlternatingVector e (e y) := by
            symm
            apply Fintype.sum_equiv e
            intro y
            rfl
      _ = 0 := by
        rw [Fintype.sum_sum_type]
        simp only [h305FirstAlternatingVector_apply_left,
          h305FirstAlternatingVector_apply_right, Finset.sum_const_zero,
          add_zero]
        norm_cast
  · calc
      (∑ x, h305SecondAlternatingVector e x) =
          ∑ y : ZMod 8 ⊕ ZMod 8, h305SecondAlternatingVector e (e y) := by
            symm
            apply Fintype.sum_equiv e
            intro y
            rfl
      _ = 0 := by
        rw [Fintype.sum_sum_type]
        simp only [h305SecondAlternatingVector_apply_left,
          h305SecondAlternatingVector_apply_right, Finset.sum_const_zero,
          zero_add]
        norm_cast

theorem h305_alternatingVectors_eigenvalue_neg_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))}) :
    (H.adjMatrix ℂ).mulVec (h305FirstAlternatingVector e) =
        (-2 : ℂ) • h305FirstAlternatingVector e ∧
      (H.adjMatrix ℂ).mulVec (h305SecondAlternatingVector e) =
        (-2 : ℂ) • h305SecondAlternatingVector e := by
  constructor <;> funext x
  · obtain ⟨i | i, rfl⟩ := e.surjective x
    · rw [H.adjMatrix_mulVec_apply, hleft]
      rw [Finset.sum_pair
        (e.injective.ne (fun h ↦ h305_cycle_neighbor_coordinates_ne i
          (Sum.inl.inj h)))]
      simp only [Pi.smul_apply, smul_eq_mul,
        h305FirstAlternatingVector_apply_left]
      norm_cast
      exact h305AlternatingSign_identities.1 i
    · rw [H.adjMatrix_mulVec_apply, hright]
      rw [Finset.sum_pair
        (e.injective.ne (fun h ↦ h305_cycle_neighbor_coordinates_ne i
          (Sum.inr.inj h)))]
      simp
  · obtain ⟨i | i, rfl⟩ := e.surjective x
    · rw [H.adjMatrix_mulVec_apply, hleft]
      rw [Finset.sum_pair
        (e.injective.ne (fun h ↦ h305_cycle_neighbor_coordinates_ne i
          (Sum.inl.inj h)))]
      simp
    · rw [H.adjMatrix_mulVec_apply, hright]
      rw [Finset.sum_pair
        (e.injective.ne (fun h ↦ h305_cycle_neighbor_coordinates_ne i
          (Sum.inr.inj h)))]
      simp only [Pi.smul_apply, smul_eq_mul,
        h305SecondAlternatingVector_apply_right]
      norm_cast
      exact h305AlternatingSign_identities.1 i

theorem edgeEndpointSumVector_apply_of_toFinset_eq_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (f : V → ℂ) (a : R.edgeFinset) (x y : V) (hxy : x ≠ y)
    (ha : a.1.toFinset = {x, y}) :
    edgeEndpointSumVector R f a = f x + f y := by
  classical
  unfold edgeEndpointSumVector edgeEndpointIncidenceMatrix
  rw [Matrix.mulVec, dotProduct]
  simp only [Matrix.transpose_apply]
  have hfilter : (Finset.univ.filter fun z : V ↦ z ∈ a.1.toFinset) =
      {x, y} := by
    ext z
    simp [ha]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter, hfilter, Finset.sum_pair hxy]

/-- The two alternating h305 cycle modes transfer to two non-proportional
service eigenvectors.  Antipodal exterior edges on the separate cycles are
the detecting coordinates. -/
theorem h305_two_nonproportional_service_eigenvectors
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))})
    (a b : R.edgeFinset) (i j : ZMod 8)
    (ha : a.1.toFinset =
      {e (Sum.inl i), e (Sum.inl (i + 4))})
    (hb : b.1.toFinset =
      {e (Sum.inr j), e (Sum.inr (j + 4))}) :
    (Cedge.adjMatrix ℂ).mulVec
        (edgeEndpointSumVector R (h305FirstAlternatingVector e)) =
        (2 : ℂ) • edgeEndpointSumVector R (h305FirstAlternatingVector e) ∧
      (Cedge.adjMatrix ℂ).mulVec
        (edgeEndpointSumVector R (h305SecondAlternatingVector e)) =
        (2 : ℂ) • edgeEndpointSumVector R (h305SecondAlternatingVector e) ∧
      ∀ z : ℂ, edgeEndpointSumVector R (h305SecondAlternatingVector e) ≠
        z • edgeEndpointSumVector R (h305FirstAlternatingVector e) := by
  have heig := h305_alternatingVectors_eigenvalue_neg_two H e hleft hright
  have hsum := h305_alternatingVectors_sum_zero e
  apply edgeIndexedService_two_nonproportional_eigenvectors
    H R Cedge hservice
      (h305FirstAlternatingVector e) (h305SecondAlternatingVector e)
      hsum.1 hsum.2 heig.1 heig.2 a b
  · rw [edgeEndpointSumVector_apply_of_toFinset_eq_pair R _ a _ _
      (e.injective.ne (fun h ↦ h305_antipodal_coordinates_ne_and_signSum_ne.1 i
        (Sum.inl.inj h))) ha]
    simp only [h305FirstAlternatingVector_apply_left]
    norm_cast
    exact h305_antipodal_coordinates_ne_and_signSum_ne.2 i
  · rw [edgeEndpointSumVector_apply_of_toFinset_eq_pair R _ a _ _
      (e.injective.ne (fun h ↦ h305_antipodal_coordinates_ne_and_signSum_ne.1 i
        (Sum.inl.inj h))) ha]
    simp
  · rw [edgeEndpointSumVector_apply_of_toFinset_eq_pair R _ b _ _
      (e.injective.ne (fun h ↦ h305_antipodal_coordinates_ne_and_signSum_ne.1 j
        (Sum.inr.inj h))) hb]
    simp only [h305SecondAlternatingVector_apply_right]
    norm_cast
    exact h305_antipodal_coordinates_ne_and_signSum_ne.2 j

end

end Erdos85

#print axioms Erdos85.h305_alternatingVectors_eigenvalue_neg_two
#print axioms Erdos85.h305_two_nonproportional_service_eigenvectors
