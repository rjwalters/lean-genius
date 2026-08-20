import Proofs.Erdos85MuNegThreeZeroFiveExplicitEigenfamilies
import Proofs.Erdos85EigenfamilyCharpolyFactor

/-! # Explicit irrational eigenfamilies on the two h305 C8 shores -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Rational part of the two `sqrt 2` modes (and their alternating twists). -/
def h305SqrtTwoModeA (neg m : Fin 2) (i : ZMod 8) : ℤ :=
  let a := if m = 0 then
    if i.val = 1 then 1 else if i.val = 3 then -1 else
    if i.val = 5 then -1 else if i.val = 7 then 1 else 0
  else
    if i.val = 1 then 1 else if i.val = 3 then 1 else
    if i.val = 5 then -1 else if i.val = 7 then -1 else 0
  if neg = 0 ∨ i.val % 2 = 0 then a else -a

/-- `sqrt 2` coefficient of the two modes. -/
def h305SqrtTwoModeB (neg m : Fin 2) (i : ZMod 8) : ℤ :=
  let b := if m = 0 then
    if i.val = 0 then 1 else if i.val = 4 then -1 else 0
  else
    if i.val = 2 then 1 else if i.val = 6 then -1 else 0
  if neg = 0 ∨ i.val % 2 = 0 then b else -b

/-- The real mode obtained from its two integral coefficient tables. -/
def h305SqrtTwoMode (neg m : Fin 2) (i : ZMod 8) : ℝ :=
  h305SqrtTwoModeA neg m i + Real.sqrt 2 * h305SqrtTwoModeB neg m i

set_option maxRecDepth 100000 in
theorem h305SqrtTwoMode_integral_identities :
    (∀ neg m : Fin 2, ∀ i : ZMod 8,
      h305SqrtTwoModeA neg m (i - 1) + h305SqrtTwoModeA neg m (i + 1) =
        (if neg = 0 then 2 else -2) * h305SqrtTwoModeB neg m i) ∧
    (∀ neg m : Fin 2, ∀ i : ZMod 8,
      h305SqrtTwoModeB neg m (i - 1) + h305SqrtTwoModeB neg m (i + 1) =
        (if neg = 0 then 1 else -1) * h305SqrtTwoModeA neg m i) ∧
    (∀ neg m : Fin 2, ∑ i : ZMod 8, h305SqrtTwoModeA neg m i = 0) ∧
    (∀ neg m : Fin 2, ∑ i : ZMod 8, h305SqrtTwoModeB neg m i = 0) ∧
    (∀ neg m n : Fin 2,
      h305SqrtTwoModeA neg m ((2 * n.val : ℕ) : ZMod 8) = 0 ∧
      h305SqrtTwoModeB neg m ((2 * n.val : ℕ) : ZMod 8) =
        if m = n then 1 else 0) := by
  native_decide

theorem h305SqrtTwoMode_identities :
    (∀ neg m : Fin 2, ∀ i : ZMod 8,
      h305SqrtTwoMode neg m (i - 1) + h305SqrtTwoMode neg m (i + 1) =
        (if neg = 0 then Real.sqrt 2 else -Real.sqrt 2) *
          h305SqrtTwoMode neg m i) ∧
    (∀ neg m : Fin 2, ∑ i : ZMod 8, h305SqrtTwoMode neg m i = 0) ∧
    (∀ neg m n : Fin 2,
      h305SqrtTwoMode neg m ((2 * n.val : ℕ) : ZMod 8) =
        if m = n then (if neg = 0 then Real.sqrt 2 else Real.sqrt 2) else 0) := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  constructor
  · intro neg m i
    have ha := h305SqrtTwoMode_integral_identities.1 neg m i
    have hb := h305SqrtTwoMode_integral_identities.2.1 neg m i
    fin_cases neg
    · norm_num at ha hb ⊢
      have haR : (h305SqrtTwoModeA 0 m (i - 1) : ℝ) +
          h305SqrtTwoModeA 0 m (i + 1) = 2 * h305SqrtTwoModeB 0 m i := by
        exact_mod_cast ha
      have hbR : (h305SqrtTwoModeB 0 m (i - 1) : ℝ) +
          h305SqrtTwoModeB 0 m (i + 1) = h305SqrtTwoModeA 0 m i := by
        exact_mod_cast hb
      simp only [h305SqrtTwoMode]
      calc
        _ = ((h305SqrtTwoModeA 0 m (i - 1) : ℝ) +
              h305SqrtTwoModeA 0 m (i + 1)) + Real.sqrt 2 *
              ((h305SqrtTwoModeB 0 m (i - 1) : ℝ) +
                h305SqrtTwoModeB 0 m (i + 1)) := by ring
        _ = _ := by rw [haR, hbR]; ring_nf; rw [hs]
    · norm_num at ha hb ⊢
      have haR : (h305SqrtTwoModeA 1 m (i - 1) : ℝ) +
          h305SqrtTwoModeA 1 m (i + 1) = -(2 * h305SqrtTwoModeB 1 m i) := by
        exact_mod_cast ha
      have hbR : (h305SqrtTwoModeB 1 m (i - 1) : ℝ) +
          h305SqrtTwoModeB 1 m (i + 1) = -h305SqrtTwoModeA 1 m i := by
        exact_mod_cast hb
      simp only [h305SqrtTwoMode]
      calc
        _ = ((h305SqrtTwoModeA 1 m (i - 1) : ℝ) +
              h305SqrtTwoModeA 1 m (i + 1)) + Real.sqrt 2 *
              ((h305SqrtTwoModeB 1 m (i - 1) : ℝ) +
                h305SqrtTwoModeB 1 m (i + 1)) := by ring
        _ = _ := by rw [haR, hbR]; ring_nf; rw [hs]
  constructor
  · intro neg m
    have ha : ∑ i : ZMod 8, h305SqrtTwoModeA neg m i = 0 :=
      h305SqrtTwoMode_integral_identities.2.2.1 neg m
    have hb : ∑ i : ZMod 8, h305SqrtTwoModeB neg m i = 0 :=
      h305SqrtTwoMode_integral_identities.2.2.2.1 neg m
    have haR : ∑ i : ZMod 8, (h305SqrtTwoModeA neg m i : ℝ) = 0 := by
      exact_mod_cast ha
    have hbR : ∑ i : ZMod 8, (h305SqrtTwoModeB neg m i : ℝ) = 0 := by
      exact_mod_cast hb
    simp [h305SqrtTwoMode, sum_add_distrib, ← mul_sum, haR, hbR]
  · intro neg m n
    rw [h305SqrtTwoMode]
    obtain ⟨ha, hb⟩ := h305SqrtTwoMode_integral_identities.2.2.2.2 neg m n
    rw [ha, hb]
    simp

/-- Four shore-supported modes for either irrational eigenvalue. -/
def h305SqrtTwoEigenfamily
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) (neg : Fin 2) :
    (Fin 2 × Fin 2) → V → ℂ := fun q x ↦
  match e.symm x with
  | Sum.inl i => if q.1 = 0 then (h305SqrtTwoMode neg q.2 i : ℂ) else 0
  | Sum.inr i => if q.1 = 1 then (h305SqrtTwoMode neg q.2 i : ℂ) else 0

@[simp] theorem h305SqrtTwoEigenfamily_apply_left
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) (neg : Fin 2)
    (q : Fin 2 × Fin 2) (i : ZMod 8) :
    h305SqrtTwoEigenfamily e neg q (e (Sum.inl i)) =
      if q.1 = 0 then (h305SqrtTwoMode neg q.2 i : ℂ) else 0 := by
  simp [h305SqrtTwoEigenfamily]

@[simp] theorem h305SqrtTwoEigenfamily_apply_right
    {V : Type*} (e : (ZMod 8 ⊕ ZMod 8) ≃ V) (neg : Fin 2)
    (q : Fin 2 × Fin 2) (i : ZMod 8) :
    h305SqrtTwoEigenfamily e neg q (e (Sum.inr i)) =
      if q.1 = 1 then (h305SqrtTwoMode neg q.2 i : ℂ) else 0 := by
  simp [h305SqrtTwoEigenfamily]

theorem h305_sqrtTwoEigenfamily_sum_zero
    {V : Type*} [Fintype V]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V) (neg : Fin 2) :
    ∀ q, ∑ x, h305SqrtTwoEigenfamily e neg q x = 0 := by
  intro q
  calc
    (∑ x, h305SqrtTwoEigenfamily e neg q x) =
        ∑ y : ZMod 8 ⊕ ZMod 8, h305SqrtTwoEigenfamily e neg q (e y) := by
      symm
      apply Fintype.sum_equiv e
      intro y
      rfl
    _ = 0 := by
      rw [Fintype.sum_sum_type]
      rcases q with ⟨q, m⟩
      fin_cases q <;> simp only [h305SqrtTwoEigenfamily_apply_left,
        h305SqrtTwoEigenfamily_apply_right] <;> norm_num <;> norm_cast
      · exact h305SqrtTwoMode_identities.2.1 neg m
      · exact h305SqrtTwoMode_identities.2.1 neg m

theorem h305_sqrtTwoEigenfamily_eigenvalue
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V)
    (hleft : ∀ i, H.neighborFinset (e (Sum.inl i)) =
      {e (Sum.inl (i - 1)), e (Sum.inl (i + 1))})
    (hright : ∀ i, H.neighborFinset (e (Sum.inr i)) =
      {e (Sum.inr (i - 1)), e (Sum.inr (i + 1))})
    (neg : Fin 2) :
    ∀ q, (H.adjMatrix ℂ).mulVec (h305SqrtTwoEigenfamily e neg q) =
      ((if neg = 0 then Real.sqrt 2 else -Real.sqrt 2 : ℝ) : ℂ) •
        h305SqrtTwoEigenfamily e neg q := by
  intro q
  funext x
  obtain ⟨i | i, rfl⟩ := e.surjective x
  · rw [H.adjMatrix_mulVec_apply, hleft, Finset.sum_pair
      (e.injective.ne (fun h ↦ h305_cycle_neighbor_coordinates_ne i
        (Sum.inl.inj h)))]
    simp only [Pi.smul_apply, h305SqrtTwoEigenfamily_apply_left]
    by_cases hq : q.1 = 0
    · simp only [hq, if_true]
      fin_cases neg
      · have h := congrArg (fun z : ℝ ↦ (z : ℂ))
          (h305SqrtTwoMode_identities.1 (0 : Fin 2) q.2 i)
        simpa [smul_eq_mul] using h
      · have h := congrArg (fun z : ℝ ↦ (z : ℂ))
          (h305SqrtTwoMode_identities.1 (1 : Fin 2) q.2 i)
        simpa [smul_eq_mul] using h
    · simp [hq]
  · rw [H.adjMatrix_mulVec_apply, hright, Finset.sum_pair
      (e.injective.ne (fun h ↦ h305_cycle_neighbor_coordinates_ne i
        (Sum.inr.inj h)))]
    simp only [Pi.smul_apply, h305SqrtTwoEigenfamily_apply_right]
    by_cases hq : q.1 = 1
    · simp only [hq, if_true]
      fin_cases neg
      · have h := congrArg (fun z : ℝ ↦ (z : ℂ))
          (h305SqrtTwoMode_identities.1 (0 : Fin 2) q.2 i)
        simpa [smul_eq_mul] using h
      · have h := congrArg (fun z : ℝ ↦ (z : ℂ))
          (h305SqrtTwoMode_identities.1 (1 : Fin 2) q.2 i)
        simpa [smul_eq_mul] using h
    · simp [hq]

theorem h305_sqrtTwoEigenfamily_linearIndependent
    {V : Type*} [Fintype V]
    (e : (ZMod 8 ⊕ ZMod 8) ≃ V) (neg : Fin 2) :
    LinearIndependent ℂ (h305SqrtTwoEigenfamily e neg) := by
  classical
  have hrR : (Real.sqrt 2 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hr : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrR
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  rcases q with ⟨q, m⟩
  fin_cases q
  · have h := congrFun hg (e (Sum.inl ((2 * m.val : ℕ) : ZMod 8)))
    rw [Fintype.sum_prod_type] at h
    fin_cases m
    · have hv0 := h305SqrtTwoMode_identities.2.2 neg (0 : Fin 2) (0 : Fin 2)
      have hv1 := h305SqrtTwoMode_identities.2.2 neg (1 : Fin 2) (0 : Fin 2)
      norm_num at hv0 hv1
      simp [Fin.sum_univ_two, h305SqrtTwoEigenfamily, hv0, hv1] at h
      exact h
    · have hv0 := h305SqrtTwoMode_identities.2.2 neg (0 : Fin 2) (1 : Fin 2)
      have hv1 := h305SqrtTwoMode_identities.2.2 neg (1 : Fin 2) (1 : Fin 2)
      norm_num at hv0 hv1
      simp [Fin.sum_univ_two, h305SqrtTwoEigenfamily, hv0, hv1] at h
      exact h
  · have h := congrFun hg (e (Sum.inr ((2 * m.val : ℕ) : ZMod 8)))
    rw [Fintype.sum_prod_type] at h
    fin_cases m
    · have hv0 := h305SqrtTwoMode_identities.2.2 neg (0 : Fin 2) (0 : Fin 2)
      have hv1 := h305SqrtTwoMode_identities.2.2 neg (1 : Fin 2) (0 : Fin 2)
      norm_num at hv0 hv1
      simp [Fin.sum_univ_two, h305SqrtTwoEigenfamily, hv0, hv1] at h
      exact h
    · have hv0 := h305SqrtTwoMode_identities.2.2 neg (0 : Fin 2) (1 : Fin 2)
      have hv1 := h305SqrtTwoMode_identities.2.2 neg (1 : Fin 2) (1 : Fin 2)
      norm_num at hv0 hv1
      simp [Fin.sum_univ_two, h305SqrtTwoEigenfamily, hv0, hv1] at h
      exact h

/-- Each sign of `sqrt 2` transfers to four independent service eigenvectors
at the opposite sign. -/
theorem h305_sqrtTwoEigenfamily_transfer
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
      MuNegThreeZeroFiveTfShoreMode R (fun j ↦ e (Sum.inr j)))
    (neg : Fin 2) :
    let mu : ℂ := ((if neg = 0 then Real.sqrt 2 else -Real.sqrt 2 : ℝ) : ℂ)
    (∀ q, (Cedge.adjMatrix ℂ).mulVec
        (edgeEndpointSumVector R (h305SqrtTwoEigenfamily e neg q)) =
      (-mu) • edgeEndpointSumVector R (h305SqrtTwoEigenfamily e neg q)) ∧
    LinearIndependent ℂ
      (fun q ↦ edgeEndpointSumVector R (h305SqrtTwoEigenfamily e neg q)) := by
  dsimp only
  exact h305_equiv_correctShoreModes_eigenfamily_transfer
    H R Cedge hservice e hmodeu hmodev (h305SqrtTwoEigenfamily e neg)
      (((if neg = 0 then Real.sqrt 2 else -Real.sqrt 2 : ℝ) : ℂ))
      (h305_sqrtTwoEigenfamily_sum_zero e neg)
      (h305_sqrtTwoEigenfamily_eigenvalue H e hleft hright neg)
      (h305_sqrtTwoEigenfamily_linearIndependent e neg)

end

/-- Both conjugate irrational service eigenvalues have multiplicity at least
four.  Equivalently, their fourth-power linear factors divide the service
characteristic polynomial. -/
theorem h305_irrational_service_charpoly_factors
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
    (Polynomial.X - Polynomial.C ((Real.sqrt 2 : ℝ) : ℂ)) ^ 4 ∣
        (Cedge.adjMatrix ℂ).charpoly ∧
      (Polynomial.X - Polynomial.C (-((Real.sqrt 2 : ℝ) : ℂ))) ^ 4 ∣
        (Cedge.adjMatrix ℂ).charpoly := by
  obtain ⟨hposEig, hposLi⟩ := h305_sqrtTwoEigenfamily_transfer
    H R Cedge hservice e hleft hright hmodeu hmodev (1 : Fin 2)
  obtain ⟨hnegEig, hnegLi⟩ := h305_sqrtTwoEigenfamily_transfer
    H R Cedge hservice e hleft hright hmodeu hmodev (0 : Fin 2)
  let fpos : Fin 4 → R.edgeFinset → ℂ := fun q ↦
    edgeEndpointSumVector R
      (h305SqrtTwoEigenfamily e 1 (finProdFinEquiv.symm q))
  let fneg : Fin 4 → R.edgeFinset → ℂ := fun q ↦
    edgeEndpointSumVector R
      (h305SqrtTwoEigenfamily e 0 (finProdFinEquiv.symm q))
  constructor
  · apply matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily
      (Cedge.adjMatrix ℂ) ((Real.sqrt 2 : ℝ) : ℂ) 4 fpos
    · intro q
      simpa [fpos] using hposEig (finProdFinEquiv.symm q)
    · exact hposLi.comp _ finProdFinEquiv.symm.injective
  · apply matrix_charpoly_linearFactor_pow_dvd_of_eigenfamily
      (Cedge.adjMatrix ℂ) (-((Real.sqrt 2 : ℝ) : ℂ)) 4 fneg
    · intro q
      simpa [fneg] using hnegEig (finProdFinEquiv.symm q)
    · exact hnegLi.comp _ finProdFinEquiv.symm.injective

end Erdos85

#print axioms Erdos85.h305_sqrtTwoEigenfamily_transfer
#print axioms Erdos85.h305_irrational_service_charpoly_factors
