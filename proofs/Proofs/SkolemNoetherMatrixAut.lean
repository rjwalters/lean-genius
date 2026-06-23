/-
  Skolem-Noether Theorem: K-Algebra Automorphisms of Mn(K) Are Inner
  (cayley-hamilton-minpoly-oq-02-oq-01-oq-01)

  Proof method: Elementary matrix units approach (no Artin-Wedderburn needed).
  Given phi : Mn(K) ≃_K Mn(K), the images phi(E_ij) satisfy the same
  multiplication rules. From these we construct linearly independent vectors p_j,
  form an invertible matrix P, and show phi = conj(P).
-/
import Mathlib

set_option linter.deprecated false

namespace SkolemNoether

variable {K : Type*} [Field K]
variable {n : Type*} [DecidableEq n] [Fintype n]

noncomputable def conjAlgEquiv (P : (Matrix n n K)ˣ) :
    Matrix n n K ≃ₐ[K] Matrix n n K where
  toFun := fun A => P⁻¹.val * A * P.val
  invFun := fun A => P.val * A * P⁻¹.val
  left_inv := fun A => by
    show P.val * (P⁻¹.val * A * P.val) * P⁻¹.val = A
    calc P.val * (P⁻¹.val * A * P.val) * P⁻¹.val
        = (P.val * P⁻¹.val) * A * (P.val * P⁻¹.val) := by simp only [mul_assoc]
      _ = 1 * A * 1 := by rw [Units.mul_inv]
      _ = A := by simp
  right_inv := fun A => by
    show P⁻¹.val * (P.val * A * P⁻¹.val) * P.val = A
    calc P⁻¹.val * (P.val * A * P⁻¹.val) * P.val
        = (P⁻¹.val * P.val) * A * (P⁻¹.val * P.val) := by simp only [mul_assoc]
      _ = 1 * A * 1 := by rw [Units.inv_mul]
      _ = A := by simp
  map_mul' := fun A B => by
    show P⁻¹.val * (A * B) * P.val
        = (P⁻¹.val * A * P.val) * (P⁻¹.val * B * P.val)
    have h : P.val * P⁻¹.val = 1 := Units.mul_inv P
    symm
    calc (P⁻¹.val * A * P.val) * (P⁻¹.val * B * P.val)
        = P⁻¹.val * A * (P.val * P⁻¹.val) * B * P.val := by simp only [mul_assoc]
      _ = P⁻¹.val * A * 1 * B * P.val := by rw [h]
      _ = P⁻¹.val * (A * B) * P.val := by simp only [mul_one, mul_assoc]
  map_add' := fun A B => by
    show P⁻¹.val * (A + B) * P.val
        = P⁻¹.val * A * P.val + P⁻¹.val * B * P.val
    simp [mul_add, add_mul]
  commutes' := fun c => by
    show P⁻¹.val * (algebraMap K (Matrix n n K) c) * P.val
        = algebraMap K (Matrix n n K) c
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm]
    rw [mul_one, Units.inv_mul]

def IsInnerAut (φ : Matrix n n K ≃ₐ[K] Matrix n n K) : Prop :=
  ∃ P : (Matrix n n K)ˣ, ∀ A : Matrix n n K, φ A = P⁻¹.val * A * P.val

theorem conjAlgEquiv_isInner (P : (Matrix n n K)ˣ) :
    IsInnerAut (conjAlgEquiv P) := ⟨P, fun _ => rfl⟩

theorem isInnerAut_id :
    IsInnerAut (AlgEquiv.refl : Matrix n n K ≃ₐ[K] Matrix n n K) := by
  exact ⟨1, fun A => by simp⟩

theorem isInnerAut_symm {φ : Matrix n n K ≃ₐ[K] Matrix n n K}
    (h : IsInnerAut φ) : IsInnerAut φ.symm := by
  obtain ⟨P, hP⟩ := h; refine ⟨P⁻¹, fun A => ?_⟩
  have key : φ.symm A = P.val * A * P⁻¹.val := by
    apply φ.injective; rw [AlgEquiv.apply_symm_apply, hP]; symm
    calc P⁻¹.val * (P.val * A * P⁻¹.val) * P.val
        = (P⁻¹.val * P.val) * A * (P⁻¹.val * P.val) := by simp only [mul_assoc]
      _ = 1 * A * 1 := by rw [Units.inv_mul]
      _ = A := by simp
  rw [key, show (P⁻¹ : (Matrix n n K)ˣ)⁻¹ = P from inv_inv P]

theorem isInnerAut_trans {φ ψ : Matrix n n K ≃ₐ[K] Matrix n n K}
    (hφ : IsInnerAut φ) (hψ : IsInnerAut ψ) : IsInnerAut (φ.trans ψ) := by
  obtain ⟨P, hP⟩ := hφ; obtain ⟨Q, hQ⟩ := hψ
  refine ⟨P * Q, fun A => ?_⟩
  simp only [AlgEquiv.trans_apply]; rw [hP, hQ]; symm
  rw [show (P * Q)⁻¹.val = Q⁻¹.val * P⁻¹.val from by simp [mul_inv_rev, Units.val_mul]]
  rw [show (P * Q).val = P.val * Q.val from Units.val_mul P Q]
  simp only [mul_assoc]

/-
  Part III: Skolem-Noether Proof

  The proof is structured as a chain of lemmas building up to the main theorem.
  All lemmas fully proved (0 sorries, 0 axioms). The mathematical argument:

  1. stdBasis_mul: E_ij * E_kl = delta_jk * E_il
  2. intertwine: phi(E_ij).mulVec(p_k) = delta_jk * p_i
  3. p linearly independent => P invertible
  4. phi(E_ij)*P = P*E_ij => phi(A)*P = P*A by linearity
  5. phi(A) = P*A*P^{-1}
-/

section SkolemNoetherProof

-- Key helper: matrix unit multiplication (routine computation)
private theorem stdBasis_entry (i₀ j₀ : n) (c : K) (a₀ b₀ : n) :
    Matrix.stdBasisMatrix i₀ j₀ c a₀ b₀ = if i₀ = a₀ ∧ j₀ = b₀ then c else 0 := by
  simp [Matrix.stdBasisMatrix, Matrix.single]

private theorem stdBasis_mul (i j k l : n) :
    Matrix.stdBasisMatrix i j (1 : K) * Matrix.stdBasisMatrix k l 1 =
      if j = k then Matrix.stdBasisMatrix i l 1 else 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.zero_apply, stdBasis_entry]
  by_cases hjk : j = k
  · subst hjk; simp only [if_pos rfl, stdBasis_entry]
    rw [Finset.sum_eq_single j
      (fun m _ hm => by simp [Ne.symm hm])
      (fun h => absurd (Finset.mem_univ _) h)]
    split_ifs <;> simp_all [stdBasis_entry]
  · simp only [if_neg hjk]
    apply Finset.sum_eq_zero; intro m _
    split_ifs <;> simp_all [stdBasis_entry]

-- Key helper: phi preserves matrix unit multiplication
private theorem f_mul (φ : Matrix n n K ≃ₐ[K] Matrix n n K) (i j k l : n) :
    φ (Matrix.stdBasisMatrix i j 1) * φ (Matrix.stdBasisMatrix k l 1) =
      if j = k then φ (Matrix.stdBasisMatrix i l 1) else 0 := by
  rw [← map_mul φ, stdBasis_mul]; split_ifs <;> simp [map_zero]

-- Key helper: intertwining property
private theorem intertwine_prop
    (φ : Matrix n n K ≃ₐ[K] Matrix n n K) (i₀ : n) (v₀ : n → K)
    (i j k : n) :
    (φ (Matrix.stdBasisMatrix i j 1)).mulVec
      ((φ (Matrix.stdBasisMatrix k i₀ 1)).mulVec v₀) =
    if j = k then (φ (Matrix.stdBasisMatrix i i₀ 1)).mulVec v₀ else 0 := by
  rw [Matrix.mulVec_mulVec, f_mul φ i j k i₀]
  split_ifs
  · rfl
  · exact Matrix.zero_mulVec v₀

-- Key helper: each p_j is nonzero
private theorem p_ne_zero
    (φ : Matrix n n K ≃ₐ[K] Matrix n n K) (i₀ : n)
    (v₀ : n → K) (hv₀ : (φ (Matrix.stdBasisMatrix i₀ i₀ 1)).mulVec v₀ ≠ 0)
    (j : n) : (φ (Matrix.stdBasisMatrix j i₀ 1)).mulVec v₀ ≠ 0 := by
  intro hpj
  -- By intertwine_prop: phi(E_{i0,j}).mulVec(p_j) = p_{i0} (nonzero)
  have h := intertwine_prop φ i₀ v₀ i₀ j j
  simp only [if_pos rfl] at h
  -- But p_j = 0, so phi(E_{i0,j}).mulVec(0) = 0
  rw [hpj, Matrix.mulVec_zero] at h
  -- 0 = p_{i0}, contradicting hv₀
  exact hv₀ h.symm

-- Key helper: linear independence of constructed vectors
private theorem p_linearIndependent
    (φ : Matrix n n K ≃ₐ[K] Matrix n n K) (i₀ : n)
    (v₀ : n → K) (hv₀ : (φ (Matrix.stdBasisMatrix i₀ i₀ 1)).mulVec v₀ ≠ 0) :
    LinearIndependent K
      (fun j : n => (φ (Matrix.stdBasisMatrix j i₀ 1)).mulVec v₀) := by
  rw [Fintype.linearIndependent_iff]
  intro c hsum k
  -- hsum: ∑ j, c j • p_j = 0
  -- Apply phi(E_{k,k}).mulVec to both sides via the linear map mulVecLin
  set M := Matrix.mulVecLin (φ (Matrix.stdBasisMatrix k k 1)) with hM_def
  have key : M (∑ j : n, c j • (φ (Matrix.stdBasisMatrix j i₀ 1)).mulVec v₀) = 0 := by
    rw [hsum]; exact map_zero M
  -- Distribute: M(∑ c_j • p_j) = ∑ c_j • M(p_j)
  rw [map_sum] at key
  simp only [map_smul] at key
  -- Apply intertwine_prop: M(p_j) = phi(E_{k,k}).mulVec(p_j) = delta_{k,j} * p_k
  simp only [hM_def, show ∀ j, Matrix.mulVecLin (φ (Matrix.stdBasisMatrix k k 1))
      ((φ (Matrix.stdBasisMatrix j i₀ 1)).mulVec v₀) =
      if k = j then (φ (Matrix.stdBasisMatrix k i₀ 1)).mulVec v₀ else 0 from
      fun j => intertwine_prop φ i₀ v₀ k k j] at key
  -- Sum collapses: ∑ c_j • (if k=j then p_k else 0) = c_k • p_k
  simp only [smul_ite, smul_zero] at key
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true] at key
  -- key: c_k • p_k = 0, and p_k ≠ 0, so c_k = 0
  exact (smul_eq_zero.mp key).resolve_right (p_ne_zero φ i₀ v₀ hv₀ k)

/-- **Skolem-Noether Theorem**: Every K-algebra automorphism of Mn(K) is inner.

  Proof: Elementary matrix units approach. No Artin-Wedderburn theory needed.
  The images phi(E_ij) of the standard matrix units satisfy the same
  multiplication rules as E_ij. This constructs linearly independent
  vectors {p_j} and an invertible matrix P with phi = conj(P). -/
theorem skolemNoether [Nonempty n] (φ : Matrix n n K ≃ₐ[K] Matrix n n K) :
    IsInnerAut φ := by
  obtain ⟨i₀⟩ := ‹Nonempty n›
  -- phi(E_{i0,i0}) != 0, so find v0 with nonzero action
  obtain ⟨v₀, hv₀⟩ : ∃ v : n → K,
      (φ (Matrix.stdBasisMatrix i₀ i₀ 1)).mulVec v ≠ 0 := by
    by_contra hall; push_neg at hall
    have hzero : φ (Matrix.stdBasisMatrix i₀ i₀ 1) = 0 := by
      have mulvec_single : ∀ (M : Matrix n n K) (i j : n),
          M.mulVec (Pi.single j 1) i = M i j := by
        intro M i j
        simp [Matrix.mulVec, Matrix.vecMul, Pi.single_apply,
              Finset.sum_ite_eq', Finset.mem_univ]
      ext a b
      have key := congr_fun (hall (Pi.single b 1)) a
      simp only [Pi.zero_apply] at key
      rwa [mulvec_single] at key
    have hne : Matrix.stdBasisMatrix i₀ i₀ (1 : K) ≠ 0 := by
      intro h; have := congr_fun (congr_fun h i₀) i₀
      simp [Matrix.stdBasisMatrix, Matrix.of_apply] at this
    exact hne (φ.injective (hzero.trans (map_zero φ).symm))
  -- Define column vectors p_j and matrix P
  set p : n → (n → K) := fun j => (φ (Matrix.stdBasisMatrix j i₀ 1)).mulVec v₀
  set Pmat : Matrix n n K := Matrix.of (fun i j => p j i)
  -- P is invertible (linearly independent columns)
  obtain ⟨Pu, hPu⟩ : IsUnit Pmat := by
    have hli := p_linearIndependent φ i₀ v₀ hv₀
    -- Pmat.mulVec w = ∑ j, w_j • p_j (columns of P are the p_j vectors)
    have hmulvec : ∀ w : n → K, Pmat.mulVec w = ∑ j : n, w j • p j := by
      intro w; ext i
      simp only [Matrix.mulVec, Matrix.dotProduct, Pmat, Matrix.of_apply,
                  Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- mulVec is injective from linear independence of columns
    have hinj : Function.Injective (Matrix.mulVecLin Pmat) := by
      intro u v huv
      have h0 : Pmat.mulVec (u - v) = 0 := by
        show (Matrix.mulVecLin Pmat) (u - v) = 0
        rw [map_sub, sub_eq_zero]; exact huv
      rw [hmulvec] at h0
      have hcoeff := (Fintype.linearIndependent_iff.mp hli) (u - v) h0
      ext j; exact sub_eq_zero.mpr (by simpa using (hcoeff j).symm)
    -- Injective endomorphism of fin-dim space → surjective → IsUnit
    have hbij : Function.Bijective (Matrix.mulVecLin Pmat) :=
      ⟨hinj, (LinearMap.injective_iff_surjective.mp hinj)⟩
    rw [Matrix.isUnit_iff_isUnit_det]
    rwa [Matrix.isUnit_det_iff_isUnit_mulVecLin, LinearMap.isUnit_iff_bijective]
  -- The intertwining: phi(A) * P = P * A for all A
  -- (from phi(E_ij)*P = P*E_ij on generators, extended by K-linearity)
  have hintertwine : ∀ A : Matrix n n K, φ A * Pu.val = Pu.val * A := by
    -- Step 1: Intertwining for basis elements E_{ij}
    have hbasis_intertwine : ∀ i j : n,
        φ (Matrix.stdBasisMatrix i j 1) * Pmat = Pmat * Matrix.stdBasisMatrix i j 1 := by
      intro i j; ext a b
      -- Column b of LHS = φ(E_ij).mulVec(column_b(P)) = φ(E_ij).mulVec(p_b)
      simp only [Matrix.mul_apply, Pmat, Matrix.of_apply]
      -- LHS: ∑_m φ(E_ij)_{a,m} * p_b_m = (φ(E_ij).mulVec(p_b))_a
      -- RHS: ∑_m P_{a,m} * E_ij_{m,b} = P_{a,j} * δ_{j,b} = δ_{jb} * p_j_a
      -- By intertwine_prop: φ(E_ij).mulVec(p_b) = δ_{jb} * p_i
      have hlhs : ∑ m : n, φ (Matrix.stdBasisMatrix i j 1) a m * p b m =
          (φ (Matrix.stdBasisMatrix i j 1)).mulVec (p b) a := by
        simp [Matrix.mulVec, Matrix.dotProduct]
      have hrhs : ∑ m : n, p m a * Matrix.stdBasisMatrix i j (1 : K) m b =
          if j = b then p i a else 0 := by
        rw [Finset.sum_eq_single i (fun m _ hm => by simp [stdBasis_entry, Ne.symm hm])
            (fun h => absurd (Finset.mem_univ _) h)]
        simp [stdBasis_entry]
      rw [hlhs, hrhs]
      have := congr_fun (intertwine_prop φ i₀ v₀ i j b) a
      simp only [p] at this ⊢
      exact this
    -- Step 2: Every matrix decomposes as A = ∑_{i,j} A_ij • E_ij
    have hdecomp : ∀ A : Matrix n n K,
        A = ∑ i : n, ∑ j : n, A i j • Matrix.stdBasisMatrix i j 1 := by
      intro A; ext a b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, stdBasis_entry]
      rw [Finset.sum_eq_single a (fun m _ hm => by simp [Ne.symm hm])
          (fun h => absurd (Finset.mem_univ _) h)]
      simp [Finset.sum_eq_single b (fun m _ hm => by simp [Ne.symm hm])
          (fun h => absurd (Finset.mem_univ _) h)]
    -- Step 3: Extend by K-linearity
    intro A
    conv_lhs => rw [hdecomp A]
    rw [map_sum]; simp_rw [map_sum, map_smul]
    simp_rw [Matrix.smul_mul_assoc, Matrix.mul_smul_comm]
    -- Now both sides have ∑∑ A_ij • (φ(E_ij) * P) vs ∑∑ A_ij • (P * E_ij)
    congr 1; ext i; congr 1; ext j
    rw [hPu]; exact hbasis_intertwine i j
  -- Conclude: phi(A) = P * A * P⁻¹
  refine ⟨Pu⁻¹, fun A => ?_⟩
  rw [show (Pu⁻¹ : (Matrix n n K)ˣ)⁻¹ = Pu from inv_inv Pu]
  calc φ A = φ A * 1 := (mul_one _).symm
    _ = φ A * (Pu.val * Pu⁻¹.val) := by rw [Units.mul_inv]
    _ = φ A * Pu.val * Pu⁻¹.val := by rw [mul_assoc]
    _ = Pu.val * A * Pu⁻¹.val := by rw [hintertwine A]

end SkolemNoetherProof

section Consequences
variable [Nonempty n]

theorem exists_conjugating_matrix (φ : Matrix n n K ≃ₐ[K] Matrix n n K) :
    ∃ P : (Matrix n n K)ˣ, ∀ A, φ A = P⁻¹.val * A * P.val := skolemNoether φ

theorem surjection_units_to_aut (φ : Matrix n n K ≃ₐ[K] Matrix n n K) :
    ∃ P : (Matrix n n K)ˣ, φ = conjAlgEquiv P := by
  obtain ⟨P, hP⟩ := skolemNoether φ; exact ⟨P, AlgEquiv.ext (fun A => hP A)⟩
end Consequences

theorem automorphism_preserves_minpoly (φ : Matrix n n K ≃ₐ[K] Matrix n n K)
    (A : Matrix n n K) : minpoly K (φ A) = minpoly K A :=
  minpoly.algEquiv_eq φ A

theorem aut_ext {φ ψ : Matrix n n K ≃ₐ[K] Matrix n n K}
    (h : ∀ A : Matrix n n K, φ A = ψ A) : φ = ψ := AlgEquiv.ext h

theorem skolemNoether_one
    (φ : Matrix (Fin 1) (Fin 1) K ≃ₐ[K] Matrix (Fin 1) (Fin 1) K)
    (A : Matrix (Fin 1) (Fin 1) K) : φ A = A := by
  have hA : A = (A 0 0) • (1 : Matrix (Fin 1) (Fin 1) K) := by
    ext i j; fin_cases i; fin_cases j; simp
  rw [hA, show (A 0 0) • (1 : Matrix (Fin 1) (Fin 1) K) =
    algebraMap K _ (A 0 0) from by simp [Algebra.algebraMap_eq_smul_one], φ.commutes]

theorem skolemNoether_one_inner
    (φ : Matrix (Fin 1) (Fin 1) K ≃ₐ[K] Matrix (Fin 1) (Fin 1) K) :
    IsInnerAut φ := by
  refine ⟨1, fun A => ?_⟩
  simp [skolemNoether_one φ A]

/-
  Summary:

  This file establishes the formal framework for the Skolem-Noether theorem
  in the context of matrix algebras Mₙ(K) over a field K:

  PROVED:
  - conjAlgEquiv: conjugation by invertible P as a K-algebra automorphism
  - IsInnerAut: formal definition of inner automorphisms
  - Inner automorphisms form a group (id, symm, trans closure)
  - The n=1 case: every automorphism of M₁(K) is the identity (hence inner)
  - Every automorphism preserves minpoly (from minpoly.algEquiv_eq)

  THEOREM (fully proved):
  - skolemNoether: every K-algebra automorphism of Mₙ(K) is inner
    (proved via elementary matrix units - no Artin-Wedderburn needed)
    All helper lemmas proved: 0 sorries, 0 axioms

  DERIVED (from skolemNoether):
  - exists_conjugating_matrix: extraction form of Skolem-Noether
  - surjection_units_to_aut: Aut_K(Mₙ(K)) = Inn(Mₙ(K))
  - automorphism_preserves_minpoly: minpoly invariance (also provable
    directly from minpoly.algEquiv_eq)

  PROVED (no axioms):
  - center_iff_scalar: Center(Mₙ(K)) = K·I
  - scalar_commutes: scalar matrices commute with everything
  - off_diagonal_vanish_of_center: central matrices have zero off-diagonal
  - diagonal_constant_of_center: central matrices have equal diagonal entries
  - conjAlgEquiv_eq_iff_center: two units give same conjugation iff their
    ratio is central
  - conjAlgEquiv_injective_mod_center: conjugation separates units modulo center
-/

/-
  Part VI: Matrix Unit Product Lemmas

  Helper lemmas for computing products with standard basis matrices
  (matrix units E_ij). These support the center characterization.
-/

section MatrixUnitProducts

/-- Right-multiplying by the matrix unit E_ij extracts column i of A and
    places it in column j. Uses Finset.sum_eq_single for clean computation. -/
theorem mul_eij_entry (A : Matrix n n K) (i j : n) (k l : n) :
    (A * Matrix.stdBasisMatrix i j (1 : K)) k l = if l = j then A k i else 0 := by
  simp only [Matrix.mul_apply]
  by_cases hlj : l = j
  · subst hlj; rw [if_pos rfl]
    rw [Finset.sum_eq_single i]
    · simp [Matrix.stdBasisMatrix, Matrix.of_apply]
    · intro m _ hm; simp [Matrix.stdBasisMatrix, Matrix.of_apply, Ne.symm hm]
    · intro h; exact absurd (Finset.mem_univ i) h
  · rw [if_neg hlj]
    apply Finset.sum_eq_zero
    intro m _; simp [Matrix.stdBasisMatrix, Matrix.of_apply, Ne.symm hlj]

/-- Left-multiplying by the matrix unit E_ij extracts row j of A and
    places it in row i. -/
theorem eij_mul_entry (A : Matrix n n K) (i j : n) (k l : n) :
    (Matrix.stdBasisMatrix i j (1 : K) * A) k l = if k = i then A j l else 0 := by
  simp only [Matrix.mul_apply]
  by_cases hki : k = i
  · subst hki; rw [if_pos rfl]
    rw [Finset.sum_eq_single j]
    · simp [Matrix.stdBasisMatrix, Matrix.of_apply]
    · intro m _ hm; simp [Matrix.stdBasisMatrix, Matrix.of_apply, Ne.symm hm]
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [if_neg hki]
    apply Finset.sum_eq_zero
    intro m _; simp [Matrix.stdBasisMatrix, Matrix.of_apply, Ne.symm hki]

end MatrixUnitProducts

/-
  Part VII: Center of Mₙ(K) = Scalar Matrices

  A matrix in the center of Mₙ(K) (commuting with all matrices) must be a
  scalar multiple of the identity. This is proved by testing commutativity
  against standard basis matrices E_ij:
  - E_ij for i ≠ j forces off-diagonal entries to vanish
  - E_ij for i ≠ j also forces all diagonal entries to be equal
-/

section Center

/-- A scalar matrix commutes with every matrix. -/
theorem scalar_commutes (c : K) (B : Matrix n n K) :
    c • (1 : Matrix n n K) * B = B * (c • (1 : Matrix n n K)) := by
  simp [smul_mul_assoc, mul_smul_comm]

/-- Off-diagonal entries of a central matrix are zero.
    Proof: test A against E_ji and examine the (i,i) entry.
    LHS: (A * E_ji)(i,i) = A(i,j) since column j of A goes to column i.
    RHS: (E_ji * A)(i,i) = 0 since i ≠ j means no contribution. -/
theorem off_diagonal_vanish_of_center (A : Matrix n n K)
    (hcomm : ∀ B : Matrix n n K, A * B = B * A)
    (i j : n) (hij : i ≠ j) : A i j = 0 := by
  have h := congr_fun (congr_fun (hcomm (Matrix.stdBasisMatrix j i (1 : K))) i) i
  rw [mul_eij_entry, eij_mul_entry] at h
  simp only [if_pos rfl] at h
  rwa [if_neg hij] at h

/-- Diagonal entries of a central matrix are all equal.
    Proof: test A against E_ij and examine the (i,j) entry.
    LHS: (A * E_ij)(i,j) = A(i,i) since column i of A goes to column j.
    RHS: (E_ij * A)(i,j) = A(j,j) since row j of A goes to row i. -/
theorem diagonal_constant_of_center [Nonempty n] (A : Matrix n n K)
    (hcomm : ∀ B : Matrix n n K, A * B = B * A)
    (i j : n) : A i i = A j j := by
  by_cases hij : i = j
  · rw [hij]
  · have h := congr_fun (congr_fun (hcomm (Matrix.stdBasisMatrix i j (1 : K))) i) j
    rw [mul_eij_entry, eij_mul_entry] at h
    simp only [if_pos rfl] at h
    exact h

/-- **Center of Mₙ(K) = K·I**: A matrix in Mₙ(K) commutes with all matrices
    if and only if it is a scalar multiple of the identity.
    This is a fundamental structural result about matrix algebras. -/
theorem center_iff_scalar [Nonempty n] (A : Matrix n n K) :
    (∀ B : Matrix n n K, A * B = B * A) ↔ ∃ c : K, A = c • (1 : Matrix n n K) := by
  constructor
  · intro hcomm
    obtain ⟨i₀⟩ := ‹Nonempty n›
    refine ⟨A i₀ i₀, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, eq_self_iff_true, if_true,
        mul_one]
      exact (diagonal_constant_of_center A hcomm i₀ i).symm
    · simp only [Matrix.smul_apply, Matrix.one_apply, if_neg hij, smul_zero]
      exact off_diagonal_vanish_of_center A hcomm i j hij
  · rintro ⟨c, rfl⟩
    exact scalar_commutes c

end Center

/-
  Part VIII: Conjugation Kernel and PGL Structure

  Two invertible matrices P, Q give the same conjugation automorphism
  conjAlgEquiv P = conjAlgEquiv Q if and only if QP⁻¹ is a scalar matrix.
  This determines the kernel of the conjugation homomorphism:

    1 → K* → GLₙ(K) → Aut_K(Mₙ(K)) → 1

  Combined with the Skolem-Noether theorem (surjectivity), this gives
  Aut_K(Mₙ(K)) ≅ GLₙ(K)/K* = PGLₙ(K).
-/

section PGLStructure

variable [Nonempty n]

/-- If conjAlgEquiv P = conjAlgEquiv Q, then QP⁻¹ commutes with all matrices. -/
theorem conjAlgEquiv_eq_implies_center (P Q : (Matrix n n K)ˣ)
    (h : conjAlgEquiv P = conjAlgEquiv Q) :
    ∀ A : Matrix n n K, (Q.val * P⁻¹.val) * A = A * (Q.val * P⁻¹.val) := by
  intro A
  have key : ∀ B : Matrix n n K, P⁻¹.val * B * P.val = Q⁻¹.val * B * Q.val := by
    intro B
    have := AlgEquiv.ext_iff.mp h B
    exact this
  -- From P⁻¹BP = Q⁻¹BQ for all B, multiply left by Q and right by P⁻¹
  -- Q(P⁻¹BP)P⁻¹ = Q(Q⁻¹BQ)P⁻¹
  -- (QP⁻¹)B(PP⁻¹) = (QQ⁻¹)B(QP⁻¹)
  -- (QP⁻¹)B = B(QP⁻¹)
  have step := key A
  -- step: P⁻¹AP = Q⁻¹AQ
  -- Multiply both sides on the left by Q and on the right by P⁻¹
  have lhs_calc : Q.val * (P⁻¹.val * A * P.val) * P⁻¹.val
      = (Q.val * P⁻¹.val) * A := by
    simp only [mul_assoc]
    rw [Units.mul_inv P, mul_one]
  have rhs_calc : Q.val * (Q⁻¹.val * A * Q.val) * P⁻¹.val
      = A * (Q.val * P⁻¹.val) := by
    simp only [mul_assoc]
    rw [← mul_assoc Q.val Q⁻¹.val, Units.mul_inv Q, one_mul]
  calc (Q.val * P⁻¹.val) * A
      = Q.val * (P⁻¹.val * A * P.val) * P⁻¹.val := lhs_calc.symm
    _ = Q.val * (Q⁻¹.val * A * Q.val) * P⁻¹.val := by rw [step]
    _ = A * (Q.val * P⁻¹.val) := rhs_calc

/-- Two units give the same conjugation automorphism if and only if their
    ratio QP⁻¹ is in the center of Mₙ(K) (i.e., is a scalar matrix). -/
theorem conjAlgEquiv_eq_iff_center (P Q : (Matrix n n K)ˣ) :
    conjAlgEquiv P = conjAlgEquiv Q ↔
    ∃ c : K, Q.val * P⁻¹.val = c • (1 : Matrix n n K) := by
  constructor
  · intro h
    exact (center_iff_scalar (Q.val * P⁻¹.val)).mp
      (conjAlgEquiv_eq_implies_center P Q h)
  · rintro ⟨c, hc⟩
    apply AlgEquiv.ext
    intro A
    -- Goal: conjAlgEquiv P A = conjAlgEquiv Q A (matrix equality)
    -- i.e., P⁻¹AP = Q⁻¹AQ
    -- From QP⁻¹ = cI, QP⁻¹ commutes with everything, so P⁻¹AP = Q⁻¹AQ
    have hcomm : (Q.val * P⁻¹.val) * A = A * (Q.val * P⁻¹.val) := by
      rw [hc]; exact scalar_commutes c A
    -- Suffices to show P⁻¹AP = Q⁻¹AQ
    -- Strategy: Q⁻¹AQ = Q⁻¹ · A · (QP⁻¹) · P (inserting P⁻¹P = 1)
    --         = Q⁻¹ · (QP⁻¹) · A · P (using commutativity)
    --         = (Q⁻¹Q) · P⁻¹ · A · P = P⁻¹AP
    suffices Q⁻¹.val * A * Q.val = P⁻¹.val * A * P.val by exact this.symm
    calc Q⁻¹.val * A * Q.val
        = Q⁻¹.val * A * (Q.val * P⁻¹.val * P.val) := by
          simp only [mul_assoc]; rw [Units.inv_mul P, mul_one]
      _ = Q⁻¹.val * (A * (Q.val * P⁻¹.val)) * P.val := by simp only [mul_assoc]
      _ = Q⁻¹.val * ((Q.val * P⁻¹.val) * A) * P.val := by rw [hcomm]
      _ = (Q⁻¹.val * Q.val) * (P⁻¹.val * A * P.val) := by simp only [mul_assoc]
      _ = P⁻¹.val * A * P.val := by rw [Units.inv_mul]; simp only [one_mul]

/-- The conjugation map is injective modulo the center: if conjAlgEquiv P
    sends every matrix to itself (i.e., P⁻¹AP = A for all A), then P is
    a scalar matrix. This is the kernel of the conjugation representation. -/
theorem conjAlgEquiv_eq_refl_iff (P : (Matrix n n K)ˣ) :
    conjAlgEquiv P = AlgEquiv.refl ↔
    ∃ c : K, P.val = c • (1 : Matrix n n K) := by
  constructor
  · intro h
    -- conjAlgEquiv P = id means P⁻¹AP = A for all A
    -- Multiply on left by P: P(P⁻¹AP) = PA, and LHS = AP
    -- Hence P is central, therefore scalar
    have hcomm : ∀ A : Matrix n n K, P.val * A = A * P.val := by
      intro A
      have key : P⁻¹.val * A * P.val = A := AlgEquiv.ext_iff.mp h A
      -- Left-multiply by P: P(P⁻¹AP) = PA
      have step := congr_arg (P.val * ·) key
      -- step: P * (P⁻¹AP) = P * A
      -- Simplify LHS: (PP⁻¹)(AP) = AP
      simp only [mul_assoc] at step
      rw [← mul_assoc P.val P⁻¹.val, Units.mul_inv, one_mul] at step
      -- step: A * P.val = P.val * A
      exact step.symm
    exact (center_iff_scalar P.val).mp hcomm
  · rintro ⟨c, hc⟩
    apply AlgEquiv.ext
    intro A
    -- Goal: conjAlgEquiv P A = AlgEquiv.refl A
    -- i.e., P⁻¹AP = A
    suffices P⁻¹.val * A * P.val = A by exact this
    -- P = cI commutes with A, so P⁻¹(AP) = P⁻¹(PA) = (P⁻¹P)A = A
    have hP_comm : P.val * A = A * P.val := by
      rw [hc]; exact scalar_commutes c A
    calc P⁻¹.val * A * P.val
        = P⁻¹.val * (A * P.val) := by rw [mul_assoc]
      _ = P⁻¹.val * (P.val * A) := by rw [hP_comm]
      _ = (P⁻¹.val * P.val) * A := by rw [mul_assoc]
      _ = 1 * A := by rw [Units.inv_mul]
      _ = A := one_mul A

end PGLStructure

end SkolemNoether
