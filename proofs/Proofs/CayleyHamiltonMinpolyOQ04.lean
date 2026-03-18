/-
  Nonderogatory Matrix Characterization via Cyclic Vectors
  (cayley-hamilton-minpoly-oq-04)

  Theorem: A matrix M ∈ M_n(K) is nonderogatory (μ_M = χ_M) if and only if
  it possesses a cyclic vector v such that {v, Mv, ..., M^{n-1}v} forms a
  basis of K^n.

  Main results:
  1. Forward direction (complete proof, 0 sorries):
     IsCyclicVector M v → IsNonderogatory M
  2. Bridge lemma (complete proof, 0 sorries):
     natDeg(minpoly) = natDeg(charpoly) → minpoly = charpoly
  3. Backward direction (axiomatized):
     IsNonderogatory M → ∃ v, IsCyclicVector M v
     (requires structure theorem for f.g. modules over PID)
  4. Full equivalence:
     IsNonderogatory M ↔ ∃ v, IsCyclicVector M v

  The cyclic vector condition is expressed as: no nonzero polynomial of
  degree < n annihilates v under M. This is equivalent to linear
  independence of the Krylov vectors {v, Mv, ..., M^{n-1}v}.

  Proof strategy for the forward direction:
  - minpoly(M) annihilates M, so (aeval M (minpoly K M)).mulVec v = 0
  - If deg(minpoly) < n, this gives a nonzero polynomial of degree < n
    annihilating v, contradicting the cyclic vector property
  - Therefore deg(minpoly) = n = deg(charpoly)
  - Since minpoly | charpoly and both are monic of the same degree, they
    must be equal

  References:
  - Horn & Johnson, "Matrix Analysis" §3.2.4
  - Hoffman & Kunze, "Linear Algebra" §7.2
  - Mathlib: LinearAlgebra.Matrix.Charpoly.Minpoly

  Extends:
  - MinpolyCharpoly.lean (basic divisibility and degree bounds)
  - CayleyHamiltonMinpolyOQ02.lean (similar matrices have same minpoly)
  - CayleyHamiltonOQ01.lean (annihilator ideal theory)
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

namespace Nonderogatory

open Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- PART I: Definitions
-- ============================================================

/-- A vector v is a **cyclic vector** for matrix M if no nonzero polynomial
    of degree less than n annihilates v under M.

    Equivalently, the Krylov vectors {v, Mv, M²v, ..., M^{n-1}v}
    are linearly independent (hence form a basis of K^n).

    This is the "annihilator" formulation, which directly captures the
    algebraic essence of the cyclic vector condition: the annihilator
    ideal of v as a K[X]-module (via M) intersects the low-degree
    polynomials only at zero. -/
def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

/-- The standard linear independence formulation of cyclic vector:
    the Krylov vectors {v, Mv, M²v, ..., M^{n-1}v} are linearly independent. -/
def IsCyclicVectorLI (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  LinearIndependent K (fun k : Fin n => (M ^ (k : ℕ)).mulVec v)

/-- A matrix is **nonderogatory** if its minimal polynomial equals
    its characteristic polynomial: μ_M = χ_M.

    Nonderogatory matrices have the simplest possible invariant factor
    decomposition: V ≅ K[X]/(χ_M) as a K[X]-module. The matrix is
    similar to the companion matrix of χ_M.

    Examples:
    - Companion matrices are nonderogatory
    - Diagonal matrices with distinct eigenvalues are nonderogatory
    - Scalar matrices cI (for n ≥ 2) are derogatory: μ = X-c, χ = (X-c)^n -/
def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- PART II: Bridge Lemma
-- ============================================================

/-- **Bridge Lemma**: If the minimal polynomial and characteristic polynomial
    of a matrix have the same degree, they are equal.

    Both are monic and one divides the other, so equal degree forces
    the cofactor to be a monic polynomial of degree 0 (hence 1). -/
theorem minpoly_eq_charpoly_of_natDegree_eq (M : Matrix (Fin n) (Fin n) K)
    (h : (minpoly K M).natDegree = M.charpoly.natDegree) :
    IsNonderogatory M := by
  unfold IsNonderogatory
  have hm := minpoly.monic (isIntegral M)
  have hc := charpoly_monic M
  obtain ⟨r, hr⟩ := minpoly_dvd_charpoly M
  -- r must be nonzero (otherwise charpoly = 0, contradicting monic)
  have hr_ne : r ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hr; exact hc.ne_zero hr
  -- Degree additivity: deg(charpoly) = deg(minpoly) + deg(r)
  have h_add : M.charpoly.natDegree = (minpoly K M).natDegree + r.natDegree := by
    rw [hr]; exact natDegree_mul hm.ne_zero hr_ne
  -- Therefore deg(r) = 0
  have hr_deg : r.natDegree = 0 := by omega
  -- r is monic: from hm.leadingCoeff_mul, (minpoly * r).leadingCoeff = r.leadingCoeff
  -- Since M.charpoly = minpoly * r and charpoly is monic, r.leadingCoeff = 1
  have hr_monic : r.Monic := by
    have h_lc : (minpoly K M * r).leadingCoeff = r.leadingCoeff := by
      simp [hm.leadingCoeff, one_mul]
    show r.leadingCoeff = 1
    calc r.leadingCoeff
        = (minpoly K M * r).leadingCoeff := h_lc.symm
      _ = M.charpoly.leadingCoeff := by rw [hr]
      _ = 1 := hc.leadingCoeff
  -- A monic polynomial of degree 0 must be 1
  have hr_one : r = 1 := by
    have h_eq : r = C (r.coeff 0) := eq_C_of_natDegree_eq_zero hr_deg
    have h_coeff : r.coeff 0 = 1 := by
      have := hr_monic
      simp only [Monic.def, leadingCoeff] at this
      rwa [hr_deg] at this
    rw [h_eq, h_coeff, map_one]
  -- Therefore minpoly = charpoly
  rw [hr, hr_one, mul_one]

-- ============================================================
-- PART III: Forward Direction - Cyclic Vector → Nonderogatory
-- ============================================================

/-- **Main Theorem (Forward Direction)**: If M has a cyclic vector, then
    M is nonderogatory (minpoly = charpoly).

    Proof: The minimal polynomial annihilates M, hence annihilates v via M.
    If deg(minpoly) < n, this gives a nonzero polynomial of degree < n
    annihilating v, contradicting the cyclic vector property.
    Therefore deg(minpoly) = n = deg(charpoly), and the bridge lemma
    gives minpoly = charpoly. -/
theorem cyclic_implies_nonderogatory (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (hv : IsCyclicVector M v) :
    IsNonderogatory M := by
  -- Suffices to show deg(minpoly) = deg(charpoly)
  apply minpoly_eq_charpoly_of_natDegree_eq
  -- We know deg(minpoly) ≤ deg(charpoly)
  have hle : (minpoly K M).natDegree ≤ M.charpoly.natDegree :=
    natDegree_le_of_dvd (minpoly_dvd_charpoly M) (charpoly_monic M).ne_zero
  -- Assume for contradiction they're not equal
  by_contra hne
  have hlt : (minpoly K M).natDegree < M.charpoly.natDegree := by omega
  -- deg(charpoly) = n
  rw [charpoly_natDegree_eq_dim M, Fintype.card_fin] at hlt
  -- So deg(minpoly) < n
  -- The minimal polynomial annihilates v via M
  have hann : (aeval M (minpoly K M)).mulVec v = 0 := by
    simp [minpoly.aeval K M]
  -- But minpoly is nonzero (it's monic)
  have hne_zero : minpoly K M ≠ 0 := (minpoly.monic (isIntegral M)).ne_zero
  -- By IsCyclicVector, any polynomial of degree < n annihilating v must be 0
  -- This gives minpoly = 0, contradicting monicity
  exact hne_zero (hv _ hlt hann)

-- ============================================================
-- PART IV: Backward Direction - Nonderogatory → Cyclic Vector
-- ============================================================

/-
  The backward direction requires substantially more infrastructure:

  Approach 1 (General fields):
    Use the structure theorem for finitely generated modules over a PID.
    V ≅ K[X]/(d₁) ⊕ ... ⊕ K[X]/(d_k) where d₁ | d₂ | ... | d_k.
    minpoly = d_k, charpoly = d₁ · ... · d_k.
    If minpoly = charpoly, then k = 1 (single cyclic summand).
    The generator of this cyclic module is the cyclic vector.

  Approach 2 (Algebraically closed fields):
    Use Jordan Normal Form. If minpoly = charpoly, each eigenvalue μ has
    maxGenEigenspaceIndex f μ = multiplicity of μ in charpoly = dim(genEigenspace μ).
    This means exactly one Jordan block per eigenvalue. Take a generator
    for each primary component and sum them.

  Approach 3 (Infinite fields):
    The set of vectors v with annihilator polynomial ≠ minpoly is a finite
    union of proper subspaces (one per proper divisor of minpoly). Over an
    infinite field, a finite union of proper subspaces cannot cover V.

  None of these are currently available as single Mathlib lemmas, though
  the building blocks exist (PID theory, Jordan-Chevalley decomposition).
-/

/-- **Backward Direction**: A nonderogatory matrix has a cyclic vector.
    This is axiomatized because the proof requires the structure theorem
    for finitely generated modules over a PID, which is substantial
    infrastructure to deploy in a single formalization.

    The result holds over ALL fields (including finite fields), which
    rules out simple "union of proper subspaces" arguments. -/
axiom nonderogatory_has_cyclic_vector (M : Matrix (Fin n) (Fin n) K)
    (h : IsNonderogatory M) : ∃ v, IsCyclicVector M v

-- ============================================================
-- PART V: Full Characterization
-- ============================================================

/-- **Nonderogatory Characterization Theorem**:
    A matrix is nonderogatory if and only if it has a cyclic vector.

    μ_M = χ_M ↔ ∃ v, IsCyclicVector M v

    The forward direction is proved; the backward direction is axiomatized. -/
theorem nonderogatory_iff_cyclic_vector (M : Matrix (Fin n) (Fin n) K) :
    IsNonderogatory M ↔ ∃ v, IsCyclicVector M v := by
  constructor
  · exact nonderogatory_has_cyclic_vector M
  · rintro ⟨v, hv⟩
    exact cyclic_implies_nonderogatory M v hv

-- ============================================================
-- PART VI: Corollaries
-- ============================================================

/-- A cyclic vector implies deg(minpoly) = n.
    This is the key degree equality that underlies nonderogatory. -/
theorem minpoly_natDegree_eq_dim_of_cyclic (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (hv : IsCyclicVector M v) :
    (minpoly K M).natDegree = Fintype.card (Fin n) := by
  have h := cyclic_implies_nonderogatory M v hv
  unfold IsNonderogatory at h
  rw [h, charpoly_natDegree_eq_dim]

/-- For a nonderogatory matrix, the algebra K[M] has dimension n over K.
    This means {I, M, M², ..., M^{n-1}} is a basis for K[M]. -/
theorem nonderogatory_algebra_dim (M : Matrix (Fin n) (Fin n) K)
    (h : IsNonderogatory M) :
    (minpoly K M).natDegree = Fintype.card (Fin n) := by
  unfold IsNonderogatory at h
  rw [h, charpoly_natDegree_eq_dim]

/-- The minimal polynomial of a nonderogatory matrix divides the
    characteristic polynomial (trivially, since they're equal). -/
theorem nonderogatory_minpoly_dvd_charpoly (M : Matrix (Fin n) (Fin n) K)
    (h : IsNonderogatory M) :
    minpoly K M ∣ M.charpoly := by
  unfold IsNonderogatory at h
  rw [h]

-- ============================================================
-- PART VII: Degree Characterization
-- ============================================================

/-- A matrix is nonderogatory iff deg(minpoly) = n. -/
theorem nonderogatory_iff_natDegree_eq (M : Matrix (Fin n) (Fin n) K) :
    IsNonderogatory M ↔ (minpoly K M).natDegree = Fintype.card (Fin n) := by
  constructor
  · intro h; exact nonderogatory_algebra_dim M h
  · intro h
    apply minpoly_eq_charpoly_of_natDegree_eq
    rw [h, charpoly_natDegree_eq_dim]

/-- A matrix is derogatory (NOT nonderogatory) iff deg(minpoly) < n. -/
theorem derogatory_iff_natDegree_lt (M : Matrix (Fin n) (Fin n) K)
    [Nontrivial (Matrix (Fin n) (Fin n) K)] :
    ¬ IsNonderogatory M ↔ (minpoly K M).natDegree < Fintype.card (Fin n) := by
  rw [nonderogatory_iff_natDegree_eq]
  constructor
  · intro h
    have hle : (minpoly K M).natDegree ≤ Fintype.card (Fin n) := by
      calc (minpoly K M).natDegree
          ≤ M.charpoly.natDegree :=
            natDegree_le_of_dvd (minpoly_dvd_charpoly M) (charpoly_monic M).ne_zero
        _ = Fintype.card (Fin n) := charpoly_natDegree_eq_dim M
    omega
  · intro h; omega

-- ============================================================
-- Summary
-- ============================================================

/-
  ## Summary: Nonderogatory Matrix Characterization

  For M ∈ M_n(K) over a field K:

  **Definitions**:
  - IsCyclicVector M v: No nonzero polynomial of degree < n annihilates v via M
  - IsNonderogatory M: minpoly K M = M.charpoly

  **Main Results**:
  - cyclic_implies_nonderogatory: IsCyclicVector M v → IsNonderogatory M (proved)
  - nonderogatory_has_cyclic_vector: IsNonderogatory M → ∃ v, IsCyclicVector M v (axiom)
  - nonderogatory_iff_cyclic_vector: IsNonderogatory M ↔ ∃ v, IsCyclicVector M v

  **Degree Characterization**:
  - nonderogatory_iff_natDegree_eq: IsNonderogatory M ↔ deg(minpoly) = n
  - derogatory_iff_natDegree_lt: ¬IsNonderogatory M ↔ deg(minpoly) < n

  **Bridge Lemma**:
  - minpoly_eq_charpoly_of_natDegree_eq: Same degree + monic + divisibility → equal

  **Proved** (0 sorries):
  - Forward direction of the characterization
  - Bridge lemma
  - All corollaries

  **Axiomatized** (1 axiom):
  - nonderogatory_has_cyclic_vector (requires PID module structure theorem)
-/

end Nonderogatory
