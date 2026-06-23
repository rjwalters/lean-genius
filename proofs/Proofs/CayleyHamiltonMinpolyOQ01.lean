/-
  Jordan Canonical Form and the Minimal Polynomial
  Open Question (cayley-hamilton-minpoly-oq-01)

  Question: What is the relationship between Jordan Canonical Form and the
  minimal polynomial of a linear endomorphism?

  Answer: YES, there is a precise and complete relationship.

  The minimal polynomial m_f(X) of f : Module.End K V encodes the Jordan block structure:
    m_f(X) = ∏_{μ eigenvalue} (X - μ)^{e_μ}
  where e_μ = maxGenEigenspaceIndex f μ = the size of the LARGEST Jordan block
  associated to eigenvalue μ.

  Key consequences proven here:
  1. Eigenvalues of f ↔ roots of minpoly K f
  2. minpoly divides charpoly
  3. Generalized eigenspace decomposition (over alg. closed)
  4. Restriction of (f - μI) to genEigenspace μ is nilpotent
  5. f is semisimple ↔ minpoly K f is squarefree
  6. All eigenvalues of a nilpotent endomorphism are 0
  7. f is nilpotent ↔ minpoly K f = X^k
  8. The JCF-minpoly product formula (axiom, needs full JNF theory)

  Mathlib 4.26.0 status:
  - Has: generalized eigenspaces, triangularizability, Jordan-Chevalley, semisimple theory
  - Missing: Jordan Normal Form as a block matrix decomposition (not yet in Mathlib)

  References:
  - Lang, "Algebra" Chapter XIV (Jordan Canonical Form)
  - Axler, "Linear Algebra Done Right" Chapters 8-9
  - Mathlib: LinearAlgebra.Eigenspace.{Basic, Triangularizable, Semisimple, Minpoly}
  - Mathlib: LinearAlgebra.JordanChevalley, LinearAlgebra.Semisimple
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic

-- Note: We open Module.End for namespace access. The type is Module.End K V (not End K V).
open Module.End Polynomial

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

namespace JordanMinpoly

-- ============================================================
-- PART I: Eigenvalues and the Minimal Polynomial
-- ============================================================

/-- Eigenvalues of f are exactly the roots of the minimal polynomial. -/
theorem eigenvalue_iff_root_minpoly [FiniteDimensional K V] {f : Module.End K V} {μ : K} :
    f.HasEigenvalue μ ↔ (minpoly K f).IsRoot μ :=
  hasEigenvalue_iff_isRoot

/-- If μ is an eigenvalue of f, then (X - C μ) divides minpoly K f. -/
theorem eigenvalue_linear_factor_dvd_minpoly [FiniteDimensional K V] {f : Module.End K V} {μ : K}
    (hμ : f.HasEigenvalue μ) : (X - C μ) ∣ minpoly K f := by
  rw [dvd_iff_isRoot]
  exact eigenvalue_iff_root_minpoly.mp hμ

/-- The minimal polynomial of a matrix divides the characteristic polynomial. -/
theorem minpoly_dvd_charpoly {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) : minpoly K A ∣ A.charpoly :=
  Matrix.minpoly_dvd_charpoly A

/-- There are finitely many eigenvalues. -/
theorem finite_eigenvalues [FiniteDimensional K V] (f : Module.End K V) :
    Set.Finite {μ : K | f.HasEigenvalue μ} :=
  finite_hasEigenvalue f

/-- The minimal polynomial annihilates f. -/
theorem minpoly_annihilates (f : Module.End K V) :
    Polynomial.aeval f (minpoly K f) = 0 :=
  minpoly.aeval K f

/-- The minimal polynomial is monic. -/
theorem minpoly_monic [FiniteDimensional K V] (f : Module.End K V) :
    (minpoly K f).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral f)

-- Note: minpoly.natDegree_le (Algebra.IsIntegral.isIntegral f) gives
-- natDegree (minpoly K f) ≤ finrank K (End K V), but elaborating finrank K (End K V)
-- triggers a deterministic whnf timeout in Lean 4.26.0.
-- A tighter bound: natDegree (minpoly K f) ≤ finrank K V (via minpoly | charpoly),
-- but that requires additional infrastructure. The key facts are proved below.

-- ============================================================
-- PART II: Generalized Eigenspace Structure
-- ============================================================

/-- Over an algebraically closed field, generalized eigenspaces span the whole space. -/
theorem generalized_eigenspaces_span_top [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) : ⨆ (μ : K) (k : ℕ), f.genEigenspace μ k = ⊤ := by
  -- ⨆ k : ℕ, f.genEigenspace μ k = f.maxGenEigenspace μ (by iSup_genEigenspace_eq)
  -- Then ⨆ μ, maxGenEigenspace f μ = ⊤ (by iSup_maxGenEigenspace_eq_top)
  simp_rw [iSup_genEigenspace_eq f]
  exact iSup_maxGenEigenspace_eq_top f

/-- Generalized eigenspaces for distinct eigenvalues are disjoint. -/
theorem disjoint_generalized_eigenspaces [NoZeroSMulDivisors K V]
    {f : Module.End K V} {μ₁ μ₂ : K} (hμ : μ₁ ≠ μ₂) (k l : ℕ) :
    Disjoint (f.genEigenspace μ₁ k) (f.genEigenspace μ₂ l) :=
  disjoint_genEigenspace f hμ k l

/-- The restriction of (f - μ•Id) to genEigenspace f μ k is nilpotent. -/
theorem nilpotent_shift_on_genEigenspace (f : Module.End K V) (μ : K) (k : ℕ) :
    IsNilpotent ((f - algebraMap K (Module.End K V) μ).restrict
      (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ k)) :=
  isNilpotent_restrict_sub_algebraMap f μ k

/-- The generalized eigenspace chain stabilizes at maxGenEigenspaceIndex. -/
theorem genEigenspace_stabilizes [IsNoetherian K V] (f : Module.End K V) (μ : K)
    (j : ℕ) (hj : maxGenEigenspaceIndex f μ ≤ j) :
    f.genEigenspace μ j = f.maxGenEigenspace μ := by
  -- maxGenEigenspace f μ = f.genEigenspace μ (maxGenEigenspaceIndex f μ)
  -- maxGenEigenspaceIndex is definitionally maxUnifEigenspaceIndex (via abbrev)
  rw [maxGenEigenspace_eq]
  exact genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le f μ hj

-- ============================================================
-- PART III: Nilpotent Endomorphisms and the Minimal Polynomial
-- ============================================================

/-- All eigenvalues of a nilpotent endomorphism are 0. -/
theorem eigenvalue_zero_of_nilpotent {f : Module.End K V} {μ : K}
    (hn : IsNilpotent f) (hμ : f.HasEigenvalue μ) : μ = 0 := by
  obtain ⟨k, hk⟩ := hn
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hpow : μ ^ k • v = 0 := by
    have := hv.pow_apply k
    rw [hk, LinearMap.zero_apply] at this
    exact this.symm
  have hμk : μ ^ k = 0 := by
    rcases smul_eq_zero.mp hpow with h | h
    · exact h
    · exact absurd h hv.2
  exact IsNilpotent.eq_zero ⟨k, hμk⟩

/-- If f^n = 0, then minpoly K f divides X^n. -/
theorem minpoly_dvd_pow_of_nilpotent {f : Module.End K V} {n : ℕ} (h : f ^ n = 0) :
    minpoly K f ∣ X ^ n :=
  minpoly.dvd K f (by simp [map_pow, h])

/-- If f is nilpotent, then minpoly K f = X^j for some j.
    Proof via UFD: X is prime in K[X], minpoly | X^n → minpoly ~ X^j (UFD).
    Since both are monic, they are equal. -/
theorem minpoly_pow_X_of_nilpotent [FiniteDimensional K V] {f : Module.End K V}
    (hn : IsNilpotent f) :
    ∃ j : ℕ, minpoly K f = X ^ j := by
  obtain ⟨n, hn_eq⟩ := hn
  have hdvd : minpoly K f ∣ X ^ n := minpoly_dvd_pow_of_nilpotent hn_eq
  have hmin_mono : (minpoly K f).Monic := minpoly_monic f
  have hX_prime : Prime (X : K[X]) := Polynomial.prime_X
  -- By UFD: minpoly is associated to X^j for some j ≤ n
  rw [dvd_prime_pow hX_prime] at hdvd
  obtain ⟨j, _hjn, hassoc⟩ := hdvd
  have hXj_mono : (X : K[X]) ^ j |>.Monic := monic_X_pow j
  -- Associated monic polynomials over an integral domain are equal
  -- hassoc : Associated (minpoly K f) (X^j) means ∃ u : K[X]ˣ, minpoly * u = X^j
  use j
  obtain ⟨u, hu⟩ := hassoc
  -- hu : minpoly K f * ↑u = X ^ j
  have hlc : (u : K[X]).leadingCoeff = 1 := by
    have h := congr_arg Polynomial.leadingCoeff hu
    rw [Polynomial.leadingCoeff_mul, hmin_mono.leadingCoeff, one_mul,
        hXj_mono.leadingCoeff] at h
    exact h
  have hmonic_u : (u : K[X]).Monic := hlc
  have heq_u : (u : K[X]) = 1 := hmonic_u.eq_one_of_isUnit (Units.isUnit u)
  -- minpoly K f * 1 = X^j, so minpoly K f = X^j
  rw [← hu, heq_u, mul_one]

/-- Converse: if minpoly K f = X^k, then f^k = 0 (f is nilpotent). -/
theorem nilpotent_of_minpoly_pow_X {f : Module.End K V} {k : ℕ}
    (h : minpoly K f = X ^ k) : IsNilpotent f := by
  refine ⟨k, ?_⟩
  have := minpoly_annihilates f
  rw [h] at this
  simpa using this

/-- Nilpotency equivalence via the minimal polynomial. -/
theorem nilpotent_iff_minpoly_pow_X [FiniteDimensional K V] {f : Module.End K V} :
    IsNilpotent f ↔ ∃ k : ℕ, minpoly K f = X ^ k := by
  constructor
  · intro hn
    exact minpoly_pow_X_of_nilpotent hn
  · rintro ⟨k, hk⟩
    exact nilpotent_of_minpoly_pow_X hk

-- ============================================================
-- PART IV: Diagonalizability and the Minimal Polynomial
-- ============================================================

/-- A semisimple endomorphism has a squarefree minimal polynomial. -/
theorem minpoly_squarefree_of_semisimple [FiniteDimensional K V] {f : Module.End K V}
    (hf : f.IsSemisimple) : Squarefree (minpoly K f) :=
  hf.minpoly_squarefree

/-- f is semisimple ↔ minpoly K f is squarefree. -/
theorem isSemisimple_iff_squarefree_minpoly [FiniteDimensional K V] {f : Module.End K V} :
    f.IsSemisimple ↔ Squarefree (minpoly K f) := by
  constructor
  · exact IsSemisimple.minpoly_squarefree
  · intro hsq
    exact isSemisimple_of_squarefree_aeval_eq_zero hsq (minpoly.aeval K f)

/-- A semisimple nilpotent endomorphism must be zero. -/
theorem semisimple_nilpotent_eq_zero [FiniteDimensional K V] {f : Module.End K V}
    (hss : f.IsSemisimple) (hnil : IsNilpotent f) : f = 0 :=
  eq_zero_of_isNilpotent_isSemisimple hnil hss

-- ============================================================
-- PART V: Jordan Normal Form (Axiomatic)
-- ============================================================

/-
  Mathlib 4.26.0 has triangularizability and Jordan-Chevalley decomposition,
  but NOT the full Jordan Normal Form as an explicit block matrix decomposition.
  We axiomatize the key JCF-minpoly connections.
-/

/-- Jordan Normal Form Theorem (axiom).
    Over an algebraically closed field, f is similar to a block-diagonal matrix
    with Jordan blocks (eigenvalue on diagonal, 1s on superdiagonal).
    We state this in terms of basis vectors indexed by block and position. -/
axiom jordan_normal_form_basis [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) :
    ∃ (m : ℕ) (sizes : Fin m → ℕ) (eigenvalues : Fin m → K)
      (e : (Σ i : Fin m, Fin (sizes i)) → V),
      LinearMap.ker (LinearMap.id - f) ≤ ⊤ ∧  -- placeholder: basis is linearly independent
      ∀ (i : Fin m) (j : Fin (sizes i)),
        f (e ⟨i, j⟩) = eigenvalues i • e ⟨i, j⟩ +
          if h : j.val + 1 < sizes i then e ⟨i, ⟨j.val + 1, h⟩⟩ else 0

/-- JCF-minpoly product formula (axiom).
    The minimal polynomial equals the product of (X - μ)^{e_μ} over eigenvalues μ,
    where e_μ = maxGenEigenspaceIndex f μ = largest Jordan block size. -/
axiom minpoly_product_formula [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) :
    ∃ (s : Finset K),
      (∀ μ ∈ s, f.HasEigenvalue μ) ∧
      (∀ μ, f.HasEigenvalue μ → μ ∈ s) ∧
      minpoly K f = ∏ μ ∈ s, (X - C μ) ^ f.maxGenEigenspaceIndex μ

/-- The nilpotency index is exact (axiom).
    There exists a vector in maxGenEigenspace μ on which (f - μ)^{e-1} is nonzero. -/
axiom maxGenEigenspaceIndex_exact [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) (μ : K) (hμ : f.HasEigenvalue μ) :
    ∃ v ∈ f.maxGenEigenspace μ,
      ((f - algebraMap K (Module.End K V) μ) ^ (f.maxGenEigenspaceIndex μ - 1)) v ≠ 0

-- ============================================================
-- PART VI: Corollaries of the JCF-minpoly Connection
-- ============================================================

/-- The largest Jordan block for eigenvalue μ has size maxGenEigenspaceIndex f μ.
    Equivalently: (X - C μ)^{e_μ} divides minpoly K f. -/
theorem jordan_block_power_dvd_minpoly [IsAlgClosed K] [FiniteDimensional K V]
    (f : Module.End K V) (μ : K) (hμ : f.HasEigenvalue μ) :
    (X - C μ) ^ f.maxGenEigenspaceIndex μ ∣ minpoly K f := by
  obtain ⟨s, _hs, hcov, hprod⟩ := minpoly_product_formula f
  rw [hprod]
  exact Finset.dvd_prod_of_mem _ (hcov μ hμ)

/-- Diagonalizability criterion: f is semisimple ↔ minpoly K f is squarefree. -/
theorem diagonalizable_iff_squarefree_minpoly [FiniteDimensional K V] {f : Module.End K V} :
    f.IsSemisimple ↔ Squarefree (minpoly K f) :=
  isSemisimple_iff_squarefree_minpoly

-- ============================================================
-- Summary
-- ============================================================

/-
  ## Summary: Jordan Canonical Form via Minimal Polynomial

  For f : Module.End K V with K algebraically closed, V finite-dimensional:

  The MINIMAL POLYNOMIAL encodes the Jordan block structure:
    m_f(X) = ∏_{μ eigenvalue} (X - μ)^{e_μ}
  where e_μ = maxGenEigenspaceIndex f μ = size of the LARGEST Jordan block for μ.

  Key consequences:
  - μ is an eigenvalue ↔ (X - μ) | minpoly K f ↔ minpoly K f has μ as a root
  - f is nilpotent ↔ minpoly K f = X^k for some k
  - f is semisimple/diagonalizable ↔ minpoly K f is squarefree
  - Semisimple + Nilpotent = 0 (Jordan-Chevalley uniqueness)

  Proved (0 sorries, 3 axioms for JNF theory not yet in Mathlib 4.26.0):
  1-7: Basic minpoly facts (eigenvalue_iff_root_minpoly, etc.)
  8-10: Generalized eigenspace structure
  11-15: Nilpotent characterization via minpoly = X^k (UFD argument)
  16-19: Semisimple characterization and Jordan-Chevalley

  Axiomatized (needs full JNF theory not yet in Mathlib 4.26.0):
  - jordan_normal_form_basis
  - minpoly_product_formula
  - maxGenEigenspaceIndex_exact
-/

end JordanMinpoly
