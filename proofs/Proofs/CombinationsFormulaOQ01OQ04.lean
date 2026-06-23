import Proofs.BallotProblemOQ03OQ02

/-
# The Lindström-Gessel-Viennot Lemma

## What This Proves

The Lindström-Gessel-Viennot (LGV) Lemma connects determinants of binomial
coefficient matrices to counts of non-intersecting lattice path tuples.

**Main Theorem**: Let a₁ < a₂ < ... < aᵣ and b₁ < b₂ < ... < bᵣ be strictly
increasing y-coordinates on the start column (x=0) and end column (x=m). Define
the r×r matrix M where Mᵢⱼ = C(m + bⱼ - aᵢ, m) counts lattice paths using m East
steps and (bⱼ - aᵢ) North steps. Then:

  det(M) = #{r-tuples of pairwise non-intersecting paths,
             path i connecting y=aᵢ to y=bᵢ}

**Key consequences**:
- Determinants of such binomial matrices are always non-negative integers
- The formula unifies classical identities: Catalan numbers, Schur polynomials,
  plane partition formulas, and ballot problem non-crossing counts

## Proof Infrastructure

This file builds on `BallotProblemOQ03OQ02.lean`, which contains:
- `LGVConfig r`: the r×r source/target configuration structure
- `pathMatrix`: the binomial coefficient matrix M_{ij} = C(m + b_j - a_i, m)
- `niTupleCount`: the count of non-intersecting path r-tuples
- `lgv_lemma_rxr`: the core theorem `niTupleCount = det(pathMatrix)`
- The full Gessel-Viennot sign-reversing involution proof

## Status: 0 axioms, 0 sorries
-/

namespace CombinationsFormulaOQ01OQ04

open LGV

-- ============================================================
-- Part I: The Core LGV Theorem
-- ============================================================

/-- **The Lindström-Gessel-Viennot (LGV) Lemma**:
    The count of non-intersecting lattice path r-tuples equals the
    determinant of the r×r binomial coefficient matrix.

    The well-formedness condition requires max(sources) ≤ min(targets),
    ensuring paths can potentially avoid crossing. -/
theorem lgv_determinant_formula {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed) :
    (LGV.niTupleCount cfg : ℤ) = (LGV.pathMatrix cfg).det :=
  LGV.lgv_lemma_rxr cfg hwf

/-- **Non-negativity of binomial determinants**:
    For well-formed source/target configurations, det(M) ≥ 0,
    since it counts non-intersecting path tuples (a natural number). -/
theorem lgv_det_nonneg {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed) :
    0 ≤ (LGV.pathMatrix cfg).det :=
  LGV.pathMatrix_det_nonneg cfg hwf

-- ============================================================
-- Part II: The 1×1 Case
-- ============================================================

/-- **1×1 LGV configuration**: a single path from y=a to y=b using m East steps. -/
def lgvConfig1 (m a b : ℕ) (hab : a ≤ b) : LGVConfig 1 where
  m := m
  sources := fun _ => a
  targets := fun _ => b
  sources_strictMono := by intro i j h; fin_cases i <;> fin_cases j <;> omega
  targets_strictMono := by intro i j h; fin_cases i <;> fin_cases j <;> omega
  source_le_target := fun _ => hab

theorem lgvConfig1_wellFormed (m a b : ℕ) (hab : a ≤ b) :
    (lgvConfig1 m a b hab).wellFormed :=
  fun _ _ => hab

/-- **1×1 LGV**: The 1×1 determinant is the single path count C(m + b - a, m).
    Every single path is trivially non-intersecting with itself. -/
theorem lgv_one_by_one (m a b : ℕ) (hab : a ≤ b) :
    (LGV.pathMatrix (lgvConfig1 m a b hab)).det = Nat.choose (m + (b - a)) m := by
  simp [LGV.pathMatrix, Matrix.det_fin_one, Matrix.of_apply, lgvConfig1]

-- ============================================================
-- Part III: The Standard 2×2 Configuration
-- ============================================================

/-- **2×2 LGV configuration**: sources [a, a+1], targets [b, b+1].
    The path matrix is:
      M = [[C(m+b-a, m),   C(m+b+1-a, m)  ],
           [C(m+b-a-1, m), C(m+b-a, m)    ]]
    and det(M) = C(m+b-a, m)² - C(m+b+1-a, m)·C(m+b-a-1, m). -/
def lgvConfig2 (m a b : ℕ) (hab : a ≤ b) : LGVConfig 2 where
  m := m
  sources := ![a, a + 1]
  targets := ![b, b + 1]
  sources_strictMono := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> omega
  targets_strictMono := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> omega
  source_le_target := by
    intro i
    fin_cases i <;>
      simp_all [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> omega

/-- The 2×2 configuration with a+1 ≤ b is well-formed:
    the maximum source (a+1) does not exceed the minimum target (b). -/
theorem lgvConfig2_wellFormed (m a b : ℕ) (hab : a + 1 ≤ b) :
    (lgvConfig2 m a b (by omega)).wellFormed := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp_all [lgvConfig2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] <;> omega

-- ============================================================
-- Part IV: Concrete 2×2 Example (m=2, a=0, b=2)
-- ============================================================

/-- **Example 1**: m=2, sources=[0,1], targets=[2,3].
    Path matrix: [[C(4,2), C(5,2)], [C(3,2), C(4,2)]] = [[6,10],[3,6]].
    det = 6·6 - 10·3 = 36 - 30 = 6. -/
theorem lgv_2x2_det_ex1 :
    (LGV.pathMatrix (lgvConfig2 2 0 2 (by norm_num))).det = 6 := by
  simp only [LGV.pathMatrix, Matrix.det_fin_two, Matrix.of_apply, lgvConfig2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  native_decide

/-- The count of non-intersecting path pairs equals 6 for example 1
    (derived from the determinant via the LGV theorem). -/
theorem lgv_2x2_ni_count_ex1 :
    LGV.niTupleCount (lgvConfig2 2 0 2 (by norm_num)) = 6 := by
  have h := lgv_determinant_formula (lgvConfig2 2 0 2 (by norm_num))
              (lgvConfig2_wellFormed 2 0 2 (by norm_num))
  rw [lgv_2x2_det_ex1] at h
  exact_mod_cast h.symm

-- ============================================================
-- Part V: A Larger Example (m=3, a=0, b=3)
-- ============================================================

/-- **Example 2**: m=3, sources=[0,1], targets=[3,4].
    Path matrix: [[C(6,3), C(7,3)], [C(5,3), C(6,3)]] = [[20,35],[10,20]].
    det = 20·20 - 35·10 = 400 - 350 = 50. -/
theorem lgv_2x2_det_ex2 :
    (LGV.pathMatrix (lgvConfig2 3 0 3 (by norm_num))).det = 50 := by
  simp only [LGV.pathMatrix, Matrix.det_fin_two, Matrix.of_apply, lgvConfig2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  native_decide

theorem lgv_2x2_ni_count_ex2 :
    LGV.niTupleCount (lgvConfig2 3 0 3 (by norm_num)) = 50 := by
  have h := lgv_determinant_formula (lgvConfig2 3 0 3 (by norm_num))
              (lgvConfig2_wellFormed 3 0 3 (by norm_num))
  rw [lgv_2x2_det_ex2] at h
  exact_mod_cast h.symm

-- ============================================================
-- Part VI: Non-Negativity and Well-Formedness
-- ============================================================

/-- Non-negativity of the 2×2 determinant for all valid configurations. -/
theorem lgv_2x2_det_nonneg (m a b : ℕ) (hab : a + 1 ≤ b) :
    0 ≤ (LGV.pathMatrix (lgvConfig2 m a b (by omega))).det :=
  lgv_det_nonneg _ (lgvConfig2_wellFormed m a b hab)

/-- When sources and targets share endpoints (b=0, so sources=[0,1], targets=[0,1]),
    the well-formedness condition fails: source 1 = 1 > 0 = target 0. -/
theorem lgv_2x2_not_wellFormed_when_b_zero :
    ¬ (lgvConfig2 2 0 0 (by norm_num)).wellFormed := by
  intro h
  have h10 := h 1 0
  simp only [lgvConfig2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h10
  omega

-- ============================================================
-- Part VII: The Determinant Is Always a Natural Number
-- ============================================================

/-- For well-formed LGV configurations, the determinant of the binomial
    coefficient matrix is always a non-negative integer — it equals a
    count of combinatorial objects. -/
theorem lgv_det_is_natural {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed) :
    ∃ n : ℕ, (LGV.pathMatrix cfg).det = n :=
  ⟨LGV.niTupleCount cfg, (LGV.lgv_lemma_rxr cfg hwf).symm⟩

end CombinationsFormulaOQ01OQ04
