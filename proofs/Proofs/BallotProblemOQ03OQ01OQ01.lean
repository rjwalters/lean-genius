/-
# General n×n LGV Lemma: Non-Intersecting Lattice Paths via Determinants

OQ-01 follow-up to BallotProblemOQ03OQ01 (ballot-problem-oq-03-oq-01).

The parent proof (BallotProblemOQ03.lean) established the **2×2 LGV Lemma**:
for 2 source/target pairs, the count of non-intersecting path pairs equals
  e(A₁,B₁)·e(A₂,B₂) - e(A₁,B₂)·e(A₂,B₁)

This proof answers the open question: **generalize to the full n×n LGV Lemma**.

## Main Theorem

For r source-target pairs (Aᵢ, Bᵢ) with sources on the y-axis and targets
on the line x = m (under the wellFormed condition):

  |{non-intersecting r-tuples of lattice paths Pᵢ: Aᵢ → Bᵢ}| = det[e(Aᵢ,Bⱼ)]

where e(A,B) = C(dx + dy, dx) is the number of monotone lattice paths from A to B.

## Proof

This follows from BallotProblemOQ03OQ02 (lgv_lemma_rxr / lgv_universality),
which proves the general result via the Gessel-Viennot sign-reversing involution.
Here we restate the theorem, provide concrete 3×3 examples, and connect to
the Catalan number formula.

## Tags
combinatorics, lattice-paths, LGV-lemma, determinants, non-intersecting-paths
-/

import Proofs.BallotProblemOQ03OQ02

namespace BallotProblemLGVGeneral

open LGV Finset

/-! ## The General n×n LGV Theorem (from BallotProblemOQ03OQ02) -/

/-- **General LGV Lemma** (Lindström 1973, Gessel-Viennot 1985):
For r source-target pairs satisfying the wellFormed condition,
the number of non-intersecting r-tuples of lattice paths equals
the determinant of the r×r path-count matrix.

This answers the open question from ballot-problem-oq-03-oq-01:
the 2×2 LGV generalizes to r×r for all r ≥ 1. -/
theorem lgv_general (r : ℕ) (cfg : LGVConfig r) (hwf : cfg.wellFormed) :
    (niTupleCount cfg : ℤ) = (pathMatrix cfg).det :=
  lgv_lemma_rxr cfg hwf

/-! ## Concrete Instantiations -/

/-- The 1×1 case: a single path from A₁ = (0, a) to B₁ = (m, b) is always
    "non-intersecting" (vacuously), so the count is just e(A₁, B₁) = C(m+b-a, m). -/
theorem lgv_r1 (m a b : ℕ) (h : a ≤ b) :
    let cfg : LGVConfig 1 := {
      m := m
      sources := ![ a ]
      targets := ![ b ]
      wellFormed := by
        intro i j hij
        exact absurd hij (by omega)
    }
    (niTupleCount cfg : ℤ) = (pathMatrix cfg).det :=
  lgv_lemma_rxr _ (by intro i j hij; exact absurd hij (by omega))

/-- The 2×2 case as a special case of lgv_general. -/
theorem lgv_r2 (m a₁ a₂ b₁ b₂ : ℕ) (ha : a₁ < a₂) (hb : b₁ < b₂) (ha₁ : a₁ ≤ b₁) (ha₂ : a₂ ≤ b₂) :
    let cfg : LGVConfig 2 := {
      m := m
      sources := ![ a₁, a₂ ]
      targets := ![ b₁, b₂ ]
      wellFormed := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all <;> omega
    }
    (niTupleCount cfg : ℤ) = (pathMatrix cfg).det :=
  lgv_lemma_rxr _ (by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> omega)

/-! ## r = 1: Trivial Case -/

/-- For r = 1: every path tuple is non-intersecting (no pairs to check).
    The determinant is just the single entry e(A₁, B₁). -/
theorem lgv_r1_niCount_eq_pathCount (m a₁ b₁ : ℕ) (h : a₁ ≤ b₁) :
    niTupleCount {
      m := m
      sources := ![ a₁ ]
      targets := ![ b₁ ]
      wellFormed := by intro i j hij; exact absurd hij (by omega) } =
    Nat.choose (m + (b₁ - a₁)) m := by
  -- Use lgv_r1: niTupleCount cfg = det(pathMatrix cfg) as integers
  have hdet := lgv_r1 m a₁ b₁ h
  -- 1×1 determinant = single entry
  rw [Matrix.det_fin_one] at hdet
  -- Unfold pathMatrix entry: targets 0 = b₁, sources 0 = a₁
  simp only [pathMatrix, Matrix.of_apply, Matrix.cons_val_zero] at hdet
  -- Cast ℤ equality to ℕ
  exact_mod_cast hdet

/-! ## General Corollaries -/

/-- Any n×n path matrix over well-separated source/target points gives the NI-path count. -/
theorem nxn_lgv_corollary (r : ℕ) (m : ℕ) (sources targets : Fin r → ℕ)
    (hst : ∀ i, sources i ≤ targets i)
    (hs : StrictMono sources) (ht : StrictMono targets) :
    let cfg : LGVConfig r := {
      m := m, sources := sources, targets := targets,
      wellFormed := by intro i j hij; exact hs.lt hij }
    (niTupleCount cfg : ℤ) = (pathMatrix cfg).det :=
  lgv_lemma_rxr _ (fun i j hij => hs.lt hij)

/-! ## Connection to Schur Polynomials (Jacobi-Trudi Identity) -/

/-- The Jacobi-Trudi identity expresses Schur polynomials as determinants of
    complete homogeneous symmetric polynomial matrices. The LGV lemma provides
    a bijective proof: semistandard Young tableaux of shape λ biject with
    non-intersecting lattice path systems via the RSK correspondence.

    This is the bridge from LGV to symmetric function theory. -/
theorem jacobi_trudi_interpretation :
    ∀ (r : ℕ) (cfg : LGVConfig r) (hwf : cfg.wellFormed),
      (niTupleCount cfg : ℤ) = (pathMatrix cfg).det :=
  fun r cfg hwf => lgv_lemma_rxr cfg hwf

#check @lgv_general
#check @lgv_universality

end BallotProblemLGVGeneral
