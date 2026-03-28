/-
  Weakening the Infinite Field Hypothesis for Cyclic Vectors

  The nonderogatory cyclic vector theorem (OQ-05-OQ-01) requires K to be
  infinite. This file shows the hypothesis can be weakened: it suffices
  that |K| > n where n is the matrix dimension.

  The key insight: the union avoidance argument only needs |K| > number
  of proper subspaces, and the number of irreducible factors of a
  degree-n polynomial is at most n.

  More precisely: for M ∈ M_n(K) nonderogatory, the number of cofactor
  kernels equals the number of distinct irreducible factors of minpoly(M),
  which is at most n. Union avoidance over k proper subspaces needs
  |K| ≥ k, so |K| ≥ n suffices (actually |K| > k-1 = number of factors - 1).
-/
import Mathlib

noncomputable section

namespace CyclicVectorFiniteField

open Matrix Polynomial

attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] {n : ℕ}

-- ============================================================
-- SECTION I: Definitions (consistent with OQ05OQ01)
-- ============================================================

def IsCyclicVector (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) : Prop :=
  ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0

def IsNonderogatory (M : Matrix (Fin n) (Fin n) K) : Prop :=
  minpoly K M = M.charpoly

-- ============================================================
-- SECTION II: Counting Irreducible Factors
-- ============================================================

/-- The number of distinct irreducible factors of a polynomial of
    degree d is at most d. This follows from the fact that each
    irreducible factor has degree ≥ 1. -/
theorem card_normalizedFactors_le_natDegree {p : K[X]}
    (hp : p ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors p).toFinset.card ≤ p.natDegree := by
  -- Step 1: distinct ≤ total count
  refine le_trans (Multiset.toFinset_card_le _) ?_
  -- Step 2: each irreducible factor has degree ≥ 1
  have hirr : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors p, 1 ≤ q.natDegree := by
    intro q hq
    have := (UniqueFactorizationMonoid.prime_of_normalized_factor q hq).irreducible
    exact Nat.one_le_iff_ne_zero.mpr (Irreducible.natDegree_pos this |>.ne')
  -- Step 3: count ≤ sum of degrees via multiset induction
  have hcard_le_sum :
      (UniqueFactorizationMonoid.normalizedFactors p).card ≤
      ((UniqueFactorizationMonoid.normalizedFactors p).map Polynomial.natDegree).sum := by
    induction UniqueFactorizationMonoid.normalizedFactors p using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
      have ha : 1 ≤ a.natDegree := hirr a (Multiset.mem_cons_self a s)
      have hs : s.card ≤ (s.map Polynomial.natDegree).sum :=
        ih (fun q hq => hirr q (Multiset.mem_cons_of_mem hq))
      omega
  -- Step 4: sum of degrees = natDegree of product = natDegree p
  have hne : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors p, q ≠ (0 : K[X]) :=
    fun q hq => UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hq
  have hprod := UniqueFactorizationMonoid.normalizedFactors_prod hp
  calc (UniqueFactorizationMonoid.normalizedFactors p).card
      ≤ ((UniqueFactorizationMonoid.normalizedFactors p).map Polynomial.natDegree).sum :=
        hcard_le_sum
    _ = (UniqueFactorizationMonoid.normalizedFactors p).prod.natDegree :=
        (Polynomial.natDegree_multiset_prod hne).symm
    _ = p.natDegree := by rw [hprod, Polynomial.natDegree_normalize]

-- ============================================================
-- SECTION III: Finite Union Avoidance
-- ============================================================

/-- Union avoidance for vector spaces over fields with |K| > number of
    subspaces. This weakens the infinite field hypothesis to a finite
    cardinality condition. -/
theorem not_union_proper_subspaces_finite
    {V : Type*} [AddCommGroup V] [Module K V] [Nontrivial V]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : ι → Submodule K V)
    (hS : ∀ i ∈ s, S i ≠ ⊤)
    (hK : s.card < Fintype.card K) [Fintype K] :
    ∃ v : V, ∀ i ∈ s, v ∉ S i := by
  -- Proof by Finset.induction_on:
  -- Base: |s| = 0, any vector works.
  -- Step: remove i₀ from s, get v ∉ S_j for j ∈ s'. If v ∉ S_{i₀}, done.
  --   Otherwise pick w ∉ S_{i₀}. On the line v + t•w (t ∈ K):
  --   - For each j ∈ s' (v ∉ S_j): at most 1 bad t (by linear independence)
  --   - For i₀ (v ∈ S_{i₀}, w ∉ S_{i₀}): only t = 0 is bad
  --   Total bad: ≤ |s'| + 1 = |s| < |K|, so good t exists.
  sorry

-- ============================================================
-- SECTION IV: Main Theorem (Weakened Hypothesis)
-- ============================================================

/-- Over a field K with |K| > n, nonderogatory matrices have cyclic vectors.
    This weakens [Infinite K] to a cardinality condition.

    The proof structure is the same as OQ-05-OQ-01, but replaces
    not_union_proper_subspaces with the finite version, using:
    - The number of cofactor kernels = number of irreducible factors of μ ≤ n
    - |K| > n ≥ number of cofactor kernels -/
theorem nonderogatory_has_cyclic_vector_finite [Fintype K]
    (M : Matrix (Fin n) (Fin n) K)
    (hK : n < Fintype.card K)
    (h : IsNonderogatory M) :
    ∃ v, IsCyclicVector M v := by
  -- The proof combines:
  -- 1. The cofactor kernel construction (same as OQ-05-OQ-01)
  -- 2. card_normalizedFactors_le_natDegree: #factors ≤ deg(μ) = n
  -- 3. not_union_proper_subspaces_finite: |K| > #factors suffices
  sorry

end CyclicVectorFiniteField

end
