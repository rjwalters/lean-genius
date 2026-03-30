/-
  Erdős Problem #1, Open Question 02:
  Improved Lower Bounds for Distinct Subset Sums

  This file improves the basic counting bound N ≥ (2^n - 1)/n by using
  the fact that DSS elements must be distinct (and hence, when bounded
  by N, their sum is at most nN - n(n-1)/2 instead of nN).

  Main result (2× form, division-free):
    2·n·N + 2 ≥ 2^(n+1) + n·(n-1)

  Readable form: N ≥ (2^n - 1)/n + (n-1)/2

  For n = 4: counting bound → N ≥ 3, improved → N ≥ 5 (actual: 7)
  For n = 5: counting bound → N ≥ 6, improved → N ≥ 8 (actual: 13)
  For n = 8: counting bound → N ≥ 31, improved → N ≥ 34 (actual: 84)

  The improvement of (n-1)/2 comes from the distinctness of elements:
  n distinct naturals ≤ N have sum ≤ nN - n(n-1)/2 (the top-n bound).
  Combined with the DSS sum bound sum(A) ≥ 2^n - 1, this gives
  the tighter lower bound on N.

  This bridges part of the gap between the basic counting bound and the
  Dubroff-Fox-Xu (2021) bound N ≥ Ω(2^n/√n).

  Status: FORMALIZED (0 axioms, 0 sorries)
  Reference: https://erdosproblems.com/1
-/

import Proofs.Erdos1OQ01
import Mathlib

open Finset

-- ════════════════════════════════════════════════════════════════
-- PART I: Sum Lower Bound for Distinct Natural Numbers
-- ════════════════════════════════════════════════════════════════

/-- Generalized lower bound: n distinct naturals, each ≥ c, have total
    sum ≥ cn + n(n-1)/2. In "2×" form to avoid division.

    Proof by induction on n: extract the minimum m ≥ c; the remaining
    n-1 elements are all ≥ m+1, so the IH applies with c' = m+1. -/
theorem sum_lower_bound_gen (n : ℕ) :
    ∀ (c : ℕ) (B : Finset ℕ), B.card = n → (∀ b ∈ B, c ≤ b) →
    n * (2 * c + n - 1) ≤ 2 * B.sum id := by
  induction n with
  | zero =>
    intro c B hcard _
    simp [Finset.card_eq_zero.mp hcard]
  | succ n ih =>
    intro c B hcard hge
    have hne : B.Nonempty := Finset.card_pos.mp (by omega)
    set m := B.min' hne with hm_def
    have hm_mem : m ∈ B := B.min'_mem hne
    have hm_ge : c ≤ m := hge m hm_mem
    set B' := B.erase m with hB'_def
    have hcard' : B'.card = n := by
      rw [Finset.card_erase_of_mem hm_mem, hcard]; omega
    have hge' : ∀ b ∈ B', m + 1 ≤ b := by
      intro b hb
      have ⟨hne_m, hb_mem⟩ := Finset.mem_erase.mp hb
      have hle := B.min'_le b hb_mem
      omega
    have ih' := ih (m + 1) B' hcard' hge'
    have hsum_decomp : B.sum id = B'.sum id + m := by
      have h := Finset.add_sum_erase B id hm_mem
      linarith
    -- Simplify ℕ subtraction in the goal and ih'
    have hgoal_sub : 2 * c + (n + 1) - 1 = 2 * c + n := by omega
    have hih_sub : 2 * (m + 1) + n - 1 = 2 * m + n + 1 := by omega
    rw [hsum_decomp, show n + 1 = n.succ from rfl]
    simp only [Nat.succ_eq_add_one]
    rw [show (n + 1) * (2 * c + (n + 1) - 1) = (n + 1) * (2 * c + n) from by omega]
    rw [show n * (2 * (m + 1) + n - 1) = n * (2 * m + n + 1) from by omega] at ih'
    nlinarith [hm_ge]

/-- Corollary: any n distinct non-negative integers sum to ≥ n(n-1)/2.
    In 2× form: 2·sum(B) ≥ |B|·(|B|-1). -/
theorem two_mul_sum_ge_card_pred (B : Finset ℕ) :
    B.card * (B.card - 1) ≤ 2 * B.sum id := by
  have h := sum_lower_bound_gen B.card 0 B rfl (fun _ _ => Nat.zero_le _)
  simpa using h

-- ════════════════════════════════════════════════════════════════
-- PART II: Sum Upper Bound for Distinct Bounded Naturals
-- ════════════════════════════════════════════════════════════════

/-- The complement sum identity: for A ⊆ {0,...,N},
    n·N = ∑(N - a) + ∑ a, where sums are over A.

    Proof by induction on A using Finset.induction_on. -/
theorem complement_sum_identity {A : Finset ℕ} {N : ℕ}
    (hA : ∀ a ∈ A, a ≤ N) :
    A.card * N = A.sum (fun a => N - a) + A.sum id := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    simp only [Finset.sum_insert has, Finset.card_insert_of_not_mem has, id]
    have ha := hA a (Finset.mem_insert_self a s)
    have hs := fun x hx => hA x (Finset.mem_insert_of_mem hx)
    nlinarith [ih hs, Nat.sub_add_cancel ha]

/-- If A has n distinct elements in {0,...,N}, then
    2·sum(A) + n(n-1) ≤ 2nN.

    Proof: the "complement" map a ↦ N-a sends A to a set B of n
    distinct non-negative integers with sum = nN - sum(A).
    By the lower bound on B, nN - sum(A) ≥ n(n-1)/2. -/
theorem sum_upper_bound_distinct {A : Finset ℕ} {N : ℕ}
    (hA : ∀ a ∈ A, a ≤ N) :
    2 * A.sum id + A.card * (A.card - 1) ≤ 2 * A.card * N := by
  -- The complement map a ↦ N - a is injective on A
  have hinj : ∀ x ∈ A, ∀ y ∈ A, N - x = N - y → x = y := by
    intro x hx y hy hxy
    have := hA x hx; have := hA y hy; omega
  -- Image B has same card
  set B := A.image (fun a => N - a)
  have hcard_B : B.card = A.card :=
    Finset.card_image_of_injOn (by
      intro x hx y hy hxy
      exact hinj x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy)
  -- B.sum id = A.sum (fun a => N - a) via the image-sum identity
  have hsum_B : B.sum id = A.sum (fun a => N - a) :=
    Finset.sum_image hinj
  -- The complement sum identity
  have hident := complement_sum_identity hA
  -- Lower bound on B: 2 · sum(B) ≥ |B| · (|B| - 1)
  have hB_bound := two_mul_sum_ge_card_pred B
  rw [hcard_B, hsum_B] at hB_bound
  -- Combine: A.card * (A.card - 1) ≤ 2 * A.sum (fun a => N - a)
  -- = 2 * (A.card * N - A.sum id) from hident
  linarith

-- ════════════════════════════════════════════════════════════════
-- PART III: The Improved Lower Bound for DSS
-- ════════════════════════════════════════════════════════════════

/-- DSS sets contain no zero: if 0 ∈ A, then ∅ and {0} are distinct
    subsets with equal sums, contradicting DSS. -/
theorem dss_pos_of_mem {A : Finset ℕ} (hA : hasDistinctSubsetSums A)
    {a : ℕ} (ha : a ∈ A) : 0 < a := by
  by_contra h
  push_neg at h
  interval_cases a
  have h := hA ∅ {0} (Finset.empty_subset A)
    (Finset.singleton_subset_iff.mpr ha) (by simp)
  simp at h

/-- **Improved Erdős #1 bound**: For a DSS set of n elements in {0,...,N}:
    2nN + 2 ≥ 2^(n+1) + n(n-1).

    This improves the counting bound (which gives 2^(n+1) ≤ 2nN + 2)
    by the additive term n(n-1), coming from the distinctness of elements.

    Equivalently: N ≥ (2^n - 1)/n + (n-1)/2. -/
theorem improved_dss_bound {A : Finset ℕ} {N : ℕ}
    (hA : ∀ a ∈ A, a ≤ N)
    (hDistinct : hasDistinctSubsetSums A) :
    2 ^ (A.card + 1) + A.card * (A.card - 1) ≤ 2 * A.card * N + 2 := by
  -- From DSS: 2^n ≤ sum(A) + 1
  have hsum_bound := distinct_subset_sums_sum_bound hDistinct
  -- From distinctness + bounded: 2·sum(A) + n(n-1) ≤ 2nN
  have hupper := sum_upper_bound_distinct hA
  -- 2^(n+1) = 2 · 2^n
  have hpow : 2 ^ (A.card + 1) = 2 * 2 ^ A.card := by ring
  -- Combine: 2^(n+1) + n(n-1) ≤ (2·sum(A) + 2) + n(n-1) ≤ 2nN + 2
  linarith

-- ════════════════════════════════════════════════════════════════
-- PART IV: Small Case Verification
-- ════════════════════════════════════════════════════════════════

/-- n = 4: Counting → N ≥ 3, improved → N ≥ 5, actual f(4) = 7 -/
example : (2 ^ 4 - 1) / 4 + (4 - 1) / 2 = 5 := by norm_num

/-- n = 5: Counting → N ≥ 6, improved → N ≥ 8, actual f(5) = 13 -/
example : (2 ^ 5 - 1) / 5 + (5 - 1) / 2 = 8 := by norm_num

/-- n = 8: Counting → N ≥ 31, improved → N ≥ 34, actual f(8) = 84 -/
example : (2 ^ 8 - 1) / 8 + (8 - 1) / 2 = 34 := by norm_num

-- ════════════════════════════════════════════════════════════════
-- PART V: The Dubroff-Fox-Xu Bound (Statement Only)
-- ════════════════════════════════════════════════════════════════

/-- **Dubroff-Fox-Xu (2021)**: Best known lower bound.
    ∃ C > 0 such that for all DSS sets A ⊆ {1,...,N} with |A| = n ≥ 1,
    N ≥ C · 2^n / √n.

    Our improved bound gives N ≥ 2^n/n + n/2 (roughly), while DFX gives
    N ≥ c · 2^n/√n. The gap is a factor of √n in the leading term.

    The full Erdős $500 conjecture asks: N ≥ c · 2^n (no √n factor). -/
def dubroff_fox_xu_bound : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ (A : Finset ℕ) (N : ℕ),
    (∀ a ∈ A, a ≤ N) →
    hasDistinctSubsetSums A →
    A.card ≥ 1 →
    C * (2 : ℝ) ^ A.card / Real.sqrt A.card ≤ (N : ℝ)

/-
## Summary

**Theorems (6)**:
- sum_lower_bound_gen: n distinct naturals ≥ c have 2·sum ≥ n·(2c+n-1)
- two_mul_sum_ge_card_pred: n distinct naturals have 2·sum ≥ n·(n-1)
- complement_sum_identity: n·N = ∑(N-a) + ∑a for A ⊆ {0,...,N}
- sum_upper_bound_distinct: n distinct elements ≤ N have 2·sum + n(n-1) ≤ 2nN
- dss_pos_of_mem: DSS sets have only positive elements
- improved_dss_bound: 2nN + 2 ≥ 2^(n+1) + n(n-1) for DSS sets in {0,...,N}

**Definitions (1)**:
- dubroff_fox_xu_bound: DFX bound statement (N ≥ C·2^n/√n)

**Axioms (0)**, **Sorries (0)**

The key improvement over the counting bound:
- Counting: 2^(n+1) ≤ 2nN + 2
- Improved: 2^(n+1) + n(n-1) ≤ 2nN + 2

The extra n(n-1) term comes from the fact that n distinct naturals ≤ N
must "waste" at least n(n-1)/2 in total gap (they can't all equal N),
so their sum is ≤ nN - n(n-1)/2 instead of ≤ nN.

References:
- Erdős (1955): Problems and results in additive number theory
- Conway, Guy (1968): Upper bound construction
- Dubroff, Fox, Xu (2021): N ≥ √(2/π) · 2^n / √n
-/
