/-
  Aristotle targets for ShannonSourceCodingOQ04.lean
  Routine supporting lemmas for automated proof search.
  See ShannonSourceCodingOQ04.lean for the main formalization.

  PRIMARY TARGET (Session 2):
  - type_class_size_eq_multinomial: |T_f| = n! / ∏(f i)! (multinomial counting fact)

  Previously proved in main file (included here for context, no sorries):
  - empDist_sum', typeProb_pos', log_typeProb_eq'
  Note: type_class_size_le_entropy_pow and dominant_type_lower_bound
  were proved in the main file (PR #12457); removed from this companion file.

  NOT included:
  - source_coding_achievability_mot (OPEN: needs LLN/concentration inequalities)
-/
import Mathlib

open Real Finset BigOperators

namespace ShannonSourceCodingOQ04Aristotle

variable {k : ℕ} [NeZero k]

-- ============================================================
-- Local definitions (matching ShannonSourceCodingOQ04.lean)
-- ============================================================

def empDist' (n : ℕ) (x : Fin n → Fin k) (i : Fin k) : ℕ :=
  (Finset.univ.filter fun j => x j = i).card

noncomputable def empEntropy' (n : ℕ) (hn : (n : ℝ) ≠ 0) (f : Fin k → ℕ) : ℝ :=
  -∑ i : Fin k,
    if f i = 0 then 0
    else (f i / (n : ℝ)) * Real.log (f i / (n : ℝ))

noncomputable def typeProb' (n : ℕ) (hn : (n : ℝ) ≠ 0) (f : Fin k → ℕ) : ℝ :=
  ∏ i : Fin k, ((f i : ℝ) / n) ^ (f i)

def typeClass' (n : ℕ) (f : Fin k → ℕ) (hf : ∑ i, f i = n) : Finset (Fin n → Fin k) :=
  Finset.univ.filter fun x => empDist' n x = f

-- ============================================================
-- Target 1: Empirical distribution sums to block length
-- ============================================================

/-- The empirical counts sum to n: ∑_i |{j : x j = i}| = n.
    Proof: the filters partition Finset.univ (Fin n) since every j has a unique image x j. -/
theorem empDist_sum' (n : ℕ) (x : Fin n → Fin k) :
    ∑ i : Fin k, empDist' n x i = n := by
  unfold empDist'
  have hdisj : (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint
      (fun i => Finset.univ.filter fun a : Fin n => x a = i) :=
    fun i _ j _ hij => Finset.disjoint_filter.mpr fun a _ ha hb => hij (ha ▸ hb)
  have huniv : (Finset.univ : Finset (Fin n)) =
      Finset.biUnion Finset.univ (fun i => Finset.univ.filter fun j => x j = i) := by
    ext a; simp
  calc ∑ i : Fin k, (Finset.univ.filter fun j : Fin n => x j = i).card
      = (Finset.biUnion Finset.univ (fun i => Finset.univ.filter fun j : Fin n => x j = i)).card :=
        (Finset.card_biUnion hdisj).symm
    _ = (Finset.univ : Finset (Fin n)).card := by rw [← huniv]
    _ = n := Finset.card_fin n

-- ============================================================
-- Target 2: Type probability is positive
-- ============================================================

/-- When all empirical counts are positive (f i > 0 for all i),
    the type probability typeProb' = ∏ ((f i)/n)^{f i} is strictly positive.
    Proof: product of positive reals is positive. -/
theorem typeProb_pos' (n : ℕ) (hn : (n : ℝ) ≠ 0)
    (hn_pos : 0 < (n : ℝ)) (f : Fin k → ℕ)
    (hf_pos : ∀ i, 0 < f i) :
    0 < typeProb' n hn f := by
  apply Finset.prod_pos
  intro i _
  apply pow_pos
  apply div_pos
  · exact_mod_cast hf_pos i
  · exact hn_pos

-- ============================================================
-- Target 3: log(typeProb') = -n * empEntropy'
-- ============================================================

/-- The log of typeProb' equals -(n : ℝ) * empEntropy', when all f i > 0.
    Proof: expand log of product, use log(a^b) = b·log(a),
    then rearrange to match empEntropy' definition. -/
theorem log_typeProb_eq' (n : ℕ) (hn : (n : ℝ) ≠ 0)
    (hn_pos : 0 < (n : ℝ)) (f : Fin k → ℕ)
    (hf_pos : ∀ i, (0 : ℝ) < (f i : ℝ) / n) :
    Real.log (typeProb' n hn f) = -(n : ℝ) * empEntropy' n hn f := by
  have hfi_ne_zero : ∀ i : Fin k, f i ≠ 0 := fun i => by
    intro h
    have hpos := hf_pos i
    have hcast : (f i : ℝ) = 0 := by exact_mod_cast h
    rw [hcast, zero_div] at hpos
    exact absurd hpos (lt_irrefl 0)
  simp only [typeProb', empEntropy']
  rw [Real.log_prod (fun i _ => ne_of_gt (pow_pos (hf_pos i) _))]
  simp_rw [Real.log_pow]
  have hif : ∀ i : Fin k,
      (if f i = 0 then (0 : ℝ) else (f i : ℝ) / n * Real.log ((f i : ℝ) / n)) =
      (f i : ℝ) / n * Real.log ((f i : ℝ) / n) :=
    fun i => if_neg (hfi_ne_zero i)
  simp_rw [hif]
  have neg_simp : -(n : ℝ) * (-(∑ i : Fin k, (f i : ℝ) / n * Real.log ((f i : ℝ) / n))) =
      (n : ℝ) * ∑ i : Fin k, (f i : ℝ) / n * Real.log ((f i : ℝ) / n) := by ring
  rw [neg_simp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hkey : (n : ℝ) * ((f i : ℝ) / n) = (f i : ℝ) := by field_simp
  calc (f i : ℝ) * Real.log ((f i : ℝ) / n)
      = ((n : ℝ) * ((f i : ℝ) / n)) * Real.log ((f i : ℝ) / n) := by rw [hkey]
    _ = (n : ℝ) * ((f i : ℝ) / n * Real.log ((f i : ℝ) / n)) := by ring

-- ============================================================
-- PRIMARY TARGET: Type class size = multinomial coefficient
-- ============================================================

/-- **Type class size equals the multinomial coefficient**: |T_f| = n! / ∏(f i)!

    This is the fundamental counting fact of the method of types (Csiszár-Körner 1981).

    Proof approach 1 (INDUCTION ON n):
    - Base n=0: one empty function, multinomial = 0!/1 = 1. ✓
    - Inductive step: partition T_f by the last element x(Fin.last n).
      For v with f(v) > 0: {x ∈ T_f | x(n) = v} ≅ T_{f[v ↦ f(v)-1]}
      via the bijection x ↦ x ∘ Fin.castSucc (drop last element).
      Pascal identity: multinomial(f) = ∑_{v:f(v)>0} multinomial(f[v↦f(v)-1])
      follows from: ∏(f i)! * multinomial(f) = n! (multinomial_spec) and
      ∏(f i)! * multinomial(update f v (f(v)-1)) = f(v) * (n-1)!
      (since ∏(update f v (f(v)-1) i)! = ∏(f i)! / f(v)).

    Proof approach 2 (PERMUTATION QUOTIENT):
    - Define canonical sequence C_f : Fin n → Fin k where position j maps to i
      if ∑_{l<i} f l ≤ j < ∑_{l≤i} f l (sorted multiset arrangement).
    - Map σ : Equiv.Perm (Fin n) ↦ C_f ∘ σ ∈ T_f.
    - Fiber over each x ∈ T_f has size ∏(f i)! (permutations within each preimage block).
    - Therefore |T_f| = n! / ∏(f i)! = multinomial (by multinomial_spec).

    Key lemmas:
    - Nat.multinomial_spec: ∏(f i)! * multinomial univ f = (∑ f i)! = n!
    - Fintype.card_perm: (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n! -/
theorem type_class_size_eq_multinomial (n : ℕ) (f : Fin k → ℕ) (hf : ∑ i, f i = n) :
    (typeClass' n f hf).card = Nat.multinomial Finset.univ f := by
  sorry

end ShannonSourceCodingOQ04Aristotle
