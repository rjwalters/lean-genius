/-
  Aristotle targets for ShannonSourceCodingOQ04.lean
  Routine supporting lemmas for automated proof search.
  See ShannonSourceCodingOQ04.lean for the main formalization.

  Targets:
  - empDist_sum: empirical distribution counts sum to block length n
  - typeProb_pos: type probability is positive when all empirical counts are positive
  - typeProb_eq_exp_neg: typeProb = exp(-n H_emp(Q)) via log identity
  - type_class_size_le_entropy_pow: |T_f| ≤ exp(n H(f/n)) (method of types key bound)
  - dominant_type_lower_bound: pigeonhole bound on largest type class size

  NOT included:
  - type_class_size_eq_multinomial (requires ~60-line bijection argument)
  - source_coding_achievability_mot (main theorem; assembles the above)
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
-- Target 4: Type class size ≤ exp(n H_emp(Q))
-- ============================================================

/-- **Type Class Size Upper Bound** (method of types key lemma).

    For any type f with ∑ f i = n and all f i > 0:
      |T_f| ≤ exp(n H(f/n))

    Proof sketch (probability argument):
    1. Each x ∈ typeClass'(f) satisfies empDist' n x = f (by definition)
    2. Assign Q-probability: prob(x) = ∏_i (f_i/n)^{f_i} = typeProb' (constant on T_f)
    3. ∑_{x : Fin n → Fin k} prob(x) ≤ 1 (multinomial normalization)
    4. ∑_{x ∈ T_f} prob(x) = |T_f| * typeProb' (sum of constant = card times value)
    5. So |T_f| * typeProb' ≤ 1, hence |T_f| ≤ exp(n H(Q)) = 1/typeProb'. -/
theorem type_class_size_le_entropy_pow' (n : ℕ) (hn : 0 < n) (f : Fin k → ℕ)
    (hf : ∑ i, f i = n) (hf_pos : ∀ i, 0 < f i) :
    ((typeClass' n f hf).card : ℝ) ≤
    Real.exp ((n : ℝ) * empEntropy' n (Nat.cast_pos.mpr hn).ne' f) := by
  sorry

-- ============================================================
-- Target 5: Dominant type class lower bound (pigeonhole)
-- ============================================================

/-- **Dominant Type Lower Bound** (pigeonhole principle).

    There exists a type f with ∑ f i = n such that its type class satisfies
      |T_f| ≥ k^n / (n+1)^k

    Proof: There are k^n total sequences (Fintype.card (Fin n → Fin k) = k^n)
    and at most (n+1)^k distinct types (each type maps Fin k to {0,...,n}).
    By pigeonhole, some type class has size ≥ k^n / (n+1)^k. -/
theorem dominant_type_lower_bound' (n : ℕ) :
    ∃ f : Fin k → ℕ, ∃ hf : ∑ i, f i = n,
    k ^ n / (n + 1) ^ k ≤ (typeClass' n f hf).card := by
  sorry

end ShannonSourceCodingOQ04Aristotle
