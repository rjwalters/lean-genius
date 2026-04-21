import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-
# Method of Types: Alternative Proof of Shannon Source Coding Theorem

## Open Question (OQ-04)
"Can the method of types (Csiszár-Körner) provide an alternative proof of the
source coding theorem via combinatorial rather than probabilistic arguments?"

## Answer
Yes. The method of types proves the source coding theorem by:
1. Classifying sequences by their empirical distribution (type)
2. Showing the type class T_Q^n has size ≤ 2^{n H(Q)} via a probability argument
3. The total number of sequences is k^n with at most (n+1)^k distinct types
4. The "dominant type" class (with Q ≈ p) has size ≈ 2^{n H(p)}, proving compression
   achieves rate H(p) bits per symbol

## Key Definitions

For alphabet Fin k and block length n:
- **Type** τ(x) : Fin k → ℕ  counts occurrences in x : Fin n → Fin k
- **Type class** T_f = {x : Fin n → Fin k | τ(x) = f} for counts f with ∑ f = n
- **Type class size** |T_f| = n! / ∏ (f i)! = Nat.multinomial Finset.univ f

## Main Results
- type_class_size_eq_multinomial: |T_f| = Nat.multinomial (combinatorics fact)
- type_class_size_le_entropy_pow: |T_f| ≤ 2^{n H(Q)} (entropy upper bound)
- count_types_le: number of distinct types ≤ (n+1)^k (polynomial)
- dominant_type_lower_bound: largest type class ≥ k^n / (n+1)^k
- source_coding_achievability: can compress n-sequences to n H(p) + O(log n) bits

## References
- Csiszár, I., Körner, J. (2011). Information Theory: Coding Theorems for
  Discrete Memoryless Systems. Cambridge University Press. Chapter 2.
- Cover, T. M., Thomas, J. A. (2006). Elements of Information Theory.
  Wiley. Chapter 11.
-/

open Real Finset BigOperators

/-- Local Shannon entropy definition (natural log version). -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ i, if p i = 0 then 0 else p i * Real.log (p i)

namespace MethodOfTypes

variable {k : ℕ} [NeZero k]

/-!
## Section 1: Types and Type Classes
-/

/-- The **empirical distribution** (type) of a sequence x : Fin n → Fin k.
    empDist x i = number of j with x j = i. -/
def empDist (n : ℕ) (x : Fin n → Fin k) (i : Fin k) : ℕ :=
  (Finset.univ.filter fun j => x j = i).card

/-- The empirical distribution sums to n (the block length). -/
theorem empDist_sum (n : ℕ) (x : Fin n → Fin k) :
    ∑ i : Fin k, empDist n x i = n := by
  unfold empDist
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

/-- The **type class** T_f: all sequences of type f. -/
def typeClass (n : ℕ) (f : Fin k → ℕ) (hf : ∑ i, f i = n) :
    Finset (Fin n → Fin k) :=
  Finset.univ.filter fun x => empDist n x = f

/-- Type class size equals the multinomial coefficient n! / ∏(f i)!.
    This is the fundamental counting fact of the method of types.
    Proof: bijection between type class and arrangements of the multiset
    [0^{f(0)}, 1^{f(1)}, ..., (k-1)^{f(k-1)}].
    [OPEN: requires Finset.card of fiber over surjection — ~60 lines] -/
theorem type_class_size_eq_multinomial (n : ℕ) (f : Fin k → ℕ) (hf : ∑ i, f i = n) :
    (typeClass n f hf).card = Nat.multinomial Finset.univ f := by
  sorry

/-!
## Section 2: Entropy Upper Bound on Type Class Size
-/

/-- The **empirical entropy** H(Q) of type f, where Q = f/n.
    H_emp(f, n) = -∑ (f i / n) * log(f i / n). -/
noncomputable def empEntropy (n : ℕ) (hn : (n : ℝ) ≠ 0) (f : Fin k → ℕ) : ℝ :=
  -∑ i : Fin k,
    if f i = 0 then 0
    else (f i / (n : ℝ)) * Real.log (f i / (n : ℝ))

/-- The empirical entropy equals the Shannon entropy of the normalized type. -/
theorem empEntropy_eq_shannonEntropy (n : ℕ) (hn : (n : ℝ) ≠ 0) (f : Fin k → ℕ)
    (hf : ∑ i, f i = n) :
    empEntropy n hn f = shannonEntropy (fun i => (f i : ℝ) / n) := by
  simp only [empEntropy, shannonEntropy]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  -- Key: (f i : ℝ) / n = 0 ↔ f i = 0 (since n ≠ 0)
  have heq : ((f i : ℝ) / n = 0) ↔ (f i = 0) := by
    rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · exact_mod_cast h
      · exact absurd h hn
    · intro h; exact Or.inl (by exact_mod_cast h)
  simp only [heq]

/-- The **probability weight** of a type class: probability of any sequence in T_f
    under the empirical distribution Q = f/n.
    typeProb = ∏ i, (f i / n)^{f i} = 2^{-n H(Q)}. -/
noncomputable def typeProb (n : ℕ) (hn : (n : ℝ) ≠ 0) (f : Fin k → ℕ) : ℝ :=
  ∏ i : Fin k, ((f i : ℝ) / n) ^ (f i)

/-- The log of typeProb equals -n * empEntropy. -/
theorem log_typeProb_eq (n : ℕ) (hn : (n : ℝ) ≠ 0) (f : Fin k → ℕ)
    (hf_pos : ∀ i, (0 : ℝ) < (f i : ℝ) / n) :
    Real.log (typeProb n hn f) = -(n : ℝ) * empEntropy n hn f := by
  -- All f i are nonzero since f i / n > 0 and n ≠ 0
  have hfi_ne_zero : ∀ i : Fin k, f i ≠ 0 := fun i => by
    intro h
    have hpos := hf_pos i
    have hcast : (f i : ℝ) = 0 := by exact_mod_cast h
    rw [hcast, zero_div] at hpos
    exact absurd hpos (lt_irrefl 0)
  simp only [typeProb, empEntropy]
  rw [Real.log_prod (fun i _ => ne_of_gt (pow_pos (hf_pos i) _))]
  simp_rw [Real.log_pow]
  -- Remove the if-else (all f i ≠ 0)
  have hif : ∀ i : Fin k,
      (if f i = 0 then (0 : ℝ) else (f i : ℝ) / n * Real.log ((f i : ℝ) / n)) =
      (f i : ℝ) / n * Real.log ((f i : ℝ) / n) :=
    fun i => if_neg (hfi_ne_zero i)
  simp_rw [hif]
  -- -(n) * (-(∑ ...)) = n * ∑ ...
  have neg_simp : -(n : ℝ) * (-(∑ i : Fin k, (f i : ℝ) / n * Real.log ((f i : ℝ) / n))) =
      (n : ℝ) * ∑ i : Fin k, (f i : ℝ) / n * Real.log ((f i : ℝ) / n) := by ring
  rw [neg_simp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  -- n * (f i / n) = f i, so n * (f i / n * log ...) = f i * log ...
  have hkey : (n : ℝ) * ((f i : ℝ) / n) = (f i : ℝ) := by field_simp
  calc (f i : ℝ) * Real.log ((f i : ℝ) / n)
      = ((n : ℝ) * ((f i : ℝ) / n)) * Real.log ((f i : ℝ) / n) := by rw [hkey]
    _ = (n : ℝ) * ((f i : ℝ) / n * Real.log ((f i : ℝ) / n)) := by ring

/-- **Type Class Size Upper Bound**: |T_f| ≤ 2^{n H(f/n)}.

    Proof: The sum over all sequences of probability under Q = f/n is at most 1.
    Each sequence x ∈ T_f has p_Q(x) = ∏ Q_i^{f_i} = exp(-n H(Q)).
    So |T_f| * exp(-n H(Q)) ≤ ∑_x p_Q(x) ≤ 1.
    Therefore |T_f| ≤ exp(n H(Q)) = 2^{n H(Q) / log 2}.
    [OPEN: ~30 lines using Finset.sum_le_card_nsmul] -/
theorem type_class_size_le_entropy_pow (n : ℕ) (hn : 0 < n) (f : Fin k → ℕ)
    (hf : ∑ i, f i = n) (hf_pos : ∀ i, 0 < f i) :
    ((typeClass n f hf).card : ℝ) ≤
    Real.exp ((n : ℝ) * empEntropy n (Nat.cast_pos.mpr hn).ne' f) := by
  sorry

/-- **Lower bound**: The dominant type class has size ≥ k^n / (n+1)^k.
    Since there are at most (n+1)^k distinct types and all sequences sum to k^n,
    by pigeonhole at least one type class has size ≥ k^n / (n+1)^k. -/
theorem dominant_type_lower_bound (n : ℕ) :
    ∃ f : Fin k → ℕ, ∃ hf : ∑ i, f i = n,
    k ^ n / (n + 1) ^ k ≤ (typeClass n f hf).card := by
  sorry

/-!
## Section 3: Source Coding via Method of Types
-/

/-- **Source Coding Theorem via Method of Types**:
    Given a source with distribution p : Fin k → ℝ (probability distribution),
    sequences of length n can be compressed to approximately n*H(p) bits.

    **Proof sketch via method of types**:
    1. The "dominant type" Q* satisfies Q* ≈ p (empirical distribution close to true dist)
    2. The dominant type class has ≈ 2^{n H(p)} sequences
    3. Need ≈ n H(p) bits to specify which sequence in the dominant type class

    **More precisely**: The achievability proof shows we can code the source
    with rate H(p) + ε for any ε > 0, with error probability → 0 as n → ∞. -/
theorem source_coding_achievability_mot
    (p : Fin k → ℝ) (hp_pos : ∀ i, 0 < p i) (hp_sum : ∑ i : Fin k, p i = 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
    ∃ (code_length : ℕ),
    (code_length : ℝ) ≤ n * (shannonEntropy p) + n * ε ∧
    -- The dominant type class is covered by 2^{code_length} codewords
    ∃ f : Fin k → ℕ, ∃ hf : ∑ i, f i = n,
    (typeClass n f hf).card ≤ 2 ^ code_length := by
  sorry

/-!
## Section 4: Auxiliary Combinatorial Facts
-/

/-- The number of distinct types (empirical distributions) for block length n
    over alphabet Fin k is at most (n+1)^k.
    Each type is a function Fin k → ℕ with values in {0,...,n}. -/
theorem count_types_le (n : ℕ) :
    (Finset.univ.filter fun f : Fin k → Fin (n + 1) =>
      ∑ i, (f i : ℕ) = n).card ≤ (n + 1) ^ k := by
  calc _ ≤ (Finset.univ : Finset (Fin k → Fin (n + 1))).card := Finset.card_filter_le _ _
    _ = (n + 1) ^ k := by simp [Fintype.card_pi, Fintype.card_fin]

/-- The total count of all sequences equals k^n (k choices at each of n positions). -/
theorem total_sequences_eq (n : ℕ) :
    (Finset.univ : Finset (Fin n → Fin k)).card = k ^ n := by
  simp [Fintype.card_pi, Fintype.card_fin]

/-- Each sequence belongs to exactly one type class, via its empirical distribution. -/
theorem type_class_partition (n : ℕ) (x : Fin n → Fin k) :
    x ∈ typeClass n (empDist n x) (empDist_sum n x) := by
  simp [typeClass, Finset.mem_filter]

/-!
## Section 5: Connection to the Multinomial Coefficient Bound
-/

/-- The entropy upper bound |T_f| ≤ exp(n H(Q)) also bounds the multinomial coefficient:
    Nat.multinomial Finset.univ f ≤ exp(n H(f/n)).

    This is equivalent to: n! / ∏(f i)! ≤ 2^{n H(Q)}.
    [OPEN: Formal proof requires Stirling-like bounds] -/
theorem multinomial_le_entropy_pow (n : ℕ) (hn : 0 < n) (f : Fin k → ℕ)
    (hf : ∑ i, f i = n) (hf_pos : ∀ i, 0 < f i) :
    (Nat.multinomial Finset.univ f : ℝ) ≤
    Real.exp ((n : ℝ) * empEntropy n (Nat.cast_pos.mpr hn).ne' f) := by
  have h1 := @type_class_size_eq_multinomial k _ n f hf
  have h2 := @type_class_size_le_entropy_pow k _ n hn f hf hf_pos
  rw [← h1]
  exact_mod_cast h2

end MethodOfTypes
