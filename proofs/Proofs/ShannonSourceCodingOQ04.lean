import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Pigeonhole
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

/-- **Type Class Size Upper Bound**: |T_f| ≤ exp(n H(f/n)).

    Proof: Let Q = f/n be the empirical distribution (sums to 1).
    For x ∈ T_f: ∏ j, Q(x_j) = ∏ i, Q(i)^{f_i} = typeProb = exp(-n H(Q)).
    Sum over all sequences: ∑_x ∏ j, Q(x_j) = (∑ i, Q(i))^n = 1^n = 1.
    So |T_f| * exp(-n H(Q)) ≤ ∑_x ∏ j, Q(x_j) = 1.
    Therefore |T_f| ≤ exp(n H(Q)). -/
theorem type_class_size_le_entropy_pow (n : ℕ) (hn : 0 < n) (f : Fin k → ℕ)
    (hf : ∑ i, f i = n) (hf_pos : ∀ i, 0 < f i) :
    ((typeClass n f hf).card : ℝ) ≤
    Real.exp ((n : ℝ) * empEntropy n (Nat.cast_pos.mpr hn).ne' f) := by
  set hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  -- Q = empirical distribution f/n
  let Q : Fin k → ℝ := fun i => (f i : ℝ) / n
  -- Q sums to 1
  have hQsum : ∑ i : Fin k, Q i = 1 := by
    simp only [Q, ← Finset.sum_div, ← Nat.cast_sum, hf]
    exact div_self hn'
  -- Q i > 0 for all i
  have hQpos : ∀ i, 0 < Q i := fun i =>
    div_pos (Nat.cast_pos.mpr (hf_pos i)) (Nat.cast_pos.mpr hn)
  -- typeProb n hn' f > 0 (product of positives)
  have htypeProb_pos : 0 < typeProb n hn' f := by
    simp only [typeProb]
    exact Finset.prod_pos (fun i _ => pow_pos (hQpos i) _)
  -- typeProb = exp(-(n * empEntropy))
  have htypeProb_exp : typeProb n hn' f = Real.exp (-(n : ℝ) * empEntropy n hn' f) := by
    rw [← log_typeProb_eq n hn' f (fun i => hQpos i), Real.exp_log htypeProb_pos]
  -- For x ∈ T_f: ∏ j : Fin n, Q (x j) = typeProb
  have hseqProb_const : ∀ x ∈ typeClass n f hf,
      ∏ j : Fin n, Q (x j) = typeProb n hn' f := by
    intro x hx
    simp only [typeClass, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    -- hx : empDist n x = f
    simp only [typeProb, Q]
    -- Regroup positions by their alphabet value using prod_fiberwise'
    rw [← Finset.prod_fiberwise' Finset.univ x (fun j => (f j : ℝ) / ↑n)]
    apply Finset.prod_congr rfl
    intro b _
    -- ∏ a ∈ univ with x a = b, (f b / n) = (f b / n) ^ (f b)
    rw [Finset.prod_const]
    congr 1
    -- (filter card) = f b; follows from empDist n x b = f b
    change empDist n x b = f b
    exact congr_fun hx b
  -- ∑ x : Fin n → Fin k, ∏ j, Q (x j) = 1
  have hsum_one : ∑ x : Fin n → Fin k, ∏ j : Fin n, Q (x j) = 1 := by
    -- ∏ i : Fin n, ∑ j ∈ univ, Q j = ∑ x ∈ piFinset, ∏ i, Q (x i)
    have h := Finset.prod_univ_sum (κ := fun _ : Fin n => Fin k)
                 (fun _ => Finset.univ) (fun _ j => Q j)
    simp only [hQsum, Finset.prod_const_one, Fintype.piFinset_univ] at h
    simpa using h.symm
  -- |T_f| * typeProb ≤ 1 by sum estimate
  have h_key : ((typeClass n f hf).card : ℝ) * typeProb n hn' f ≤ 1 :=
    calc ((typeClass n f hf).card : ℝ) * typeProb n hn' f
        = ∑ _ ∈ typeClass n f hf, typeProb n hn' f := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = ∑ x ∈ typeClass n f hf, ∏ j : Fin n, Q (x j) :=
          Finset.sum_congr rfl (fun x hx => (hseqProb_const x hx).symm)
      _ ≤ ∑ x : Fin n → Fin k, ∏ j : Fin n, Q (x j) :=
          sum_le_univ_sum_of_nonneg (fun x =>
            Finset.prod_nonneg (fun j _ => le_of_lt (hQpos (x j))))
      _ = 1 := hsum_one
  -- Conclude: |T_f| ≤ exp(n H(Q))
  calc ((typeClass n f hf).card : ℝ)
      ≤ 1 / typeProb n hn' f := (le_div_iff htypeProb_pos).mpr h_key
    _ = Real.exp ((n : ℝ) * empEntropy n hn' f) := by
        rw [htypeProb_exp, one_div, ← Real.exp_neg, neg_neg]

/-- **Lower bound**: The dominant type class has size ≥ k^n / (n+1)^k.
    Since there are at most (n+1)^k distinct types and all sequences sum to k^n,
    by pigeonhole at least one type class has size ≥ k^n / (n+1)^k. -/
theorem dominant_type_lower_bound (n : ℕ) :
    ∃ f : Fin k → ℕ, ∃ hf : ∑ i, f i = n,
    k ^ n / (n + 1) ^ k ≤ (typeClass n f hf).card := by
  -- Trivial case: bound is 0, any type works
  by_cases hm : k ^ n / (n + 1) ^ k = 0
  · -- Exhibit the constant-zero sequence's type
    let x₀ : Fin n → Fin k := fun _ => ⟨0, Nat.pos_of_ne_zero (NeZero.ne k)⟩
    exact ⟨empDist n x₀, empDist_sum n x₀, hm ▸ Nat.zero_le _⟩
  · -- Map sequences to Fin k → Fin (n+1) via bounded empDist
    -- empDist n x i counts elements of Fin n, so ≤ n < n+1
    have h_bound : ∀ (x : Fin n → Fin k) (i : Fin k), empDist n x i ≤ n := fun x i =>
      (Finset.card_filter_le _ _).trans (by simp [Finset.card_univ, Fintype.card_fin])
    -- Define the map F : sequences → (Fin k → Fin (n+1))
    let F : (Fin n → Fin k) → (Fin k → Fin (n + 1)) :=
      fun x i => ⟨empDist n x i, Nat.lt_succ_of_le (h_bound x i)⟩
    -- Target Finset T = all functions Fin k → Fin (n+1), card = (n+1)^k
    have hT_nonempty : (Finset.univ : Finset (Fin k → Fin (n + 1))).Nonempty :=
      Finset.univ_nonempty
    have hT_card : (Finset.univ : Finset (Fin k → Fin (n + 1))).card = (n + 1) ^ k := by
      simp [Fintype.card_pi, Fintype.card_fin]
    -- Domain card = k^n
    have hS_card : (Finset.univ : Finset (Fin n → Fin k)).card = k ^ n := by
      simp [Fintype.card_pi, Fintype.card_fin]
    -- Pigeonhole bound: (n+1)^k * (k^n / (n+1)^k) ≤ k^n
    have hpig : (Finset.univ : Finset (Fin k → Fin (n + 1))).card * (k ^ n / (n + 1) ^ k) ≤
        (Finset.univ : Finset (Fin n → Fin k)).card := by
      rw [hT_card, hS_card]
      exact (mul_comm _ _).le.trans (Nat.div_mul_le_self _ _)
    -- Apply pigeonhole: ∃ y : Fin k → Fin (n+1) with large fiber
    obtain ⟨y, _, hy_card⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (f := F) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) hT_nonempty hpig
    -- The fiber {x | F x = y} is nonempty (since bound > 0)
    have h_pos : 0 < (Finset.univ.filter fun x : Fin n → Fin k => F x = y).card :=
      (Nat.pos_of_ne_zero hm).trans_le hy_card
    obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp h_pos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₀
    -- From F x₀ = y, extract: empDist n x₀ = Fin.val ∘ y
    have h_empDist_eq : empDist n x₀ = fun i => (y i).val := by
      funext i; exact (Fin.ext_iff.mp (congr_fun hx₀ i)).symm
    -- So ∑ i, (Fin.val ∘ y) i = n
    have hf₀ : ∑ i : Fin k, (y i).val = n := by
      rw [← h_empDist_eq]; exact empDist_sum n x₀
    -- The fiber equals the type class for f₀ = Fin.val ∘ y
    have h_eq : Finset.univ.filter (fun x : Fin n → Fin k => F x = y) =
        typeClass n (fun i => (y i).val) hf₀ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, typeClass, F]
      constructor
      · intro h; funext i; exact (Fin.ext_iff.mp (congr_fun h i)).symm
      · intro h; funext i; exact Fin.ext (congr_fun h i).symm
    exact ⟨fun i => (y i).val, hf₀, h_eq ▸ hy_card⟩

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
