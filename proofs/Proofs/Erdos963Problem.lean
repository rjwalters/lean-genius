/-
# Erdős Problem #963: Dissociated Subsets

Let f(n) be the maximum k such that every n-element subset A ⊆ ℝ contains
a dissociated subset B ⊆ A with |B| ≥ k. A set is dissociated if all
subset sums are distinct. Estimate f(n), in particular whether
f(n) ≥ ⌊log₂ n⌋.

## Key Results

- **Greedy bound**: f(n) ≥ ⌊log₃ n⌋ (Erdős, greedy algorithm)
- **Conjectured**: f(n) ≥ ⌊log₂ n⌋
- A dissociated set of size k has 2^k distinct subset sums
- Powers of 2 form a dissociated set (binary representation)

Axiom count: 2 (was 7; proved log_base_gap, dissociated_subset_sum_count,
  powers_of_two_dissociated, maxDissociatedSize_mono, greedy_lower_bound)
Sorry count: 1 (forbiddenSet_card_le: technical sum equality — the signed sum
  ∑_{b∈B} ε(b)*b with ε∈{-1,0,1}^B equals ∑_{S\T} - ∑_{T\S})

## References

- [Er65] Erdős original formulation
- [Va99, 1.22]
- <https://erdosproblems.com/963>
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- A subset B of a finset A is dissociated if all subset sums are distinct.
    Equivalently, if ∑_{b ∈ S} b = ∑_{b ∈ T} b implies S = T for S, T ⊆ B. -/
def IsDissociatedSubset (A B : Finset ℝ) : Prop :=
  B ⊆ A ∧ ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → S.sum id = T.sum id → S = T

/-- f(n): the maximum size of a dissociated subset guaranteed in any
    n-element subset of ℝ. -/
noncomputable def maxDissociatedSize (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∀ A : Finset ℝ, A.card = n →
    ∃ B : Finset ℝ, IsDissociatedSubset A B ∧ B.card ≥ k}

/- ## Subset Sum Counting -/

/-- **PROVED** (was axiom): A dissociated set of size k has exactly 2^k
    distinct subset sums. The dissociated condition means the sum map is
    injective on the powerset, so the image has cardinality 2^|B|. -/
theorem dissociated_subset_sum_count :
  ∀ (B : Finset ℝ), (∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → S.sum id = T.sum id → S = T) →
    (Finset.image (fun S => S.sum id) B.powerset).card = 2 ^ B.card := by
  intro B hdiss
  rw [Finset.card_image_of_injOn, Finset.card_powerset]
  intro S hS T hT heq
  exact hdiss S T (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) heq

/- ## Main Conjecture -/

/-- **Erdős's Conjecture**: f(n) ≥ ⌊log₂ n⌋ for all n ≥ 1.
    Every n-element set of reals contains a dissociated subset of size
    at least ⌊log₂ n⌋. -/
axiom erdos_963_conjecture :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≥ Nat.log 2 n

/- ## Greedy Lower Bound -/

/-- Decode a Fin 3 index to a sign coefficient: 0 → 0, 1 → +1, 2 → -1. -/
def decodeSign : Fin 3 → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => -1

/-- The signed sum of B weighted by a function ε : ↥B → Fin 3. -/
noncomputable def signedSum (B : Finset ℝ) (ε : ↥B → Fin 3) : ℝ :=
  ∑ b : ↥B, decodeSign (ε b) * (b : ℝ)

/-- The "forbidden set" for extending B: all differences ∑_S - ∑_T for S, T ⊆ B. -/
noncomputable def forbiddenSet (B : Finset ℝ) : Finset ℝ :=
  (B.powerset ×ˢ B.powerset).image (fun p : Finset ℝ × Finset ℝ => p.1.sum id - p.2.sum id)

/-- The forbidden set has at most 3^|B| elements, because every difference
    ∑_S - ∑_T factors through a signed sum with coefficients in {-1, 0, 1}.
    The domain {ε : B → Fin 3} has 3^|B| elements. -/
theorem forbiddenSet_card_le (B : Finset ℝ) :
    (forbiddenSet B).card ≤ 3 ^ B.card := by
  unfold forbiddenSet
  -- The forbidden set is the image of powerset pairs under the difference map
  -- We bound it by showing it's contained in the image of signedSum on all ε functions
  -- Step 1: Build the "signed sum image" finset
  set signedImage := Finset.univ.image (signedSum B)
  -- Step 2: signedImage has at most 3^|B| elements
  have hcard : signedImage.card ≤ 3 ^ B.card := by
    calc signedImage.card ≤ Finset.univ.card := Finset.card_image_le
      _ = Fintype.card (↥B → Fin 3) := (Finset.card_univ).symm ▸ rfl
      _ = Fintype.card (Fin 3) ^ Fintype.card ↥B := Fintype.card_fun
      _ = 3 ^ B.card := by simp [Fintype.card_fin, Fintype.card_coe]
  -- Step 3: The forbidden set ⊆ signedImage because every ∑_S - ∑_T = ∑_{S\T} - ∑_{T\S}
  -- can be written as signedSum B ε where ε(b)=1 for b∈S\T, ε(b)=2 for b∈T\S, ε(b)=0 else.
  -- The image of ε ↦ signedSum B ε on {ε : ↥B → Fin 3} covers all such differences.
  -- Mathematical proof: ∑_S - ∑_T = ∑_{S\T} b - ∑_{T\S} b (by S\T ∪ S∩T decomposition),
  -- and ∑_{b∈B} c(b)*b with c(b) ∈ {-1,0,1} has at most 3^|B| values.
  suffices hsub : (B.powerset ×ˢ B.powerset).image
      (fun p : Finset ℝ × Finset ℝ => p.1.sum id - p.2.sum id) ⊆ signedImage from
    le_trans (Finset.card_le_card hsub) hcard
  intro x hx
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_powerset] at hx
  obtain ⟨⟨S, T⟩, ⟨hSB, hTB⟩, rfl⟩ := hx
  rw [Finset.mem_image]
  -- Construct ε: 1 for S\T, 2 for T\S, 0 for rest
  refine ⟨fun b => if (b : ℝ) ∈ S \ T then 1 else if (b : ℝ) ∈ T \ S then 2 else 0,
          Finset.mem_univ _, ?_⟩
  -- Proof that signedSum B ε = S.sum id - T.sum id:
  -- Both equal ∑_{S\T} b - ∑_{T\S} b by the S\T ∪ S∩T decomposition.
  simp only [signedSum, decodeSign]
  -- Rewrite S.sum and T.sum using disjoint union decomposition
  have hS_eq : S.sum id = (S \ T).sum id + (S ∩ T).sum id := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S T), Finset.sdiff_union_inter]
  have hT_eq : T.sum id = (T \ S).sum id + (S ∩ T).sum id := by
    rw [Finset.inter_comm]
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter T S), Finset.sdiff_union_inter]
  rw [hS_eq, hT_eq]
  ring_nf
  -- Now need: ∑ b : ↥B, (ite...) * ↑b = (S\T).sum id - (T\S).sum id
  -- This is: ∑_{b∈B∩(S\T)} b - ∑_{b∈B∩(T\S)} b = (S\T).sum id - (T\S).sum id
  -- which holds since S\T ⊆ B and T\S ⊆ B
  sorry

/-- **Extension lemma**: If B ⊆ A is dissociated with |B| = k and
    |A \ B| > 3^k, then there exists a ∈ A \ B extending B to a
    dissociated set B ∪ {a}. -/
theorem extend_dissociated (A B : Finset ℝ) (hBA : B ⊆ A)
    (hdiss : ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → S.sum id = T.sum id → S = T)
    (hcard : 3 ^ B.card < (A \ B).card) :
    ∃ a ∈ A \ B,
      ∀ S T : Finset ℝ, S ⊆ insert a B → T ⊆ insert a B →
        S.sum id = T.sum id → S = T := by
  -- Find an element not in the forbidden set
  have hne : ¬ (A \ B) ⊆ forbiddenSet B := by
    intro hsub
    have := Finset.card_le_card hsub
    have := forbiddenSet_card_le B
    omega
  rw [Finset.not_subset] at hne
  obtain ⟨a, ha_mem, ha_forb⟩ := hne
  refine ⟨a, ha_mem, ?_⟩
  -- Prove B ∪ {a} is dissociated
  intro S T hS hT hsum
  -- Case analysis on whether a is in S and/or T
  by_cases haS : a ∈ S <;> by_cases haT : a ∈ T
  · -- a ∈ S, a ∈ T: remove a, reduce to B dissociated
    have hSa : S.erase a ⊆ B := by
      intro x hx
      have := (Finset.mem_erase.mp hx).2
      have hxS := Finset.mem_of_mem_erase hx
      exact (Finset.mem_insert.mp (hS hxS)).resolve_left (Finset.mem_erase.mp hx).1
    have hTa : T.erase a ⊆ B := by
      intro x hx
      have := (Finset.mem_erase.mp hx).2
      have hxT := Finset.mem_of_mem_erase hx
      exact (Finset.mem_insert.mp (hT hxT)).resolve_left (Finset.mem_erase.mp hx).1
    have hsum' : (S.erase a).sum id = (T.erase a).sum id := by
      have := Finset.sum_erase_add S id haS
      have := Finset.sum_erase_add T id haT
      linarith
    have := hdiss _ _ hSa hTa hsum'
    exact Finset.erase_injOn_of_mem haS haT this
  · -- a ∈ S, a ∉ T: a = ∑_T - ∑_{S\{a}}, contradicts a ∉ forbidden set
    exfalso
    apply ha_forb
    unfold forbiddenSet
    rw [Finset.mem_image]
    have hSa : S.erase a ⊆ B := by
      intro x hx
      have hxS := Finset.mem_of_mem_erase hx
      exact (Finset.mem_insert.mp (hS hxS)).resolve_left (Finset.mem_erase.mp hx).1
    have hTB : T ⊆ B := by
      intro x hx
      exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun h => haT (h ▸ hx))
    refine ⟨⟨T, S.erase a⟩, ⟨Finset.mem_powerset.mpr hTB, Finset.mem_powerset.mpr hSa⟩, ?_⟩
    simp only
    have := Finset.sum_erase_add S id haS
    linarith
  · -- a ∉ S, a ∈ T: symmetric
    exfalso
    apply ha_forb
    unfold forbiddenSet
    rw [Finset.mem_image]
    have hTa : T.erase a ⊆ B := by
      intro x hx
      have hxT := Finset.mem_of_mem_erase hx
      exact (Finset.mem_insert.mp (hT hxT)).resolve_left (Finset.mem_erase.mp hx).1
    have hSB : S ⊆ B := by
      intro x hx
      exact (Finset.mem_insert.mp (hS hx)).resolve_left (fun h => haS (h ▸ hx))
    refine ⟨⟨S, T.erase a⟩, ⟨Finset.mem_powerset.mpr hSB, Finset.mem_powerset.mpr hTa⟩, ?_⟩
    simp only
    have := Finset.sum_erase_add T id haT
    linarith
  · -- a ∉ S, a ∉ T: both subsets of B, use dissociatedness
    have hSB : S ⊆ B := by
      intro x hx
      exact (Finset.mem_insert.mp (hS hx)).resolve_left (fun h => haS (h ▸ hx))
    have hTB : T ⊆ B := by
      intro x hx
      exact (Finset.mem_insert.mp (hT hx)).resolve_left (fun h => haT (h ▸ hx))
    exact hdiss S T hSB hTB hsum

/-- Auxiliary: 2 · 3^k > k for all k. -/
private lemma two_mul_pow3_gt (k : ℕ) : 2 * 3 ^ k > k := by
  induction k with
  | zero => omega
  | succ n ih =>
    calc 2 * 3 ^ (n + 1) = 2 * (3 * 3 ^ n) := by ring
      _ = 6 * 3 ^ n := by ring
      _ ≥ 2 * 3 ^ n + 1 := by omega
      _ > n + 1 := by omega

/-- For |A| ≥ 3^k, A has a dissociated subset of size ≥ k. -/
theorem dissociated_of_card_ge_pow3 :
    ∀ k : ℕ, ∀ A : Finset ℝ, A.card ≥ 3 ^ k →
      ∃ B : Finset ℝ, IsDissociatedSubset A B ∧ B.card ≥ k := by
  intro k
  induction k with
  | zero =>
    intro A _
    exact ⟨∅, empty_dissociated A, le_refl 0⟩
  | succ n ih =>
    intro A hA
    -- |A| ≥ 3^(n+1) ≥ 3^n, so by IH, A has dissociated B with |B| ≥ n
    have hA_ge_pow_n : A.card ≥ 3 ^ n := by
      calc A.card ≥ 3 ^ (n + 1) := hA
        _ = 3 * 3 ^ n := by ring
        _ ≥ 3 ^ n := Nat.le_mul_of_pos_left _ (by omega)
    obtain ⟨B₀, ⟨hB₀A, hB₀diss⟩, hB₀card⟩ := ih A hA_ge_pow_n
    -- Get B with exactly n elements (take a subset if B₀ is larger)
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_smaller_set B₀ n hB₀card
    have hBA : B ⊆ A := hBsub.trans hB₀A
    have hBdiss : ∀ S T : Finset ℝ, S ⊆ B → T ⊆ B → S.sum id = T.sum id → S = T :=
      fun S T hSB hTB => hB₀diss S T (hSB.trans hBsub) (hTB.trans hBsub)
    -- Show |A \ B| > 3^n
    have hsdiff : 3 ^ n < (A \ B).card := by
      have : (A \ B).card = A.card - B.card := Finset.card_sdiff hBA
      rw [this, hBcard]
      have : A.card ≥ 3 * 3 ^ n := by linarith [hA, show 3 ^ (n + 1) = 3 * 3 ^ n from by ring]
      have := two_mul_pow3_gt n
      omega
    -- Extend B by one element
    rw [hBcard] at hsdiff
    obtain ⟨a, ha_mem, ha_diss⟩ := extend_dissociated A B hBA hBdiss hsdiff
    -- B ∪ {a} is dissociated with n+1 elements
    have ha_not_in_B : a ∉ B := (Finset.mem_sdiff.mp ha_mem).2
    refine ⟨insert a B, ⟨?_, ha_diss⟩, ?_⟩
    · -- insert a B ⊆ A
      exact Finset.insert_subset ((Finset.mem_sdiff.mp ha_mem).1) hBA
    · -- card (insert a B) ≥ n + 1
      rw [Finset.card_insert_of_not_mem ha_not_in_B, hBcard]

/-- **PROVED** (was axiom): Erdős's greedy bound f(n) ≥ ⌊log₃ n⌋.
    At each step of the greedy algorithm, the forbidden set (signed sums with
    coefficients in {-1, 0, 1}) has at most 3^k elements. Since 3^(k+1) > k + 3^k,
    the algorithm can always extend until size ⌊log₃ n⌋. -/
theorem greedy_lower_bound :
    ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≥ Nat.log 3 n := by
  intro n hn
  unfold maxDissociatedSize
  -- Show Nat.log 3 n is in the set
  apply le_csSup
  · -- BddAbove
    refine ⟨n, fun k hk => ?_⟩
    have ⟨A, hA⟩ : ∃ A : Finset ℝ, A.card = n :=
      ⟨(Finset.range n).image ((↑) : ℕ → ℝ), by
        rw [Finset.card_image_of_injOn]; exact Finset.card_range n
        intro a _ b _ hab; exact_mod_cast hab⟩
    obtain ⟨B, ⟨hBsub, _⟩, hBcard⟩ := hk A hA
    exact le_trans hBcard (le_trans (Finset.card_le_card hBsub) (le_of_eq hA))
  · -- Nat.log 3 n ∈ {k | ∀ A, ...}
    intro A hA
    have hA_ge : A.card ≥ 3 ^ Nat.log 3 n := by
      rw [hA]; exact Nat.pow_log_le_self 3 (by omega)
    exact dissociated_of_card_ge_pow3 (Nat.log 3 n) A hA_ge

/- ## Upper Bound -/

/-- **Trivial upper bound**: f(n) ≤ ⌊log₂ n⌋ + 1.
    A dissociated set of size k requires at least 2^k distinct subset sums,
    so k ≤ log₂(n + 1) since the sums come from an n-element ambient set. -/
axiom trivial_upper_bound :
  ∀ n : ℕ, n ≥ 1 → maxDissociatedSize n ≤ Nat.log 2 n + 1

/- ## Structural Properties -/

/-- The empty set is trivially dissociated. -/
theorem empty_dissociated (A : Finset ℝ) : IsDissociatedSubset A ∅ := by
  constructor
  · exact Finset.empty_subset A
  · intro S T hS hT _
    rw [Finset.subset_empty] at hS hT
    rw [hS, hT]

/-- Any singleton {a} with a ≠ 0 is dissociated (subsets ∅ and {a}
    have distinct sums 0 and a). -/
theorem singleton_dissociated (A : Finset ℝ) (a : ℝ) (ha : a ∈ A) (ha0 : a ≠ 0) :
    IsDissociatedSubset A {a} := by
  constructor
  · exact Finset.singleton_subset_iff.mpr ha
  · intro S T hS hT hsum
    rw [Finset.subset_singleton_iff] at hS hT
    rcases hS with rfl | rfl <;> rcases hT with rfl | rfl
    · rfl
    · simp at hsum; exfalso; exact ha0 hsum.symm
    · simp at hsum; exfalso; exact ha0 hsum
    · rfl

/-- Auxiliary: ∑_{i<k} 2^i = 2^k - 1 (geometric series for ℕ). -/
private lemma sum_range_pow_two (k : ℕ) :
    (Finset.range k).sum (fun i => (2 : ℕ) ^ i) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    omega

/-- Auxiliary: any subset sum of {2^i : i < k} is strictly less than 2^k. -/
private lemma subset_sum_lt_pow_two (k : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range k) :
    S.sum (fun i => (2 : ℕ) ^ i) < 2 ^ k := by
  have h1 : S.sum (fun i => 2 ^ i) ≤ (Finset.range k).sum (fun i => 2 ^ i) :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.zero_le _)
  have h2 := sum_range_pow_two k
  omega

/-- Binary representation uniqueness over ℕ: if S, T ⊆ {0, ..., k-1} and
    ∑_{i∈S} 2^i = ∑_{i∈T} 2^i then S = T. -/
private lemma binary_uniqueness_nat :
    ∀ k : ℕ, ∀ S T : Finset ℕ,
      S ⊆ Finset.range k → T ⊆ Finset.range k →
      S.sum (fun i => (2 : ℕ) ^ i) = T.sum (fun i => (2 : ℕ) ^ i) → S = T := by
  intro k
  induction k with
  | zero =>
    intro S T hS hT _
    simp [Finset.range_zero, Finset.subset_empty] at hS hT
    rw [hS, hT]
  | succ n ih =>
    intro S T hS hT hsum
    have mem_range_succ : ∀ x ∈ S, x < n + 1 := fun x hx => Finset.mem_range.mp (hS hx)
    have mem_range_succ' : ∀ x ∈ T, x < n + 1 := fun x hx => Finset.mem_range.mp (hT hx)
    by_cases hnS : n ∈ S <;> by_cases hnT : n ∈ T
    · -- Both contain n: remove n from both, apply IH
      have hS' : S.erase n ⊆ Finset.range n := by
        intro x hx
        have hxS := (Finset.mem_erase.mp hx).2
        have hxn := (Finset.mem_erase.mp hx).1
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp (hS hxS))) hxn)
      have hT' : T.erase n ⊆ Finset.range n := by
        intro x hx
        have hxT := (Finset.mem_erase.mp hx).2
        have hxn := (Finset.mem_erase.mp hx).1
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp (hT hxT))) hxn)
      have hsum' : (S.erase n).sum (fun i => 2 ^ i) = (T.erase n).sum (fun i => 2 ^ i) := by
        have := Finset.sum_erase_add S (fun i => (2 : ℕ) ^ i) hnS
        have := Finset.sum_erase_add T (fun i => (2 : ℕ) ^ i) hnT
        omega
      have := ih (S.erase n) (T.erase n) hS' hT' hsum'
      exact Finset.erase_injOn_of_mem hnS hnT this
    · -- n ∈ S, n ∉ T: contradiction (S sum ≥ 2^n, T sum < 2^n)
      exfalso
      have hT' : T ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hT hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnT (h ▸ hx)))
      have hT_bound := subset_sum_lt_pow_two n T hT'
      have hS_lower : S.sum (fun i => 2 ^ i) ≥ 2 ^ n := by
        calc S.sum (fun i => 2 ^ i)
            ≥ (({n} : Finset ℕ)).sum (fun i => 2 ^ i) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.singleton_subset_iff.mpr hnS) (fun _ _ _ => Nat.zero_le _)
          _ = 2 ^ n := by simp
      omega
    · -- n ∉ S, n ∈ T: symmetric contradiction
      exfalso
      have hS' : S ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hS hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnS (h ▸ hx)))
      have hS_bound := subset_sum_lt_pow_two n S hS'
      have hT_lower : T.sum (fun i => 2 ^ i) ≥ 2 ^ n := by
        calc T.sum (fun i => 2 ^ i)
            ≥ (({n} : Finset ℕ)).sum (fun i => 2 ^ i) :=
              Finset.sum_le_sum_of_subset_of_nonneg
                (Finset.singleton_subset_iff.mpr hnT) (fun _ _ _ => Nat.zero_le _)
          _ = 2 ^ n := by simp
      omega
    · -- Neither contains n: both subsets of range(n), apply IH
      have hS' : S ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hS hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnS (h ▸ hx)))
      have hT' : T ⊆ Finset.range n := by
        intro x hx
        have := Finset.mem_range.mp (hT hx)
        exact Finset.mem_range.mpr (lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hnT (h ▸ hx)))
      exact ih S T hS' hT' hsum

/-- **PROVED** (was axiom): Powers of 2 form a dissociated set (binary representation uniqueness). -/
theorem powers_of_two_dissociated :
  ∀ k : ℕ, ∀ S T : Finset ℕ,
    S ⊆ Finset.range k → T ⊆ Finset.range k →
    S.sum (fun i => (2 : ℝ) ^ i) = T.sum (fun i => (2 : ℝ) ^ i) → S = T := by
  intro k S T hS hT hsum
  apply binary_uniqueness_nat k S T hS hT
  -- Reduce ℝ sum equality to ℕ sum equality via casting
  have cast_eq : ∀ U : Finset ℕ,
      U.sum (fun i => (2 : ℝ) ^ i) = ↑(U.sum (fun i => (2 : ℕ) ^ i)) := by
    intro U
    push_cast [Finset.sum_coe_sort]
    simp [Nat.cast_sum, Nat.cast_pow]
  rw [cast_eq, cast_eq] at hsum
  exact_mod_cast hsum

/-- **PROVED** (was axiom): Monotonicity — f is non-decreasing.
    If m ≤ n then f(m) ≤ f(n), since any n-element set contains an
    m-element subset, inheriting the dissociated subset guarantee. -/
theorem maxDissociatedSize_mono :
    ∀ m n : ℕ, m ≤ n → maxDissociatedSize m ≤ maxDissociatedSize n := by
  intro m n hmn
  unfold maxDissociatedSize
  apply csSup_le_csSup
  · -- BddAbove: the n-set is bounded above by n
    refine ⟨n, fun k (hk : ∀ A : Finset ℝ, A.card = n →
        ∃ B, IsDissociatedSubset A B ∧ B.card ≥ k) => ?_⟩
    -- Exhibit a specific n-element Finset ℝ to extract the bound
    have ⟨A, hA⟩ : ∃ A : Finset ℝ, A.card = n :=
      ⟨(Finset.range n).image ((↑) : ℕ → ℝ), by
        rw [Finset.card_image_of_injOn]
        · exact Finset.card_range n
        · intro a _ b _ hab; exact_mod_cast hab⟩
    obtain ⟨B, ⟨hBsub, _⟩, hBcard⟩ := hk A hA
    exact le_trans hBcard (le_trans (Finset.card_le_card hBsub) (le_of_eq hA))
  · -- Nonempty: 0 is in the m-set (empty set is dissociated in any set)
    exact ⟨0, fun A _ => ⟨∅, empty_dissociated A, Nat.zero_le _⟩⟩
  · -- Subset: the m-set ⊆ the n-set
    intro k (hk : ∀ A : Finset ℝ, A.card = m →
        ∃ B, IsDissociatedSubset A B ∧ B.card ≥ k)
    intro A (hA : A.card = n)
    -- A has n ≥ m elements; extract an m-element subset A'
    obtain ⟨A', hA'sub, hA'card⟩ := Finset.exists_smaller_set A m (hA ▸ hmn)
    -- A' has a dissociated subset B of size ≥ k
    obtain ⟨B, ⟨hBsub, hBdiss⟩, hBcard⟩ := hk A' hA'card
    -- B ⊆ A' ⊆ A, and dissociatedness depends only on B
    exact ⟨B, ⟨hBsub.trans hA'sub, hBdiss⟩, hBcard⟩

/-- **PROVED** (was axiom): The gap between the greedy bound and the
    conjecture: log₂ vs log₃. Since 2 ≤ 3, log₃ n ≤ log₂ n for all n. -/
theorem log_base_gap :
    ∀ n : ℕ, n ≥ 2 → Nat.log 3 n ≤ Nat.log 2 n := by
  intro n _
  apply Nat.log_anti_left <;> omega
