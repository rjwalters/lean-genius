/-
  Aristotle targets for Erdos840 (Quasi-Sidon Subsets)
  Routine supporting lemmas for automated proof search.
  See Erdos840Problem.lean for the main formalization.

  These lemmas provide building blocks for quasi-Sidon set analysis:
  - IsSidon basic properties (distinct sums, sumset cardinality)
  - IsQuasiSidon structural helpers
  - Sidon set existence bounds
  - Arithmetic for sumset bounds (n*(n+1)/2)
  - sqrt(N) bound arithmetic
-/
import Mathlib

open Finset Real

namespace Erdos840.Aristotle

variable {α : Type*} [DecidableEq α] [AddCommMonoid α]

/-
  ## Section 1: Sumset Arithmetic
-/

/-- Helper: 2 * C(n,2) = n*(n-1). Avoids division in inductive step. -/
private lemma two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => simp
    | succ m =>
      simp only [Nat.succ_sub_one] at ih ⊢
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.mul_add]
      -- Goal: 2 * (m+1) + 2 * (m+1).choose 2 = (m+2) * (m+1)
      -- ih : 2 * (m+1).choose 2 = (m+1) * m
      have key : (m + 2) * (m + 1) = 2 * (m + 1) + (m + 1) * m := by ring
      linarith

/-- C(n,2) = n*(n-1)/2 for natural numbers -/
lemma choose_two_formula (n : ℕ) : n.choose 2 = n * (n - 1) / 2 := by
  have h := two_mul_choose_two n
  omega

/-- n*(n+1)/2 = C(n,2) + n -/
lemma triangular_eq_choose_plus (n : ℕ) : n * (n + 1) / 2 = n.choose 2 + n := by
  have h2mc := two_mul_choose_two n
  have hdvd : 2 ∣ n * (n + 1) := by
    rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨k * (2 * k + 1), by ring⟩
    · exact ⟨(2 * k + 1) * (k + 1), by ring⟩
  have hnn1 : n * (n + 1) / 2 * 2 = n * (n + 1) := Nat.div_mul_cancel hdvd
  cases n with
  | zero => simp
  | succ m =>
    simp only [Nat.succ_sub_one] at h2mc
    -- h2mc : 2 * (m+1).choose 2 = (m+1) * m
    -- hnn1 : (m+1)*(m+1+1)/2 * 2 = (m+1)*(m+1+1)  [syntactically]
    -- Goal : (m+1)*(m+1+1)/2 = (m+1).choose 2 + (m+1)
    -- Key: use (m+1+1) form throughout to match hnn1 exactly, then omega
    have hmul : (m + 1) * (m + 1 + 1) / 2 * 2 = 2 * ((m + 1).choose 2 + (m + 1)) :=
      calc (m + 1) * (m + 1 + 1) / 2 * 2
          = (m + 1) * (m + 1 + 1)                    := hnn1
        _ = (m + 1) * m + 2 * (m + 1)               := by ring
        _ = 2 * (m + 1).choose 2 + 2 * (m + 1)      := by linarith
        _ = 2 * ((m + 1).choose 2 + (m + 1))        := by ring
    omega

/-- For A with |A| = k, the number of ordered pairs (a,b) with a ≠ b is k*(k-1) -/
lemma card_ordered_pairs (A : Finset ℕ) :
    ((A ×ˢ A).filter fun p => p.1 ≠ p.2).card = A.card * (A.card - 1) := by
  have heq : (A ×ˢ A).filter (fun p => p.1 ≠ p.2) = A.offDiag := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag]
    exact ⟨fun ⟨⟨ha, hb⟩, hne⟩ => ⟨ha, hb, hne⟩,
           fun ⟨ha, hb, hne⟩ => ⟨⟨ha, hb⟩, hne⟩⟩
  rw [heq, Finset.offDiag_card]
  -- Goal: A.card * A.card - A.card = A.card * (A.card - 1)
  -- offDiag_card gives n*n - n form; need to show this equals n*(n-1)
  cases h : A.card with
  | zero => simp
  | succ n =>
    simp only [Nat.succ_sub_one]
    -- Goal: (n+1)*(n+1) - (n+1) = (n+1)*n
    have hrw : (n + 1) * (n + 1) = (n + 1) * n + (n + 1) := by ring
    omega

/-
  ## Section 2: IsSidon Properties
-/

/-- A Sidon set has all pairwise sums distinct -/
def IsSidon' (A : Finset ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → a ≤ b → c ≤ d → (a = c ∧ b = d)

/-- The sumset of a Finset -/
def sumset' (A : Finset ℕ) : Finset ℕ :=
  (A ×ˢ A).image fun p => p.1 + p.2

/-- Sumset contains both singletons and pairwise sums -/
lemma mem_sumset (A : Finset ℕ) (a b : ℕ) (ha : a ∈ A) (hb : b ∈ A) :
    a + b ∈ sumset' A := by
  simp only [sumset', Finset.mem_image, Finset.mem_product]
  exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- Singleton in A implies 2*a in sumset -/
lemma two_mul_mem_sumset (A : Finset ℕ) (a : ℕ) (ha : a ∈ A) :
    2 * a ∈ sumset' A := by
  rw [two_mul]
  exact mem_sumset A a a ha ha

/-- For Sidon set, different pairs give different sums -/
lemma sidon_distinct_sums (A : Finset ℕ) (hS : IsSidon' A)
    (a b c d : ℕ) (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a < b) (hcd : c < d) (hne : (a, b) ≠ (c, d)) : a + b ≠ c + d := by
  intro h_eq
  have := hS a b c d ha hb hc hd h_eq hab.le hcd.le
  exact hne (Prod.ext this.1 this.2)

/-
  ## Section 3: Sumset Size Bounds
-/

/-- The number of strict pairs (a, b) ∈ A × A with a < b is C(|A|, 2).

    Proof strategy (swap-bijection argument, avoiding 2-element subsets):
    Let L = strict-lt pairs, G = strict-gt pairs. Then
      * L ∪ G = offDiag (= ≠-pairs), disjoint
      * |L| = |G| via the swap bijection (a, b) ↦ (b, a)
      * |offDiag| = |A| * (|A| - 1) by `card_ordered_pairs`
    Hence 2 * |L| = |A| * (|A| - 1) = 2 * C(|A|, 2) by `two_mul_choose_two`,
    so |L| = C(|A|, 2). -/
theorem unordered_pairs_card (A : Finset ℕ) :
    ((A ×ˢ A).filter fun p => p.1 < p.2).card = A.card.choose 2 := by
  set L := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 < p.2) with hL_def
  set G := (A ×ˢ A).filter (fun p : ℕ × ℕ => p.2 < p.1) with hG_def
  -- Disjointness: a < b and b < a cannot both hold
  have h_disj : Disjoint L G := by
    rw [Finset.disjoint_left]
    rintro p hLp hGp
    simp only [hL_def, hG_def, Finset.mem_filter] at hLp hGp
    omega
  -- L ∪ G coincides with the ≠-filter, whose card is given by `card_ordered_pairs`
  have h_union_card : (L ∪ G).card = A.card * (A.card - 1) := by
    have h_eq : L ∪ G = (A ×ˢ A).filter (fun p : ℕ × ℕ => p.1 ≠ p.2) := by
      ext p
      simp only [hL_def, hG_def, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_or_gt_of_ne h2 with hlt | hgt
        · exact Or.inl ⟨h1, hlt⟩
        · exact Or.inr ⟨h1, hgt⟩
    rw [h_eq, card_ordered_pairs]
  -- Swap bijection: G is the image of L under (a, b) ↦ (b, a)
  have h_swap_inj : Function.Injective (fun p : ℕ × ℕ => (p.2, p.1)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.2 h.1
  have h_G_eq : G = L.image (fun p : ℕ × ℕ => (p.2, p.1)) := by
    ext ⟨a, b⟩
    simp only [hG_def, hL_def, Finset.mem_filter, Finset.mem_product,
               Finset.mem_image]
    constructor
    · rintro ⟨⟨ha, hb⟩, hgt⟩
      exact ⟨(b, a), ⟨⟨hb, ha⟩, hgt⟩, rfl⟩
    · rintro ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, hlt⟩, h_eq⟩
      obtain ⟨h_d_a, h_c_b⟩ : d = a ∧ c = b := Prod.mk.inj h_eq
      subst h_d_a; subst h_c_b
      exact ⟨⟨hd, hc⟩, hlt⟩
  have h_card_eq : G.card = L.card := by
    rw [h_G_eq]; exact Finset.card_image_of_injective L h_swap_inj
  -- Combine: 2 * |L| = |A| * (|A| - 1) = 2 * choose 2
  have h_two_L : 2 * L.card = A.card * (A.card - 1) := by
    rw [Finset.card_union_of_disjoint h_disj, h_card_eq] at h_union_card
    omega
  have h_two_choose := two_mul_choose_two A.card
  omega

/-- Sumset is nonempty when A is nonempty -/
lemma sumset_nonempty (A : Finset ℕ) (hA : A.Nonempty) : (sumset' A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨a + a, mem_sumset A a a ha ha⟩

/-- Sumset card ≥ |A| (the diagonal 2*a are all distinct for distinct a) -/
lemma sumset_card_ge (A : Finset ℕ) : (sumset' A).card ≥ A.card := by
  calc A.card = (A.image (fun a => 2 * a)).card :=
        (Finset.card_image_of_injective A (fun a b h => by omega)).symm
    _ ≤ (sumset' A).card := Finset.card_le_card (fun x hx => by
        simp only [Finset.mem_image] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        rw [two_mul]
        simp only [sumset', Finset.mem_image, Finset.mem_product]
        exact ⟨(a, a), ⟨ha, ha⟩, rfl⟩)

/-
  ## Section 4: sqrt(N) Arithmetic
-/

/-- (sqrt N)^2 ≤ N -/
lemma sqrt_sq_le (N : ℕ) : (Nat.sqrt N) ^ 2 ≤ N :=
  Nat.sqrt_le' N

/-- sqrt N ≤ N for N ≥ 1 -/
lemma sqrt_le_self (N : ℕ) (hN : N ≥ 1) : Real.sqrt N ≤ N := by
  have hN' : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h : Real.sqrt N ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  rwa [Real.sqrt_sq hN'] at h

/-- sqrt 3 < 2 -/
lemma sqrt3_lt_two : Real.sqrt 3 < 2 := by
  rw [show (2 : ℝ) = Real.sqrt 4 by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- 2 / sqrt 3 > 1 -/
lemma two_div_sqrt3_gt_one : 2 / Real.sqrt 3 > 1 := by
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [gt_iff_lt, ← sub_pos]
  have heq : (2 : ℝ) / Real.sqrt 3 - 1 = (2 - Real.sqrt 3) / Real.sqrt 3 := by
    field_simp [h3.ne']
  rw [heq]
  apply div_pos
  · linarith [sqrt3_lt_two]
  · exact h3

/-- Sidon set cardinality bound: |A| ≤ sqrt(2*N) + 1 for A ⊆ {1..N}

    Proof sketch (differences argument):
    The C(k,2) positive differences {a-b : a>b, a,b ∈ A} are all distinct
    (Sidon property implies distinct differences) and lie in {1,...,N-1},
    giving C(k,2) ≤ N-1, so k*(k-1)/2 ≤ N, k*(k-1) ≤ 2N, and k ≤ sqrt(2N) + 1.

    Note: the original statement sqrt(N) + 1 is incorrect for large N;
    the correct bound from the differences argument is sqrt(2*N) + 1. -/
theorem sidon_card_le_sqrt (A : Finset ℕ) (N : ℕ) (hN : N ≥ 1)
    (hA : ∀ a ∈ A, a ≤ N) (hS : IsSidon' A) :
    (A.card : ℝ) ≤ Real.sqrt (2 * N) + 1 := by sorry

end Erdos840.Aristotle
