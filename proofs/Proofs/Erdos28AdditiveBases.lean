/-
  Erdős Problem #28: Erdős-Turán Conjecture on Additive Bases

  Source: https://erdosproblems.com/28
  Status: OPEN
  Prize: $500

  Statement:
  If A ⊆ ℕ is such that A + A contains all but finitely many integers,
  then lim sup r_A(n) = ∞, where r_A(n) = |{(a,b) ∈ A×A : a + b = n}|.

  Key Definition:
  The **representation function** r_A(n) counts the number of ways to write n
  as a sum of two elements from set A.

  Stronger Conjectures:
  1. lim sup r_A(n) / log(n) > 0  (Erdős-Turán 1941)
  2. The hypothesis |A ∩ [1,N]| >> N^{1/2} suffices

  Known Results:
  - Grekos et al. (2003): r_A(n) ≥ 6 for infinitely many n
  - Borwein et al.: r_A(n) ≥ 8 for infinitely many n
  - There exist bases with bounded representations (Sidon-type constructions don't apply here)

  What We Can Do:
  1. Define representation function r_A(n)
  2. Define asymptotic basis (A+A contains all large n)
  3. State the conjecture formally
  4. Prove basic properties
  5. Exhibit constructions with unbounded representations

  Tags: number-theory, additive-combinatorics, erdos-problem, prize-problem
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Proofs.Erdos340SidonErdosTuran

namespace Erdos28

open Finset Filter

/- ## Part I: Representation Function -/

/-- The representation function r_A(n): counts pairs (a,b) ∈ A×A with a + b = n.
    We count ordered pairs, so r_A(n) counts each representation {a,b} twice if a ≠ b,
    and once if a = b. -/
noncomputable def repFunc (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}

/-- Alternative: unordered representation count (pairs with a ≤ b). -/
noncomputable def repFuncUnordered (A : Set ℕ) (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n}

/-- For finite sets, we can use Finset cardinality. -/
def repFuncFinset (A : Finset ℕ) (n : ℕ) : ℕ :=
  (A.product A).filter (fun p => p.1 + p.2 = n) |>.card

/- ## Part II: Sumset and Asymptotic Basis -/

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def sumset (A : Set ℕ) : Set ℕ :=
  {n | ∃ a b, a ∈ A ∧ b ∈ A ∧ n = a + b}

/-- A is an asymptotic additive basis of order 2 if A+A contains all sufficiently large integers. -/
def IsAsymptoticBasis (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n ≥ N₀, n ∈ sumset A

/-- Equivalent: A+A misses only finitely many integers. -/
def IsAsymptoticBasis' (A : Set ℕ) : Prop :=
  (sumset A)ᶜ.Finite

/-- The two definitions are equivalent.
    Proof sketch: If A+A contains [N₀, ∞), the complement is ⊆ {0,...,N₀-1}, hence finite.
    Conversely, if the complement is finite, it has a maximum M, so [M+1, ∞) ⊆ A+A. -/
theorem isAsymptoticBasis_iff (A : Set ℕ) :
    IsAsymptoticBasis A ↔ IsAsymptoticBasis' A := by
  constructor
  · intro ⟨N₀, h⟩
    unfold IsAsymptoticBasis'
    have hsub : (sumset A)ᶜ ⊆ Finset.range N₀ := fun n hn => by
      simp only [Set.mem_compl_iff] at hn
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra h'
      push_neg at h'
      exact hn (h n h')
    exact Set.Finite.subset (Finset.finite_toSet _) hsub
  · intro hfin
    -- The complement is finite, hence bounded, so has a maximum.
    -- All n beyond that maximum are in A+A.
    by_cases h : (sumset A)ᶜ.Nonempty
    · have hbdd : BddAbove (sumset A)ᶜ := hfin.bddAbove
      let M := sSup (sumset A)ᶜ
      use M + 1
      intro n hn
      by_contra hn'
      have hn_compl : n ∈ (sumset A)ᶜ := hn'
      have h_le : n ≤ M := le_csSup hbdd hn_compl
      omega
    · -- Complement is empty
      rw [Set.not_nonempty_iff_eq_empty] at h
      use 0
      intro n _
      rw [← Set.notMem_compl_iff, h]
      exact Set.notMem_empty n

/- ## Part III: Basic Properties -/

/-- The set of pairs summing to n is finite (both components bounded by n). -/
lemma pairs_summing_finite (A : Set ℕ) (n : ℕ) :
    {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}.Finite := by
  apply Set.Finite.subset
  · exact (Set.finite_Iio (n + 1)).prod (Set.finite_Iio (n + 1))
  · intro ⟨a, b⟩ ⟨_, _, hab⟩
    simp only [Set.mem_prod, Set.mem_Iio]
    constructor <;> omega

/-- If n ∈ A+A then r_A(n) ≥ 1. -/
theorem repFunc_pos_of_mem_sumset (A : Set ℕ) (n : ℕ) (h : n ∈ sumset A) :
    repFunc A n ≥ 1 := by
  obtain ⟨a, b, ha, hb, heq⟩ := h
  unfold repFunc
  have hpair : (a, b) ∈ {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} := by
    simp only [Set.mem_setOf_eq]
    exact ⟨ha, hb, heq.symm⟩
  have hne : {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n}.Nonempty := ⟨(a, b), hpair⟩
  have hfin := pairs_summing_finite A n
  have hpos : 0 < Set.ncard {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} := by
    rw [Set.ncard_pos hfin]
    exact hne
  omega

/-- If A is infinite and 0 ∈ A, then r_A(n) ≥ 1 for all n ∈ A. -/
theorem repFunc_pos_of_zero_mem (A : Set ℕ) (h0 : 0 ∈ A) (n : ℕ) (hn : n ∈ A) :
    repFunc A n ≥ 1 := by
  apply repFunc_pos_of_mem_sumset
  exact ⟨0, n, h0, hn, by ring⟩

/-- For Sidon sets, r_A(n) ≤ 2 for all n. -/
def IsSidon (A : Set ℕ) : Prop :=
  ∀ a b c d, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a + b = c + d → ({a, b} : Set ℕ) = {c, d}

/-- Sidon sets have bounded representation.
    Proof: For Sidon sets, if a + b = c + d then {a,b} = {c,d}.
    So at most one unordered pair sums to n, giving at most 2 ordered pairs. -/
theorem sidon_repFunc_bounded (A : Set ℕ) (hS : IsSidon A) :
    ∀ n, repFunc A n ≤ 2 := by
  intro n
  unfold repFunc
  set S := {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 + p.2 = n} with hS_def
  have hfin : S.Finite := pairs_summing_finite A n
  by_cases hne : S.Nonempty
  · -- S is nonempty, pick an element (a, b)
    obtain ⟨⟨a, b⟩, ha_mem, hb_mem, hab⟩ := hne
    -- Any other element (c, d) must satisfy {c,d} = {a,b}
    have hS_sub : S ⊆ {(a, b), (b, a)} := by
      intro ⟨c, d⟩ ⟨hc_mem, hd_mem, hcd⟩
      have heq : ({c, d} : Set ℕ) = {a, b} := by
        apply hS c d a b hc_mem hd_mem ha_mem hb_mem
        omega
      simp only [Set.mem_insert_iff, Prod.mk.injEq]
      -- From {c, d} = {a, b}, either (c,d) = (a,b) or (c,d) = (b,a)
      have hc_in : c ∈ ({a, b} : Set ℕ) := by rw [← heq]; exact Set.mem_insert c {d}
      have hd_in : d ∈ ({a, b} : Set ℕ) := by rw [← heq]; exact Set.mem_insert_of_mem c rfl
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc_in hd_in
      -- c ∈ {a, b} and d ∈ {a, b} with c + d = a + b = n
      cases hc_in with
      | inl hca =>
        cases hd_in with
        | inl hda => left; refine ⟨hca, ?_⟩; subst hca hda; omega
        | inr hdb => left; exact ⟨hca, hdb⟩
      | inr hcb =>
        cases hd_in with
        | inl hda =>
          -- c = b, d = a
          right; simp only [Set.mem_singleton_iff, Prod.mk.injEq]
          exact ⟨hcb, hda⟩
        | inr hdb =>
          -- c = b, d = b: c + d = 2b = n and a + b = n, so a = b
          left; subst hcb hdb; constructor <;> omega
    have hcard : S.ncard ≤ ({(a, b), (b, a)} : Set (ℕ × ℕ)).ncard :=
      Set.ncard_le_ncard hS_sub (Set.toFinite _)
    have htwo : ({(a, b), (b, a)} : Set (ℕ × ℕ)).ncard ≤ 2 := by
      have h1 : ({(a, b), (b, a)} : Set (ℕ × ℕ)).ncard ≤ 1 + 1 := by
        rw [Set.insert_eq]
        calc ({(a, b)} ∪ {(b, a)} : Set (ℕ × ℕ)).ncard
            ≤ ({(a, b)} : Set (ℕ × ℕ)).ncard + ({(b, a)} : Set (ℕ × ℕ)).ncard :=
              Set.ncard_union_le _ _
          _ = 1 + 1 := by simp only [Set.ncard_singleton]
      omega
    exact hcard.trans htwo
  · -- S is empty
    simp only [Set.not_nonempty_iff_eq_empty] at hne
    have hS_empty : S = ∅ := by rw [hS_def]; exact hne
    rw [hS_empty]
    simp only [Set.ncard_empty, Nat.zero_le]

/- ## Part IV: The Main Conjecture -/

/-- **Erdős-Turán Conjecture** (Weak Form, 1941)

    If A is an asymptotic basis of order 2, then the representation function
    is unbounded: lim sup r_A(n) = ∞.

    Equivalently: for every k, there exists n with r_A(n) > k. -/
def erdos_turan_weak : Prop :=
  ∀ A : Set ℕ, IsAsymptoticBasis A → ∀ k : ℕ, ∃ n : ℕ, repFunc A n > k

/-- **Erdős-Turán Conjecture** (Strong Form)

    If A is an asymptotic basis of order 2, then
    lim sup r_A(n) / log(n) > 0. -/
def erdos_turan_strong : Prop :=
  ∀ A : Set ℕ, IsAsymptoticBasis A →
    ∃ c : ℝ, c > 0 ∧ ∀ M : ℕ, ∃ n > M, repFunc A n > c * Real.log n

/-- **Erdős Problem #28** (Official Statement)

    Prize: $500 for proof or disproof. -/
def erdos_28 : Prop := erdos_turan_weak

/- ## Part V: Known Partial Results -/

/-- Grekos et al. (2003): For any asymptotic basis A, r_A(n) ≥ 6 for infinitely many n. -/
axiom grekos_lower_bound :
  ∀ A : Set ℕ, IsAsymptoticBasis A → ∀ M : ℕ, ∃ n > M, repFunc A n ≥ 6

/-- Borwein et al.: Improved to r_A(n) ≥ 8 infinitely often. -/
axiom borwein_lower_bound :
  ∀ A : Set ℕ, IsAsymptoticBasis A → ∀ M : ℕ, ∃ n > M, repFunc A n ≥ 8

/- ## Part VI: Examples -/

/-- The even numbers {0, 2, 4, 6, ...} form a basis for even numbers. -/
def evens : Set ℕ := {n | Even n}

/-- Every even number is in evens + evens. -/
theorem evens_sumset : sumset evens = evens := by
  ext n
  constructor
  · intro ⟨a, b, ha, hb, heq⟩
    obtain ⟨ka, hka⟩ := ha
    obtain ⟨kb, hkb⟩ := hb
    use ka + kb
    omega
  · intro hn_even
    -- n = 0 + n, where 0 ∈ evens and n ∈ evens
    refine ⟨0, n, ?_, hn_even, ?_⟩
    · exact ⟨0, rfl⟩
    · ring

/-- For evens, r_{evens}(2n) = n/2 + 1 for unordered pairs.
    Pairs: (2k, 2(n-k)) for k ∈ {0, ..., n/2} where 2k ≤ 2(n-k). -/
theorem evens_repFunc (n : ℕ) : repFuncUnordered evens (2*n) = n / 2 + 1 := by
  unfold repFuncUnordered evens
  -- The pairs are (2k, 2(n-k)) for k = 0, 1, ..., n/2 with k ≤ n - k
  have hS_eq : {p : ℕ × ℕ | p.1 ∈ {m | Even m} ∧ p.2 ∈ {m | Even m} ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = 2*n} =
      (fun k => (2*k, 2*(n - k))) '' (Finset.range (n / 2 + 1) : Set ℕ) := by
    ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio, Prod.mk.injEq]
    constructor
    · intro ⟨⟨ka, hka⟩, ⟨kb, hkb⟩, hab, hadd⟩
      -- a = 2*ka, b = 2*kb, a + b = 2n, a ≤ b
      use ka
      constructor
      · -- ka < n/2 + 1
        -- From a ≤ b: 2*ka ≤ 2*kb, so ka ≤ kb
        -- From a + b = 2n: 2*ka + 2*kb = 2n, so ka + kb = n
        -- Thus 2*ka ≤ n, so ka ≤ n/2
        have hsum : ka + kb = n := by omega
        have hle : ka ≤ kb := by omega
        omega
      · constructor
        · omega
        · -- b = 2*(n-ka) since ka + kb = n
          have hsum : ka + kb = n := by omega
          omega
    · intro ⟨k, hk, hak, hbk⟩
      subst hak hbk
      constructor
      · -- Even (2*k) uses definition ∃ m, 2*k = m + m
        exact ⟨k, by ring⟩
      constructor
      · -- Even (2*(n-k)) uses definition ∃ m, 2*(n-k) = m + m
        exact ⟨n - k, by ring⟩
      constructor
      · -- 2k ≤ 2(n-k) means k ≤ n - k
        omega
      · -- 2k + 2(n-k) = 2n (need omega for ℕ subtraction)
        omega
  rw [hS_eq]
  have hinj : Function.Injective (fun k : ℕ => (2*k, 2*(n - k))) := by
    intro k1 k2 h
    simp only [Prod.mk.injEq] at h
    omega
  rw [Set.ncard_image_of_injective _ hinj]
  rw [Set.ncard_coe_finset, Finset.card_range]

/-- The natural numbers ℕ form a basis (trivially). -/
theorem nat_is_basis : IsAsymptoticBasis (Set.univ : Set ℕ) := by
  use 0
  intro n _
  exact ⟨0, n, trivial, trivial, by ring⟩

/-- For ℕ, r_ℕ(n) = n/2 + 1 (unordered pairs (k, n-k) with k ≤ n-k). -/
theorem nat_repFunc (n : ℕ) : repFuncUnordered (Set.univ : Set ℕ) n = n / 2 + 1 := by
  unfold repFuncUnordered
  -- The pairs are (k, n-k) for k ∈ {0, 1, ..., n/2}
  have hS_eq : {p : ℕ × ℕ | p.1 ∈ (Set.univ : Set ℕ) ∧ p.2 ∈ Set.univ ∧ p.1 ≤ p.2 ∧ p.1 + p.2 = n} =
      {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.1 + p.2 = n} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_univ, true_and]
  rw [hS_eq]
  -- Characterize the set as image of {0, ..., n/2}
  have hS_eq2 : {p : ℕ × ℕ | p.1 ≤ p.2 ∧ p.1 + p.2 = n} =
      (fun k => (k, n - k)) '' (Finset.range (n / 2 + 1) : Set ℕ) := by
    ext ⟨a, b⟩
    simp only [Set.mem_setOf_eq, Set.mem_image, Finset.coe_range, Set.mem_Iio, Prod.mk.injEq]
    constructor
    · intro ⟨hab, hadd⟩
      use a
      constructor
      · -- a < n/2 + 1, i.e., a ≤ n/2
        -- From a ≤ b and a + b = n: 2a ≤ n, so a ≤ n/2
        omega
      · constructor
        · rfl
        · omega
    · intro ⟨k, hk, hak, hbk⟩
      subst hak hbk
      constructor
      · -- k ≤ n - k
        omega
      · -- k + (n - k) = n
        omega
  rw [hS_eq2]
  -- The image of an injective function on a finite set
  have hinj : Function.Injective (fun k : ℕ => (k, n - k)) := by
    intro k1 k2 h
    simp only [Prod.mk.injEq] at h
    exact h.1
  rw [Set.ncard_image_of_injective _ hinj]
  rw [Set.ncard_coe_finset, Finset.card_range]

/- ## Part VII: Connection to Sidon Sets -/

/-- Bridge lemma: the Set-based IsSidon (unordered pair equality) implies the
    Finset-based IsSidon (ordered pair equality with a ≤ b, c ≤ d).
    From {a,b} = {c,d} with a ≤ b, c ≤ d: if c = a then b = d by omega;
    if c = b then a ≤ b = c ≤ d and a + b = c + d forces a = c, b = d. -/
private lemma isSidon_set_to_finset (A : Finset ℕ) (h : IsSidon (↑A : Set ℕ)) :
    Erdos340.IsSidon A := by
  intro a b c d ha hb hc hd hab hcd heq
  have hset := h a b c d (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb)
    (Finset.mem_coe.mpr hc) (Finset.mem_coe.mpr hd) heq
  -- hset : ({a, b} : Set ℕ) = {c, d}, so c ∈ {a, b}
  have hc_in : c ∈ ({a, b} : Set ℕ) := by rw [hset]; exact Set.mem_insert c {d}
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc_in
  rcases hc_in with rfl | rfl
  · -- c = a: then a + b = a + d, so b = d
    exact ⟨rfl, by omega⟩
  · -- c = b: with a ≤ b = c ≤ d and a + b = b + d, so a = d
    -- Then a ≤ b and b ≤ d = a, giving a = b = c = d
    constructor <;> omega

/-- **Known Result (Erdős-Turán)**: Sidon sets have at most √(2N) + 1 elements in {1,...,N}.
    Proved by importing Erdos340.sidon_upper_bound_weak via bridge lemma. -/
theorem sidon_density_bound (A : Finset ℕ) (hS : IsSidon (A : Set ℕ)) (N : ℕ)
    (hAN : ∀ a ∈ A, a ≤ N) : A.card ≤ Nat.sqrt (2 * N) + 1 :=
  Erdos340.sidon_upper_bound_weak A (isSidon_set_to_finset A hS) N hAN

/-- The number of upper-triangular pairs (a ≤ b) in F×F satisfies
    |{(a,b) ∈ F×F : a ≤ b}| * 2 = |F| * (|F| + 1).
    Proof: partition F×F into {a ≤ b} and {b < a}, swap bijects {a < b} ↔ {b < a},
    and {a ≤ b} = {a < b} ∪ diagonal. -/
private lemma card_upper_triangle (F : Finset ℕ) :
    ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card * 2 =
    F.card * (F.card + 1) := by
  -- Step 1: {a ≤ b} and {¬(a ≤ b)} partition F×F
  have h_part : ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card +
      ((F ×ˢ F).filter (fun p : ℕ × ℕ => ¬(p.1 ≤ p.2))).card = F.card * F.card := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_product]
  -- Step 2: Swap bijection: |{b < a}| = |{a < b}| via Prod.swap image
  have h_swap : ((F ×ˢ F).filter (fun p : ℕ × ℕ => ¬(p.1 ≤ p.2))).card =
      ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
    -- Show Prod.swap maps lower to strict-upper
    suffices h_im : ((F ×ˢ F).filter (fun p : ℕ × ℕ => ¬(p.1 ≤ p.2))).image Prod.swap =
        (F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 < p.2) by
      rw [← h_im]
      exact (Finset.card_image_of_injective _ (Prod.swap_injective (α := ℕ) (β := ℕ))).symm
    ext ⟨a, b⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.swap, not_le]
    constructor
    · rintro ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, hcd⟩, heq⟩
      obtain ⟨h1, h2⟩ := (Prod.mk.inj heq)
      subst h1; subst h2; exact ⟨⟨hd, hc⟩, hcd⟩
    · intro ⟨⟨ha, hb⟩, hab⟩
      exact ⟨⟨b, a⟩, ⟨⟨hb, ha⟩, by omega⟩, by simp [Prod.mk.injEq]⟩
  -- Step 3: {a ≤ b} = {a < b} ∪ {a = b}, disjoint
  have h_split : ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card =
      ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 < p.2)).card +
      ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 = p.2)).card := by
    have h_eq : (F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 ≤ p.2) =
        (F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 < p.2) ∪
        (F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 = p.2) := by
      ext ⟨a, b⟩; simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product]
      constructor
      · intro ⟨h, hab⟩; rcases Nat.eq_or_lt_of_le hab with rfl | hlt
        · exact Or.inr ⟨h, rfl⟩
        · exact Or.inl ⟨h, hlt⟩
      · rintro (⟨h, hlt⟩ | ⟨h, heq⟩) <;> exact ⟨h, by omega⟩
    have h_disj : Disjoint ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 < p.2))
        ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 = p.2)) := by
      rw [Finset.disjoint_filter]; intro _ _ h1 h2; omega
    rw [h_eq, Finset.card_union_of_disjoint h_disj]
  -- Step 4: |{a = b}| = |F| via the diagonal map a ↦ (a,a)
  have h_diag : ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 = p.2)).card = F.card := by
    suffices h_im : F.image (fun a => (a, a)) =
        (F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 = p.2) by
      rw [← h_im]
      exact Finset.card_image_of_injective _ (fun a₁ a₂ h => (Prod.mk.inj h).1)
    ext ⟨a, b⟩
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product, Prod.mk.injEq]
    constructor
    · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩
    · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
  -- Combine: 2U = n(n+1). omega can't handle n*n, so use linarith after expanding.
  -- h_part: U + L = n*n; h_swap: L = SU; h_split: U = SU + D; h_diag: D = n
  -- => U = L + n, so U + L = 2*L + n = n*n, hence 2*U = 2*L + 2*n = n*n + n = n*(n+1)
  have : F.card * (F.card + 1) = F.card * F.card + F.card := by ring
  linarith

/-- The Finset sumset image equals the image restricted to upper-triangular pairs. -/
private lemma finset_sumset_eq_upper_image (F : Finset ℕ) :
    (F ×ˢ F).image (fun p : ℕ × ℕ => p.1 + p.2) =
    ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).image (fun p : ℕ × ℕ => p.1 + p.2) := by
  ext n
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, heq⟩
    by_cases h : a ≤ b
    · exact ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, h⟩, heq⟩
    · exact ⟨⟨b, a⟩, ⟨⟨hb, ha⟩, by omega⟩, by omega⟩
  · rintro ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, _⟩, heq⟩
    exact ⟨⟨a, b⟩, ⟨ha, hb⟩, heq⟩

/-- The sumset of a finite set F has |sumset(F)| * 2 ≤ |F| * (|F| + 1). -/
private lemma finset_sumset_card_bound (F : Finset ℕ) :
    ((F ×ˢ F).image (fun p : ℕ × ℕ => p.1 + p.2)).card * 2 ≤
    F.card * (F.card + 1) := by
  rw [finset_sumset_eq_upper_image]
  calc (((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).image
          (fun p : ℕ × ℕ => p.1 + p.2)).card * 2
      ≤ ((F ×ˢ F).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card * 2 := by
        apply Nat.mul_le_mul_right; exact Finset.card_image_le
    _ = F.card * (F.card + 1) := card_upper_triangle F

/-- **Sidon sets are NOT asymptotic bases.**

Uses the tight Sidon density bound (Erdos340.sidon_card_le_sqrt, verified, axiom-free)
to show that Sidon sets are too sparse to cover [N₀, N] when N is large.

**Proof**: By contradiction. For a Sidon basis with threshold N₀, pick N = (4N₀+100)².
Coverage gives N-N₀+1 ≤ |sumset(A_N)| ≤ |A_N|(|A_N|+1)/2 (unordered pair bound).
The tight Sidon bound gives |A_N| ≤ √N+√(√N)+2 ≤ 5N₀+127, so the RHS ≈ N/2,
contradicting the LHS ≈ N. -/
theorem sidon_not_basis (A : Set ℕ) (hS : IsSidon A) (hInf : A.Infinite) :
    ¬IsAsymptoticBasis A := by
  intro ⟨N₀, hN₀⟩
  -- Choose N = (4*N₀ + 100)², large enough for the arithmetic contradiction
  set T := 4 * N₀ + 100 with hT_def
  set N := T ^ 2 with hN_def
  have hN_ge_N0 : N ≥ N₀ := by nlinarith [hN_def, hT_def, sq_nonneg T]
  -- Truncate A to A_N = A ∩ [0, N]
  set S := A ∩ Set.Iic N with hS_set
  have hS_fin : S.Finite := Set.Finite.subset (Set.finite_Iic N) Set.inter_subset_right
  set F := hS_fin.toFinset with hF_def
  set s := F.card with hs_def
  -- IsSidon is hereditary: S ⊆ A implies S is Sidon
  have hS_sidon : IsSidon (↑F : Set ℕ) := by
    rw [Set.Finite.coe_toFinset]
    intro a b c d ha hb hc hd heq
    exact hS a b c d (Set.mem_of_mem_inter_left ha) (Set.mem_of_mem_inter_left hb)
      (Set.mem_of_mem_inter_left hc) (Set.mem_of_mem_inter_left hd) heq
  -- Sidon tight bound: s ≤ √N + √(√N) + 2  (verified Erdős–Turán/Lindström bound)
  have hF_bound : ∀ a ∈ F, a ≤ N := by
    intro a ha
    rw [Set.Finite.mem_toFinset] at ha
    exact Set.mem_Iic.mp (Set.mem_of_mem_inter_right ha)
  have h_sidon : s ≤ Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 2 :=
    Erdos340.sidon_card_le_sqrt F (isSidon_set_to_finset F hS_sidon) N hF_bound
  -- Bound s using explicit values: √(T²) = T, √T ≤ N₀ + 25
  have h_sqrt_N : Nat.sqrt N = T := by
    rw [hN_def, sq]; simp [Nat.sqrt_eq]
  have h_sqrt_T : Nat.sqrt T ≤ N₀ + 25 := by
    have : T ≤ (N₀ + 25) ^ 2 := by nlinarith [hT_def]
    calc Nat.sqrt T ≤ Nat.sqrt ((N₀ + 25) ^ 2) := Nat.sqrt_le_sqrt this
      _ = N₀ + 25 := by rw [sq]; simp [Nat.sqrt_eq]
  have h_s_bound : s ≤ 5 * N₀ + 127 := by
    have h1 := h_sidon; rw [h_sqrt_N] at h1; linarith [h_sqrt_T, hT_def]
  -- Coverage: [N₀, N] ⊆ sumset(S), so N - N₀ + 1 ≤ |sumset(S)|
  have h_cover : Set.Icc N₀ N ⊆ sumset S := by
    intro n hn
    simp only [Set.mem_Icc] at hn
    obtain ⟨a, b, ha, hb, heq⟩ := hN₀ n hn.1
    exact ⟨a, b, ⟨ha, Set.mem_Iic.mpr (by omega)⟩,
                  ⟨hb, Set.mem_Iic.mpr (by omega)⟩, heq⟩
  -- sumset S is finite (reuse from basis_element_count_sq proof pattern)
  have h_sumset_fin : (sumset S).Finite := by
    apply Set.Finite.subset (Set.finite_Iic (2 * N))
    intro n ⟨a, b, ha, hb, heq⟩
    exact Set.mem_Iic.mpr (by
      have := Set.mem_Iic.mp (Set.mem_of_mem_inter_right ha)
      have := Set.mem_Iic.mp (Set.mem_of_mem_inter_right hb)
      omega)
  -- Coverage count
  have h_Icc_card : (Set.Icc N₀ N).ncard = N - N₀ + 1 := by
    rw [show Set.Icc N₀ N = ↑(Finset.Icc N₀ N) from (Finset.coe_Icc N₀ N).symm,
        Set.ncard_coe_finset, Nat.card_Icc]; omega
  have h_cover_count : N - N₀ + 1 ≤ (sumset S).ncard := by
    rw [← h_Icc_card]
    exact Set.ncard_le_ncard h_cover h_sumset_fin
  -- Key: connect Set sumset to Finset sumset for the bound
  have h_sumset_eq : sumset S = ↑((F ×ˢ F).image (fun p : ℕ × ℕ => p.1 + p.2)) := by
    ext n; constructor
    · rintro ⟨a, b, ha, hb, heq⟩
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨⟨a, b⟩, Finset.mem_product.mpr ⟨hS_fin.mem_toFinset.mpr ha,
        hS_fin.mem_toFinset.mpr hb⟩, by dsimp; omega⟩
    · simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
      rintro ⟨⟨a, b⟩, hmem, heq⟩
      dsimp at heq; rw [Finset.mem_product] at hmem
      exact ⟨a, b, hS_fin.mem_toFinset.mp hmem.1, hS_fin.mem_toFinset.mp hmem.2, by omega⟩
  -- |sumset(S)| = Finset card of sumset
  have h_sumset_ncard : (sumset S).ncard =
      ((F ×ˢ F).image (fun p : ℕ × ℕ => p.1 + p.2)).card := by
    rw [h_sumset_eq, Set.ncard_coe_finset]
  -- Unordered pair bound: |sumset| * 2 ≤ s * (s + 1)
  have h_sumset_bound : (sumset S).ncard * 2 ≤ s * (s + 1) := by
    rw [h_sumset_ncard]; exact finset_sumset_card_bound F
  -- Combined: 2*(N - N₀ + 1) ≤ s*(s+1), convert to addition to help nlinarith
  have h_combined : 2 * N + 2 ≤ s * (s + 1) + 2 * N₀ := by
    have h := Nat.mul_le_mul_left 2 h_cover_count
    have h2 := h_sumset_bound
    omega
  -- s*(s+1) ≤ (5*N₀+127)*(5*N₀+128) since s ≤ 5*N₀+127
  have h_s_mul : s * (s + 1) ≤ (5 * N₀ + 127) * (5 * N₀ + 128) := by
    apply Nat.mul_le_mul <;> omega
  -- N = T^2 = (4*N₀+100)^2, so 2*N+2 = 2*(4*N₀+100)^2+2
  -- Combining: 2*(4*N₀+100)^2+2 ≤ (5*N₀+127)*(5*N₀+128)+2*N₀
  -- i.e., 32*N₀²+1600*N₀+20002 ≤ 25*N₀²+1277*N₀+16256
  -- i.e., 7*N₀²+323*N₀+3746 ≤ 0, which is impossible.
  have : 2 * T ^ 2 + 2 ≤ (5 * N₀ + 127) * (5 * N₀ + 128) + 2 * N₀ := by
    linarith [hN_def]
  nlinarith [hT_def, sq_nonneg N₀]

/- ## Part VIII: Ordered vs Unordered Representations -/

/-- Ordered representation count is at least the unordered count.
    Every unordered pair (a, b) with a ≤ b also satisfies the ordered condition
    (just without the a ≤ b constraint). -/
theorem repFunc_ge_repFuncUnordered (A : Set ℕ) (n : ℕ) :
    repFunc A n ≥ repFuncUnordered A n := by
  unfold repFunc repFuncUnordered
  apply Set.ncard_le_ncard
  · intro ⟨a, b⟩ ⟨ha, hb, _, hadd⟩
    exact ⟨ha, hb, hadd⟩
  · exact pairs_summing_finite A n

/- ## Part IX: The Conjecture Holds for ℕ -/

/-- For ℕ, the unordered representation function is unbounded:
    repFuncUnordered(ℕ, 2k+2) = k + 2 > k. -/
theorem nat_repFuncUnordered_unbounded :
    ∀ k : ℕ, ∃ n : ℕ, repFuncUnordered (Set.univ : Set ℕ) n > k := by
  intro k
  use 2 * k + 2
  rw [nat_repFunc]
  -- (2k+2) / 2 + 1 = k + 1 + 1 = k + 2 > k
  omega

/-- The Erdős-Turán conjecture holds trivially for ℕ.
    Since repFunc ≥ repFuncUnordered and the unordered count is unbounded,
    the ordered count is also unbounded. -/
theorem erdos_turan_holds_for_nat :
    ∀ k : ℕ, ∃ n : ℕ, repFunc (Set.univ : Set ℕ) n > k := by
  intro k
  obtain ⟨n, hn⟩ := nat_repFuncUnordered_unbounded k
  exact ⟨n, lt_of_lt_of_le hn (repFunc_ge_repFuncUnordered Set.univ n)⟩

/- ## Part X: Basis Density Lower Bound -/

/-- **Counting Argument**: For any asymptotic basis A with threshold N₀,
    the number of elements of A up to N satisfies |A ∩ [0, N]|² ≥ N - N₀ + 1.

    **Proof**:
    1. Every n ∈ [N₀, N] is in sumset(A), so n = a + b with a, b ∈ A and a, b ≤ N.
    2. Thus [N₀, N] ⊆ sumset(A ∩ [0, N]).
    3. sumset(S) is the image of addition on S × S, so |sumset(S)| ≤ |S|².
    4. |[N₀, N]| = N - N₀ + 1, giving N - N₀ + 1 ≤ |S|².

    This implies |A ∩ [0, N]| ≥ √(N - N₀ + 1) ≥ c·√N for large N,
    establishing that bases of order 2 must have density at least √N. -/
theorem basis_element_count_sq (A : Set ℕ) (hA : IsAsymptoticBasis A) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (A ∩ Set.Iic N).ncard ^ 2 ≥ N - N₀ + 1 := by
  obtain ⟨N₀, hN₀⟩ := hA
  use N₀
  intro N hN
  set S := A ∩ Set.Iic N
  have hS_fin : S.Finite := Set.Finite.subset (Set.finite_Iic N) Set.inter_subset_right
  -- [N₀, N] ⊆ sumset S: every n ∈ [N₀, N] has a representation in S
  have h_cover : Set.Icc N₀ N ⊆ sumset S := by
    intro n hn
    simp only [Set.mem_Icc] at hn
    obtain ⟨a, b, ha, hb, heq⟩ := hN₀ n hn.1
    exact ⟨a, b, ⟨ha, Set.mem_Iic.mpr (by omega)⟩,
                  ⟨hb, Set.mem_Iic.mpr (by omega)⟩, heq⟩
  -- sumset S is the image of addition on S × S
  have h_sumset_img : sumset S = (fun p : ℕ × ℕ => p.1 + p.2) '' (S ×ˢ S) := by
    ext n
    simp only [sumset, Set.mem_setOf_eq, Set.mem_image, Set.mem_prod, Prod.exists]
    exact ⟨fun ⟨a, b, ha, hb, h⟩ => ⟨a, b, ⟨ha, hb⟩, h.symm⟩,
           fun ⟨a, b, ⟨ha, hb⟩, h⟩ => ⟨a, b, ha, hb, h.symm⟩⟩
  -- sumset S is finite
  have h_sumset_fin : (sumset S).Finite := by
    rw [h_sumset_img]; exact (hS_fin.prod hS_fin).image _
  -- |sumset S| ≤ |S × S| = |S|²
  have h_sumset_bound : (sumset S).ncard ≤ S.ncard ^ 2 := by
    rw [h_sumset_img]
    calc ((fun p : ℕ × ℕ => p.1 + p.2) '' (S ×ˢ S)).ncard
        ≤ (S ×ˢ S).ncard := Set.ncard_image_le (hS_fin.prod hS_fin)
      _ = S.ncard * S.ncard := Set.ncard_prod
      _ = S.ncard ^ 2 := by ring
  -- Chain: N - N₀ + 1 ≤ |[N₀, N]| ≤ |sumset S| ≤ |S|²
  calc N - N₀ + 1
      = (Set.Icc N₀ N).ncard := by
        rw [show Set.Icc N₀ N = ↑(Finset.Icc N₀ N) from (Finset.coe_Icc N₀ N).symm,
            Set.ncard_coe_finset, Nat.card_Icc]; omega
    _ ≤ (sumset S).ncard := Set.ncard_le_ncard h_cover h_sumset_fin
    _ ≤ S.ncard ^ 2 := h_sumset_bound

end Erdos28
