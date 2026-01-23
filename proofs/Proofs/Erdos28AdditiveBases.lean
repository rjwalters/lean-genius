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

namespace Erdos28

open Finset Filter

/-! ## Part I: Representation Function -/

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

/-! ## Part II: Sumset and Asymptotic Basis -/

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

/-! ## Part III: Basic Properties -/

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

/-! ## Part IV: The Main Conjecture -/

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

/-! ## Part V: Known Partial Results -/

/-- Grekos et al. (2003): For any asymptotic basis A, r_A(n) ≥ 6 for infinitely many n. -/
axiom grekos_lower_bound :
  ∀ A : Set ℕ, IsAsymptoticBasis A → ∀ M : ℕ, ∃ n > M, repFunc A n ≥ 6

/-- Borwein et al.: Improved to r_A(n) ≥ 8 infinitely often. -/
axiom borwein_lower_bound :
  ∀ A : Set ℕ, IsAsymptoticBasis A → ∀ M : ℕ, ∃ n > M, repFunc A n ≥ 8

/-! ## Part VI: Examples -/

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

/-! ## Part VII: Connection to Sidon Sets -/

/-- **Known Result (Erdős-Turán)**: Sidon sets have at most √(2N) + 1 elements in {1,...,N}.
    This is proved in Erdos340GreedySidon.lean as sidon_upper_bound_weak. -/
axiom sidon_density_bound (A : Finset ℕ) (hS : IsSidon (A : Set ℕ)) (N : ℕ)
    (hAN : ∀ a ∈ A, a ≤ N) : A.card ≤ Nat.sqrt (2 * N) + 1

/-- **Axiom: Sidon sets are NOT asymptotic bases.**

## Mathematical Background

This is a fundamental structural result showing the tension between:
- **Sidon property**: bounded representations (r_A(n) ≤ 2)
- **Basis property**: cover all large integers (A + A ⊇ [N₀, ∞))

## Proof Outline

### Key Insight: The Erdős-Turán Density Bound is Critical

The argument requires the **tight** Erdős-Turán bound: |A ∩ [1,N]| ≤ √N + O(N^{1/4}).

With this bound:
- Sidon sumset size = |A_N|(|A_N|+1)/2 ≈ N/2 + O(N^{3/4})
- Interval [N₀, N] has N - N₀ + 1 ≈ N elements (for N >> N₀)
- Since N/2 < N, we get a contradiction

### Why the √(2N) Bound is Insufficient

The weaker bound |A ∩ [1,N]| ≤ √(2N) + 1 (proved in Erdos340GreedySidon.lean) gives:
- Sumset size ≤ (√(2N)+1)(√(2N)+2)/2 ≈ N + 1.5√(2N)
- This is ≥ N - N₀ + 1, so no direct contradiction!

### The Tight Bound Approach

The proper Erdős-Turán bound uses **sum-counting** rather than difference-counting:
1. For A ⊆ [1, N], consider the sumset A + A ⊆ [2, 2N]
2. For Sidon sets, |A + A| = |A|(|A|+1)/2 (sums are distinct)
3. Since A + A ⊆ [2, 2N], we have |A|(|A|+1)/2 ≤ 2N - 1
4. This gives |A| ≤ √(4N) - 1 + O(1) = 2√N + O(1)
5. Refinement via the Erdős-Turán analysis gives √N + O(N^{1/4})

### Formalization Gap

To prove this theorem, we need:
1. **Prove tight Sidon density bound** (~100 lines): |A ∩ [1,N]| ≤ √N + c·N^{1/4}
2. **Set up Finset ↔ Set infrastructure** for truncations
3. **Handle the contradiction argument** with explicit N choice

The main technical challenge is proving the tight density bound. The weaker √(2N)
bound uses differences, while the tight bound requires counting sums.

## References

- Erdős-Turán (1941): Original conjecture and density bounds
- Erdos340GreedySidon.lean: sidon_upper_bound_weak (√(2N) bound, PROVED)
- Erdos340GreedySidon.lean: sidon_upper_bound (√N + O(N^{1/4}) bound, AXIOM)

## Status

**HARD**: Known mathematics, needs ~200 lines of formalization.
The key prerequisite is proving sidon_upper_bound in Erdos340GreedySidon.lean.
-/
axiom sidon_not_basis (A : Set ℕ) (hS : IsSidon A) (hInf : A.Infinite) :
    ¬IsAsymptoticBasis A

#check erdos_28
#check erdos_turan_weak
#check erdos_turan_strong

end Erdos28
