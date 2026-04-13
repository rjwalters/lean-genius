/-
# Collatz Cycles OQ-04: The Algebraic Cycle Product Equation

## Open Question (OQ-04)

Formalize the connection between Collatz cycles and the algebraic identity:

  ∏ᵢ (3nᵢ + 1) = 2^M · ∏ᵢ nᵢ

where n₁,...,nⱼ are the odd elements of a cycle, mᵢ is the number of halvings
after the i-th odd step, and M = Σmᵢ is the total halvings.

## Mathematical Content

For any Collatz cycle visiting odd elements n₁, n₂, ..., nⱼ (indices mod j),
with mᵢ halvings after the i-th odd step:

  **Step equation**: 3nᵢ + 1 = 2^mᵢ · nᵢ₊₁   (for each i, indices mod j)

Taking the product:

  ∏ᵢ (3nᵢ + 1) = ∏ᵢ (2^mᵢ · nᵢ₊₁)
               = (∏ᵢ 2^mᵢ) · (∏ᵢ nᵢ₊₁)
               = 2^M · (∏ᵢ nᵢ)              [i ↦ i+1 mod j is a bijection]

## Why This Matters

1. **Halving constraint (clean proof)**: Since 3nᵢ+1 > 3nᵢ, we get
   ∏(3nᵢ+1) > 3^j · ∏nᵢ = ∏(3nᵢ), so 2^M > 3^j immediately.

2. **Element lower bounds**: (2^M - 3^j) · n₁ = Σₖ 3^(j-1-k) · 2^(m₁+...+mₖ),
   which underlies Eliahou's theorem that any non-trivial cycle has length ≥ 17,087,915.

## References

- Lagarias (1985), "The 3x+1 problem and its generalizations"
- Eliahou (1993), "The 3x+1 problem: new lower bounds on nontrivial cycle lengths"
-/

import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset

namespace CollatzCyclesAlgebraic

open Finset

/-! ## Part I: Cyclic Successor on Fin j -/

/-- Cyclic successor: i ↦ (i+1) mod j. Models "next odd element" in a cycle. -/
def cyclicSucc {j : ℕ} (hj : 0 < j) (i : Fin j) : Fin j :=
  ⟨(i.val + 1) % j, Nat.mod_lt _ hj⟩

/-- Cyclic predecessor: i ↦ (i+j-1) mod j. Inverse of cyclicSucc. -/
def cyclicPred {j : ℕ} (hj : 0 < j) (i : Fin j) : Fin j :=
  ⟨(i.val + j - 1) % j, Nat.mod_lt _ hj⟩

@[simp]
theorem cyclicSucc_cyclicPred {j : ℕ} (hj : 0 < j) (i : Fin j) :
    cyclicSucc hj (cyclicPred hj i) = i := by
  ext; simp only [cyclicSucc, cyclicPred]; omega

@[simp]
theorem cyclicPred_cyclicSucc {j : ℕ} (hj : 0 < j) (i : Fin j) :
    cyclicPred hj (cyclicSucc hj i) = i := by
  ext; simp only [cyclicSucc, cyclicPred]; omega

/-! ## Part II: The Cycle Product Equation -/

/-- **Cycle product equation**: For a Collatz cycle with j odd steps, odd elements ns,
    and halving exponents ms satisfying `3 * ns(i) + 1 = 2^ms(i) * ns(i+1 mod j)`,
    the product of all (3*ns(i)+1) equals 2^M times the product of all ns(i):

      ∏ᵢ (3 * ns(i) + 1) = 2^(Σ ms(i)) · ∏ᵢ ns(i)

    This is the central algebraic identity of Collatz cycle theory. -/
theorem collatz_cycle_product_eq {j : ℕ} (hj : 0 < j)
    (ns : Fin j → ℕ) (ms : Fin j → ℕ)
    (hstep : ∀ i : Fin j, 3 * ns i + 1 = 2 ^ ms i * ns (cyclicSucc hj i)) :
    ∏ i : Fin j, (3 * ns i + 1) = 2 ^ ∑ i : Fin j, ms i * ∏ i : Fin j, ns i := by
  -- Step 1: Replace each 3*ns(i)+1 with 2^ms(i) * ns(cyclicSucc i)
  simp_rw [hstep]
  -- Step 2: ∏(2^ms * ns∘succ) = (∏ 2^ms) * (∏ ns∘succ)
  rw [prod_mul_distrib]
  -- Step 3: ∏ᵢ 2^ms(i) = 2^(Σ ms(i))
  rw [prod_pow_eq_pow_sum]
  -- Step 4: ∏ᵢ ns(cyclicSucc i) = ∏ᵢ ns(i) — cyclicSucc is a bijection on Fin j
  congr 1
  apply prod_nbij (cyclicSucc hj)
  · -- cyclicSucc maps univ → univ
    intro i _; exact mem_univ _
  · -- cyclicSucc is injective: (i+1)%j = (k+1)%j → i = k (for i,k < j)
    intro i₁ _ i₂ _ h
    have hval := congr_arg Fin.val h
    simp only [cyclicSucc] at hval
    have h₁ := i₁.isLt; have h₂ := i₂.isLt
    ext; omega
  · -- cyclicSucc is surjective: for any b, cyclicPred b maps to b
    intro b _
    exact ⟨cyclicPred hj b, mem_univ _, cyclicSucc_cyclicPred hj b⟩
  · -- Values agree: ns(cyclicSucc i) = ns(cyclicSucc i)
    intro i _; rfl

/-! ## Part III: The Halving Constraint -/

/-- **Halving constraint via product equation**: For any Collatz cycle, 2^M > 3^j.

    Proof outline (from the product equation):
    - ∏(3ns+1) = 2^M · ∏ns  [product equation]
    - ∏(3ns+1) > ∏(3ns) = 3^j · ∏ns  [since 3ns+1 > 3ns, all terms > 0]
    - Therefore 2^M · ∏ns > 3^j · ∏ns, so 2^M > 3^j.

    This subsumes the case-by-case approach in CollatzCycles.lean. -/
theorem collatz_cycle_halving_constraint {j : ℕ} (hj : 0 < j)
    (ns : Fin j → ℕ) (ms : Fin j → ℕ)
    (hpos : ∀ i : Fin j, 0 < ns i)
    (hstep : ∀ i : Fin j, 3 * ns i + 1 = 2 ^ ms i * ns (cyclicSucc hj i)) :
    2 ^ ∑ i : Fin j, ms i > 3 ^ j := by
  -- The proof is conceptually clean: combine the product equation with
  -- ∏(3ns+1) > 3^j·∏ns (since each factor satisfies 3n+1 > 3n > 0).
  -- We leave this as sorry while the key insight is fully proved in
  -- collatz_cycle_product_eq above.
  sorry

/-! ## Part IV: The Unique One-Odd-Step Cycle -/

/-- **One-odd-step characterization**: If 3n + 1 = 2^m · n for positive odd n,
    then n = 1 and m = 2. The unique 1-odd-step "cycle" is 1 → 4 → 2 → 1. -/
theorem collatz_one_odd_step {n m : ℕ} (hn : 0 < n) (hodd : n % 2 = 1)
    (hstep : 3 * n + 1 = 2 ^ m * n) : n = 1 ∧ m = 2 := by
  -- m ≥ 2: otherwise 2^m ≤ 2 and 3n+1 = 2^m·n ≤ 2n, so n ≤ -1 (impossible)
  have hm2 : m ≥ 2 := by
    by_contra h; push_neg at h
    interval_cases m <;> omega
  -- 2^m ≥ 4 since m ≥ 2
  have hpow : 4 ≤ 2 ^ m := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) hm2)
  -- (2^m - 3) * n = 1 (rearranging 3n+1 = 2^m*n)
  have heq : (2 ^ m - 3) * n = 1 := by omega
  -- Both factors of 1 must equal 1
  have hf1 : 2 ^ m - 3 = 1 := Nat.eq_one_of_mul_eq_one_left heq
  have hn1 : n = 1 := Nat.eq_one_of_mul_eq_one_right heq
  refine ⟨hn1, ?_⟩
  -- 2^m = 4 → m = 2
  have hpow4 : 2 ^ m = 4 := by omega
  by_contra hm_ne
  interval_cases m <;> simp_all

/-! ## Part V: Additive Cycle Equation (Stub) -/

/-- The cycle forcing sum: S(ms) = Σₖ 3^(j-1-k) · 2^(Σᵢ≤ₖ ms(i)).
    For any cycle, (2^M - 3^j) · ns(0) = S(ms, j). -/
noncomputable def cycleForcingSum {j : ℕ} (ms : Fin j → ℕ) : ℕ :=
  ∑ k : Fin j,
    3 ^ (j - 1 - k.val) *
    2 ^ (∑ i : Fin (k.val + 1), ms ⟨i.val, Nat.lt_of_lt_of_le i.isLt (by omega)⟩)

/-- **Additive cycle equation** (sorry-stub):
    (2^M - 3^j) · ns(0) = cycleForcingSum ms.

    Proof by induction on j: unfold each step equation, express ns(j-1) in terms
    of ns(0) and ms, substitute back. This characterizes ALL Collatz cycles purely
    from the halving sequence, and leads to Eliahou's lower bound on cycle length. -/
theorem collatz_cycle_additive_eq {j : ℕ} (hj : 0 < j)
    (ns : Fin j → ℕ) (ms : Fin j → ℕ)
    (hpos : ∀ i : Fin j, 0 < ns i)
    (hstep : ∀ i : Fin j, 3 * ns i + 1 = 2 ^ ms i * ns (cyclicSucc hj i))
    (hM_gt : 2 ^ ∑ i : Fin j, ms i > 3 ^ j) :
    (2 ^ ∑ i : Fin j, ms i - 3 ^ j) * ns ⟨0, hj⟩ = cycleForcingSum ms := by
  sorry

/-! ## Summary

Main contributions:
- **`collatz_cycle_product_eq`** [proved]: ∏(3ns+1) = 2^M · ∏ns
  via cyclic bijection argument (the key algebraic identity)
- **`collatz_one_odd_step`** [proved]: the unique 1-odd-step "cycle" is n=1, m=2
- **`collatz_cycle_halving_constraint`** [sorry]: 2^M > 3^j (proof outlined)
- **`collatz_cycle_additive_eq`** [sorry]: (2^M-3^j)·n₁ = S(ms) (for Eliahou bounds)

The product equation proof provides the algebraic foundation that unifies
the halving constraint, element bounds, and Eliahou's theorem. -/

#check @collatz_cycle_product_eq
#check @collatz_one_odd_step
#check @cycleForcingSum

end CollatzCyclesAlgebraic
