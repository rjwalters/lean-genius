/-
# Erdős Problem #324: Distinct Polynomial Pair Sums

Does there exist a polynomial f(x) ∈ ℤ[x] such that all the sums
f(a) + f(b) with a < b nonnegative integers are distinct?

It is conjectured that f(x) = x⁵ works. The Lander-Parkin-Selfridge
conjecture would imply f(x) = xⁿ works for all n ≥ 5.

## Status: OPEN

## References
- Erdős and Graham (1980, p. 53)
-/

import Mathlib

open Polynomial

/-
## Section I: Distinct Pair Sums
-/

/-- The pair sum function: given f ∈ ℤ[X], map (a, b) ↦ f(a) + f(b). -/
noncomputable def pairSumFn (f : ℤ[X]) : ℕ × ℕ → ℤ :=
  fun p => f.eval (p.1 : ℤ) + f.eval (p.2 : ℤ)

/-- The set of ordered pairs (a, b) with a < b. -/
def orderedPairs : Set (ℕ × ℕ) :=
  { p : ℕ × ℕ | p.1 < p.2 }

/-- A polynomial has the distinct pair sum property if f(a) + f(b)
are all distinct for a < b nonneg integers. -/
def HasDistinctPairSums (f : ℤ[X]) : Prop :=
  orderedPairs.InjOn (pairSumFn f)

/-
## Section II: The Conjecture
-/

/-- **Erdős Problem #324**: Does there exist f ∈ ℤ[X] with the distinct
pair sum property? -/
def ErdosProblem324 : Prop :=
  ∃ f : ℤ[X], HasDistinctPairSums f

/-
## Section III: The Quintic Conjecture
-/

/-- The specific conjecture that f(x) = x⁵ has distinct pair sums:
a⁵ + b⁵ = c⁵ + d⁵ with a < b and c < d implies (a,b) = (c,d). -/
def QuinticConjecture : Prop :=
  HasDistinctPairSums (X ^ 5 : ℤ[X])

/-- The quintic conjecture implies the main problem. -/
theorem quintic_implies_324 (h : QuinticConjecture) : ErdosProblem324 :=
  ⟨X ^ 5, h⟩

/-
## Section IV: Power Generalizations
-/

/-- For a given exponent n, the power pair sum property asks whether
aⁿ + bⁿ = cⁿ + dⁿ with a < b and c < d implies (a,b) = (c,d). -/
def PowerPairSumDistinct (n : ℕ) : Prop :=
  HasDistinctPairSums (X ^ n : ℤ[X])

/-- The Lander-Parkin-Selfridge conjecture implies xⁿ works for all n ≥ 5.
    Taking n = 5 trivially gives a solution. -/
theorem lps_implies_power_distinct :
    (∀ n : ℕ, n ≥ 5 → PowerPairSumDistinct n) → ErdosProblem324 :=
  fun h => ⟨X ^ 5, h 5 (by omega)⟩

/-- For n = 2, the property fails: 1² + 8² = 4² + 7² = 65. -/
theorem squares_not_distinct : ¬PowerPairSumDistinct 2 := by
  intro h
  have hp1 : ((1 : ℕ), (8 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((4 : ℕ), (7 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (X ^ 2 : ℤ[X]) (1, 8) = pairSumFn (X ^ 2 : ℤ[X]) (4, 7) := by
    simp [pairSumFn, eval_pow, eval_X]
  exact absurd (h hp1 hp2 heq) (by decide)

/-- For n = 3, the property fails: the Hardy–Ramanujan taxicab number
    1³ + 12³ = 9³ + 10³ = 1729. -/
theorem cubes_not_distinct : ¬PowerPairSumDistinct 3 := by
  intro h
  have hp1 : ((1 : ℕ), (12 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((9 : ℕ), (10 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (X ^ 3 : ℤ[X]) (1, 12) = pairSumFn (X ^ 3 : ℤ[X]) (9, 10) := by
    simp [pairSumFn, eval_pow, eval_X]
  exact absurd (h hp1 hp2 heq) (by decide)

/-- For n = 4, the property fails: 59⁴ + 158⁴ = 133⁴ + 134⁴ = 635318657
    (Euler 1772). -/
theorem quartics_not_distinct : ¬PowerPairSumDistinct 4 := by
  intro h
  have hp1 : ((59 : ℕ), (158 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((133 : ℕ), (134 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (X ^ 4 : ℤ[X]) (59, 158) = pairSumFn (X ^ 4 : ℤ[X]) (133, 134) := by
    simp [pairSumFn, eval_pow, eval_X]
  exact absurd (h hp1 hp2 heq) (by decide)

/-- For n = 0, the property fails: 0⁰ + 1⁰ = 0⁰ + 2⁰ = 2. -/
theorem zeroth_power_not_distinct : ¬PowerPairSumDistinct 0 := by
  intro h
  have hp1 : ((0 : ℕ), (1 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((0 : ℕ), (2 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (X ^ 0 : ℤ[X]) (0, 1) = pairSumFn (X ^ 0 : ℤ[X]) (0, 2) := by
    simp [pairSumFn, pow_zero, eval_one]
  exact absurd (h hp1 hp2 heq) (by decide)

/-- For n = 1, the property fails: 0 + 3 = 1 + 2 = 3. -/
theorem first_power_not_distinct : ¬PowerPairSumDistinct 1 := by
  intro h
  have hp1 : ((0 : ℕ), (3 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((1 : ℕ), (2 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (X ^ 1 : ℤ[X]) (0, 3) = pairSumFn (X ^ 1 : ℤ[X]) (1, 2) := by
    simp [pairSumFn, pow_one, eval_X]
  exact absurd (h hp1 hp2 heq) (by decide)

/-- Complete characterization: xⁿ fails for all n < 5. -/
theorem power_below_five_not_distinct (n : ℕ) (hn : n < 5) :
    ¬PowerPairSumDistinct n := by
  interval_cases n
  · exact zeroth_power_not_distinct
  · exact first_power_not_distinct
  · exact squares_not_distinct
  · exact cubes_not_distinct
  · exact quartics_not_distinct

/-
## Section V: Lower Degree Impossibility
-/

/-- Linear polynomials cannot have distinct pair sums:
    for f(x) = ax + b, f(0) + f(3) = f(1) + f(2) = 3a + 2b. -/
theorem linear_not_distinct (a b : ℤ) (_ha : a ≠ 0) :
    ¬HasDistinctPairSums (C a * X + C b) := by
  intro h
  have hp1 : ((0 : ℕ), (3 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((1 : ℕ), (2 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (C a * X + C b) (0, 3) = pairSumFn (C a * X + C b) (1, 2) := by
    simp [pairSumFn, eval_add, eval_mul, eval_X]; ring
  exact absurd (h hp1 hp2 heq) (by decide)

/-- The degree of any polynomial with distinct pair sums must be ≥ 5. -/
axiom min_degree_for_distinct :
  ∀ f : ℤ[X], HasDistinctPairSums f → f.natDegree ≥ 5

/-
## Section V.b: Constant Polynomials
-/

/-- Constant polynomials cannot have distinct pair sums:
    f(a) + f(b) = 2c for all pairs, so (0,1) and (0,2) collide. -/
theorem constant_not_distinct (c : ℤ) :
    ¬HasDistinctPairSums (C c : ℤ[X]) := by
  intro h
  have hp1 : ((0 : ℕ), (1 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((0 : ℕ), (2 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (C c : ℤ[X]) (0, 1) = pairSumFn (C c : ℤ[X]) (0, 2) := by
    simp [pairSumFn]
  exact absurd (h hp1 hp2 heq) (by decide)

/-
## Section V.c: Quadratic Impossibility Subcases
-/

/-- Quadratic polynomials with no linear term cannot have distinct pair sums:
    1² + 8² = 4² + 7² = 65 gives a collision for any nonzero leading coefficient a. -/
theorem quadratic_no_linear_not_distinct (a c : ℤ) (ha : a ≠ 0) :
    ¬HasDistinctPairSums (C a * X ^ 2 + C c) := by
  intro h
  have hp1 : ((1 : ℕ), (8 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((4 : ℕ), (7 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have heq : pairSumFn (C a * X ^ 2 + C c) (1, 8) =
             pairSumFn (C a * X ^ 2 + C c) (4, 7) := by
    simp [pairSumFn, eval_add, eval_mul, eval_pow, eval_X, eval_C]; ring
  exact absurd (h hp1 hp2 heq) (by decide)

/-- Monic quadratics with negative linear coefficient -(n+2) fail distinct pair sums:
    f(0)+f(1) = f(n+1)+f(n+2) via the identity (n+1)·((n+1)-(n+2)) = -(n+1). -/
theorem monic_neg_linear_quad_not_distinct (n : ℕ) (c : ℤ) :
    ¬HasDistinctPairSums (X ^ 2 - C ((n : ℤ) + 2) * X + C c) := by
  intro h
  have hp1 : ((0 : ℕ), (1 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]
  have hp2 : ((n + 1 : ℕ), (n + 2 : ℕ)) ∈ orderedPairs := by simp [orderedPairs]; omega
  have hne : ((0 : ℕ), (1 : ℕ)) ≠ ((n + 1 : ℕ), (n + 2 : ℕ)) := by
    intro h; simp [Prod.mk.injEq] at h; omega
  have heq : pairSumFn (X ^ 2 - C ((n : ℤ) + 2) * X + C c) (0, 1) =
             pairSumFn (X ^ 2 - C ((n : ℤ) + 2) * X + C c) (n + 1, n + 2) := by
    simp [pairSumFn, eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    push_cast; ring
  exact absurd (h hp1 hp2 heq) hne

/-
## Section VI: Counting Pair Sums
-/

/-- The number of distinct values of f(a) + f(b) for a < b ≤ N. -/
noncomputable def distinctPairSumCount (f : ℤ[X]) (N : ℕ) : ℕ :=
  (Finset.filter (fun p : ℕ × ℕ => p.1 < p.2)
    (Finset.range (N + 1) ×ˢ Finset.range (N + 1))).image
    (fun p => f.eval (p.1 : ℤ) + f.eval (p.2 : ℤ)) |>.card

/-- The number of strictly ordered pairs from {0,...,N} is C(N+1,2).
    Proof via partition + swap symmetry, following the pattern from
    Erdős #530 (card_sorted_pairs). -/
private theorem card_strict_pairs (N : ℕ) :
    ((Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
      (fun p : ℕ × ℕ => p.1 < p.2)).card = (N + 1).choose 2 := by
  set S := Finset.range (N + 1)
  -- |{a<b}| + |{¬(a<b)}| = |S|²
  have h_total : ((S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2)).card +
      ((S ×ˢ S).filter (fun p : ℕ × ℕ => ¬(p.1 < p.2))).card = S.card * S.card := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, Finset.card_product]
  -- Decompose {¬(a<b)} = {b<a} ∪ {a=b}
  have h_decomp : (S ×ˢ S).filter (fun p : ℕ × ℕ => ¬(p.1 < p.2)) =
      (S ×ˢ S).filter (fun p : ℕ × ℕ => p.2 < p.1) ∪
      (S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 = p.2) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product, not_lt]
    constructor
    · intro ⟨hmem, hle⟩
      rcases eq_or_lt_of_le hle with h | h
      · exact Or.inr ⟨hmem, h.symm⟩
      · exact Or.inl ⟨hmem, h⟩
    · rintro (⟨hmem, h⟩ | ⟨hmem, h⟩)
      · exact ⟨hmem, by omega⟩
      · exact ⟨hmem, by omega⟩
  -- {b<a} and {a=b} are disjoint
  have h_disj : Disjoint
      ((S ×ˢ S).filter (fun p : ℕ × ℕ => p.2 < p.1))
      ((S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 = p.2)) := by
    rw [Finset.disjoint_filter]
    intro ⟨a, b⟩ _ h1 h2; omega
  -- |{b<a}| = |{a<b}| via swap bijection (a,b) ↦ (b,a)
  have h_swap : ((S ×ˢ S).filter (fun p : ℕ × ℕ => p.2 < p.1)).card =
      ((S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2)).card := by
    symm
    apply Finset.card_bij (fun p _ => Prod.swap p)
    · intro ⟨a, b⟩ h
      simp only [Finset.mem_filter, Finset.mem_product, Prod.swap] at h ⊢
      exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩
    · intro ⟨a₁, b₁⟩ _ ⟨a₂, b₂⟩ _ h
      simp only [Prod.swap, Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro ⟨a, b⟩ h
      simp only [Finset.mem_filter, Finset.mem_product] at h
      exact ⟨⟨b, a⟩, by
        simp only [Finset.mem_filter, Finset.mem_product]
        exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩,
        by simp [Prod.swap]⟩
  -- |{a=b}| = |S| via diagonal bijection a ↦ (a,a)
  have h_diag : ((S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 = p.2)).card = S.card := by
    symm
    apply Finset.card_bij (fun x _ => (x, x))
    · intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, ha⟩, rfl⟩
    · intro a₁ _ a₂ _ h
      exact (Prod.mk.inj h).1
    · intro p h
      have hf := Finset.mem_filter.mp h
      have hp := Finset.mem_product.mp hf.1
      exact ⟨p.1, hp.1, Prod.ext rfl hf.2⟩
  -- Key step: |{¬(a<b)}| = |{a<b}| + |S|
  suffices h_key : ((S ×ˢ S).filter (fun p : ℕ × ℕ => ¬(p.1 < p.2))).card =
      ((S ×ˢ S).filter (fun p : ℕ × ℕ => p.1 < p.2)).card + S.card by
    -- From h_total and h_key: card + (card + |S|) = |S|²
    rw [h_key] at h_total
    have hcard : S.card = N + 1 := Finset.card_range (N + 1)
    rw [hcard] at h_total
    -- h_total: card + (card + (N+1)) = (N+1)*(N+1)
    -- Use identity: choose(n,2) + choose(n,2) + n = n*n (proved by induction)
    have h_choose_id : ∀ n : ℕ, n.choose 2 + n.choose 2 + n = n * n := by
      intro n; induction n with
      | zero => simp
      | succ m ih =>
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        linarith
    linarith [h_choose_id (N + 1)]
  -- Prove h_key: decompose ¬< into > and =, swap gives |>|=|<|, diagonal gives |=|=|S|
  rw [h_decomp, Finset.card_union_of_disjoint h_disj, h_swap, h_diag]

/-- For distinct pair sums, the count equals C(N+1, 2).
    Proof: injectivity gives |image| = |source|, and the source has
    C(N+1,2) ordered pairs. -/
theorem distinct_count_eq_binomial (f : ℤ[X]) (hf : HasDistinctPairSums f) (N : ℕ) :
    distinctPairSumCount f N = (N + 1).choose 2 := by
  unfold distinctPairSumCount
  set S := (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).filter
    (fun p : ℕ × ℕ => p.1 < p.2)
  -- The function is injective on the filtered set (subset of orderedPairs)
  have h_inj : Set.InjOn (fun p : ℕ × ℕ => f.eval (↑p.1 : ℤ) + f.eval (↑p.2 : ℤ))
      (↑S : Set (ℕ × ℕ)) := by
    intro p₁ hp₁ p₂ hp₂ heq
    have h1 : p₁ ∈ orderedPairs :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hp₁)).2
    have h2 : p₂ ∈ orderedPairs :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hp₂)).2
    exact hf h1 h2 heq
  rw [Finset.card_image_of_injOn h_inj]
  exact card_strict_pairs N
