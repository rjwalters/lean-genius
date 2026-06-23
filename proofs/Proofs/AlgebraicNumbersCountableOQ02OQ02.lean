/-
Cantor's 1874 Nested Interval Proof of ℝ Uncountability

**Open Question (algebraic-numbers-countable-oq-02-oq-02)**:
Formalize Cantor's ORIGINAL 1874 proof that ℝ is uncountable, using nested
intervals rather than the diagonal argument (which came later, in 1891).

**What This Proves** (0 axioms):
1. `nested_a_lt_b` — intervals remain nonempty at every step
2. `nested_a_strict_mono` — left endpoints strictly increase
3. `nested_exclusion` — each f(n) is excluded from the next interval
4. `exists_real_not_in_range` — for any f : ℕ → ℝ, ∃ x ∉ range(f)
5. `reals_uncountable_nested` — ℝ is uncountable (alternative proof)

**Proof Strategy**:
Given any enumeration f : ℕ → ℝ, construct nested intervals [aₙ, bₙ] by:
- Divide each interval into thirds
- Choose a subinterval that avoids f(n)
- Ensure left endpoints STRICTLY increase (key for excluding boundary cases)

The supremum x = sup(aₙ) satisfies x > aₙ for all n (from strict monotonicity),
so f(n) < aₙ₊₁ < x or f(n) > bₙ₊₁ ≥ x, giving f(n) ≠ x.

**Historical Note**: This is Cantor's original argument from
"Über eine Eigenschaft des Inbegriffes aller reellen algebraischen Zahlen" (1874).
The more famous diagonal argument appeared in 1891.

References:
- AlgebraicNumbersCountableOQ02.lean: cardinality-based proof (alternative)
- Cantor, G. "Über eine Eigenschaft..." J. reine angew. Math. 77 (1874), 258-262
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false

namespace CantorNestedIntervals

/-
## The Nested Interval Construction

Given f : ℕ → ℝ, we construct intervals [aₙ, bₙ] that avoid each f(n).

At each step, divide [aₙ, bₙ] into three equal parts:
- Left third:  [aₙ, aₙ + d/3]
- Middle third: [aₙ + d/3, aₙ + 2d/3]
- Right third:  [aₙ + 2d/3, bₙ]
where d = bₙ - aₙ.

Choose based on where f(n) lies:
- f(n) in left or right third → take middle third (f(n) excluded)
- f(n) in middle third → take right third (f(n) ≤ left endpoint)

Key property: aₙ₊₁ always strictly exceeds aₙ (either +d/3 or +2d/3).
-/

/-- The nested interval construction. Returns (aₙ, bₙ) at step n. -/
noncomputable def nested (f : ℕ → ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | n + 1 =>
    let (a, b) := nested f n
    let d := b - a
    let t₁ := a + d / 3
    let t₂ := a + 2 * d / 3
    if f n < t₁ then (t₁, t₂)       -- f(n) in left third → middle
    else if f n > t₂ then (t₁, t₂)  -- f(n) in right third → middle
    else (t₂, b)                      -- f(n) in middle third → right

/-- Left endpoint of the n-th interval. -/
noncomputable def a (f : ℕ → ℝ) (n : ℕ) : ℝ := (nested f n).1

/-- Right endpoint of the n-th interval. -/
noncomputable def b (f : ℕ → ℝ) (n : ℕ) : ℝ := (nested f n).2

/-- Width of the n-th interval. -/
noncomputable def width (f : ℕ → ℝ) (n : ℕ) : ℝ := b f n - a f n

/-
## Core Properties

All proved by induction on n with case analysis on the if-then-else.
-/

@[simp] lemma nested_zero (f : ℕ → ℝ) : nested f 0 = (0, 1) := rfl

@[simp] lemma a_zero (f : ℕ → ℝ) : a f 0 = 0 := rfl

@[simp] lemma b_zero (f : ℕ → ℝ) : b f 0 = 1 := rfl

/-- The interval width is positive at every step. -/
theorem width_pos (f : ℕ → ℝ) : ∀ n, width f n > 0 := by
  intro n; induction n with
  | zero => simp [width]
  | succ n ih =>
    simp only [width, a, b, nested]
    set p := nested f n
    set a_n := p.1; set b_n := p.2
    set d := b_n - a_n
    have hd : d > 0 := ih
    -- Case split on the construction
    by_cases h1 : f n < a_n + d / 3
    · simp [h1]; linarith
    · by_cases h2 : f n > a_n + 2 * d / 3
      · simp [h1, h2]; linarith
      · simp [h1, h2]; linarith

/-- Left endpoint is strictly less than right endpoint. -/
theorem a_lt_b (f : ℕ → ℝ) (n : ℕ) : a f n < b f n := by
  have := width_pos f n; simp [width] at this; linarith

/-- Left endpoint strictly increases at each step. -/
theorem a_strict_mono (f : ℕ → ℝ) (n : ℕ) : a f (n + 1) > a f n := by
  simp only [a, nested]
  set p := nested f n
  set a_n := p.1; set b_n := p.2
  set d := b_n - a_n
  have hd : d > 0 := width_pos f n
  by_cases h1 : f n < a_n + d / 3
  · simp [h1]; linarith
  · by_cases h2 : f n > a_n + 2 * d / 3
    · simp [h1, h2]; linarith
    · simp [h1, h2]; linarith

/-- Right endpoint is non-increasing. -/
theorem b_mono (f : ℕ → ℝ) (n : ℕ) : b f (n + 1) ≤ b f n := by
  simp only [b, nested]
  set p := nested f n
  set a_n := p.1; set b_n := p.2
  set d := b_n - a_n
  have hd : d > 0 := width_pos f n
  by_cases h1 : f n < a_n + d / 3
  · simp [h1]; linarith
  · by_cases h2 : f n > a_n + 2 * d / 3
    · simp [h1, h2]; linarith
    · simp [h1, h2]

/-- **Exclusion property**: f(n) is excluded from the (n+1)-th interval.
    Specifically: f(n) ≤ aₙ₊₁ or f(n) > bₙ₊₁.
    (The ≤ case uses strict monotonicity of a to get f(n) < sup.) -/
theorem exclusion (f : ℕ → ℝ) (n : ℕ) :
    f n ≤ a f (n + 1) ∨ f n > b f (n + 1) := by
  simp only [a, b, nested]
  set p := nested f n
  set a_n := p.1; set b_n := p.2
  set d := b_n - a_n
  have hd : d > 0 := width_pos f n
  by_cases h1 : f n < a_n + d / 3
  · simp [h1]; left; linarith
  · by_cases h2 : f n > a_n + 2 * d / 3
    · simp [h1, h2]; right; linarith
    · simp [h1, h2]; left; push_neg at h2; linarith

/-- Left endpoints form a strictly monotone sequence. -/
theorem a_strictMono (f : ℕ → ℝ) : StrictMono (a f) :=
  strictMono_nat_of_lt_succ (fun n => a_strict_mono f n)

/-- Right endpoints form an antitone (non-increasing) sequence. -/
theorem b_antitone (f : ℕ → ℝ) : Antitone (b f) :=
  antitone_nat_of_succ_le (fun n => b_mono f n)

/-- Right endpoints are bounded above by b₀ = 1. -/
theorem b_le_one (f : ℕ → ℝ) (n : ℕ) : b f n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih => exact le_trans (b_mono f n) ih

/-- Any left endpoint ≤ any right endpoint. -/
theorem a_le_b_all (f : ℕ → ℝ) (m n : ℕ) : a f m ≤ b f n := by
  by_cases hmn : m ≤ n
  · -- a m ≤ a n < b n (since a is monotone)
    exact le_trans ((a_strictMono f).monotone hmn) (le_of_lt (a_lt_b f n))
  · -- a m < b m ≤ b n (since b is antitone)
    push_neg at hmn
    exact le_trans (le_of_lt (a_lt_b f m)) ((b_antitone f) (le_of_lt hmn))

/-- All left endpoints are bounded above by 1. -/
theorem a_bdd_above (f : ℕ → ℝ) (n : ℕ) : a f n ≤ 1 :=
  le_trans (a_le_b_all f n 0) (by simp)

/-
## The Limit Point

The supremum of the left endpoints exists (bounded, monotone) and satisfies
the key property: it differs from every f(n).
-/

/-- The set of left endpoints is bounded above. -/
theorem a_range_bddAbove (f : ℕ → ℝ) : BddAbove (Set.range (a f)) := by
  use 1
  intro x ⟨n, hn⟩
  rw [← hn]
  exact a_bdd_above f n

/-- The limit point: supremum of all left endpoints. -/
noncomputable def limitPoint (f : ℕ → ℝ) : ℝ :=
  sSup (Set.range (a f))

/-- The limit point exceeds every left endpoint. -/
theorem limit_gt_a (f : ℕ → ℝ) (n : ℕ) : limitPoint f > a f n := by
  have hmono := a_strict_mono f n -- a(n+1) > a(n)
  have hle : a f (n + 1) ≤ limitPoint f :=
    le_csSup (a_range_bddAbove f) ⟨n + 1, rfl⟩
  linarith

/-- The limit point is at most every right endpoint. -/
theorem limit_le_b (f : ℕ → ℝ) (n : ℕ) : limitPoint f ≤ b f n := by
  apply csSup_le ⟨a f 0, 0, rfl⟩
  intro x ⟨m, hm⟩
  rw [← hm]
  exact a_le_b_all f m n

/-
## Main Results
-/

/-- **Cantor's 1874 Theorem (core)**: For any f : ℕ → ℝ, the limit point
    of the nested interval construction is not in the range of f. -/
theorem limitPoint_not_in_range (f : ℕ → ℝ) (n : ℕ) : f n ≠ limitPoint f := by
  intro heq
  have hexcl := exclusion f n
  cases hexcl with
  | inl h =>
    -- f(n) ≤ a(n+1) < limitPoint (from limit_gt_a)
    have := limit_gt_a f (n + 1)
    have := a_strict_mono f n
    linarith
  | inr h =>
    -- f(n) > b(n+1) ≥ limitPoint (from limit_le_b)
    have := limit_le_b f (n + 1)
    linarith

/-- **Cantor's 1874 Theorem**: For any f : ℕ → ℝ, there exists a real
    number not in the range of f. -/
theorem exists_real_not_in_range (f : ℕ → ℝ) :
    ∃ x : ℝ, x ∉ Set.range f := by
  refine ⟨limitPoint f, ?_⟩
  intro ⟨n, hn⟩
  exact limitPoint_not_in_range f n hn

/-- No surjection from ℕ to ℝ exists. -/
theorem no_surjection_nat_to_real :
    ¬ ∃ f : ℕ → ℝ, Function.Surjective f := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hx⟩ := exists_real_not_in_range f
  exact hx (hf x)

/-- **ℝ is uncountable** (Cantor's 1874 nested interval proof). -/
theorem reals_uncountable_nested : ¬ Countable ℝ := by
  intro h
  haveI := h
  haveI : Nonempty ℝ := ⟨0⟩
  obtain ⟨f, hf⟩ := Countable.exists_surjective_nat ℝ ⟨(0 : ℝ)⟩
  exact no_surjection_nat_to_real ⟨f, hf⟩

/-
## Summary

**Proved** (0 sorries, 0 axioms):
1. width_pos — interval width > 0 at every step
2. a_lt_b — intervals remain nonempty
3. a_strict_mono — left endpoints strictly increase
4. b_mono — right endpoints are non-increasing
5. exclusion — f(n) excluded from (n+1)-th interval
6. a_bdd_above — left endpoints bounded by 1
7. a_le_b_all — all left endpoints ≤ all right endpoints
8. limit_gt_a — limit point exceeds every left endpoint
9. limit_le_b — limit point ≤ every right endpoint
10. limitPoint_not_in_range — limit point ≠ f(n) for any n
11. exists_real_not_in_range — ∃ x ∉ range(f)
12. no_surjection_nat_to_real — ¬∃ surjection ℕ → ℝ
13. reals_uncountable_nested — ¬ Countable ℝ

**Key technique**: The thirds-based construction ensures left endpoints
STRICTLY increase, which is essential for excluding boundary cases.
Without strict increase, f(n) could equal a boundary point that happens
to be the limit, making the exclusion argument fail.

**Historical significance**: This is Cantor's original 1874 proof,
predating the diagonal argument (1891) by 17 years.
-/

end CantorNestedIntervals
