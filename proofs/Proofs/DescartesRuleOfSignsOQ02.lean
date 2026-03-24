import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

set_option maxHeartbeats 800000

/-
# Budan's Theorem — Generalization of Descartes' Rule (OQ-02)

## What This Proves

Budan's theorem (1807) generalizes Descartes' Rule of Signs from counting
positive roots to counting roots in any half-open interval (a, b].

For a polynomial p of degree n, define the **Budan-Fourier sequence** at x:
  [p(x), p'(x), p''(x), ..., p⁽ⁿ⁾(x)]

Let V_p(x) = number of sign changes in this sequence (ignoring zeros).

**Budan's Theorem**: The number of roots of p in (a, b], counted with
multiplicity, satisfies:
  #roots(a,b] ≤ V_p(a) - V_p(b)
and the difference V_p(a) - V_p(b) - #roots(a,b] is an even non-negative number.

## Historical Context

François Budan de Boislaurent published this result in 1807. Joseph Fourier
independently rediscovered it around 1820, leading to the name
"Budan-Fourier theorem." It is strictly more powerful than Descartes' rule,
which is the special case a = 0, b → ∞.

The theorem is a key ingredient in:
- Vincent's theorem for real root isolation (1834)
- The VAS (Vincent-Akritas-Strzeboński) algorithm
- Modern real algebraic geometry computations

## Key Results

1. **Derivative sequence**: Iterated derivatives [p, p', p'', ..., p⁽ⁿ⁾]
2. **Budan-Fourier count V_p(x)**: Sign changes in the derivative sequence at x
3. **Main theorem**: #roots in (a,b] ≤ V_p(a) - V_p(b) (with parity)
4. **Descartes recovery**: Budan at (0, +∞) gives Descartes' rule
5. **Root isolation**: V_p(a) - V_p(b) = 1 implies exactly one root in (a,b]
6. **Special cases**: Constant, linear, quadratic polynomials

## Axiom Budget: 3 axioms (budan_upper_bound, budan_parity, budanCount_large)

Original formalization for Lean Genius.
-/

namespace BudanTheorem

open Polynomial

/-
## Part I: The Derivative Sequence

The Budan-Fourier sequence of a polynomial p of degree n at point x is:
  [p(x), p'(x), p''(x), ..., p⁽ⁿ⁾(x)]
-/

/-- The k-th iterated derivative of a polynomial.
    iterDeriv p 0 = p, iterDeriv p 1 = p', iterDeriv p k = p⁽ᵏ⁾ -/
noncomputable def iterDeriv (p : ℝ[X]) : ℕ → ℝ[X]
  | 0 => p
  | k + 1 => derivative (iterDeriv p k)

@[simp]
theorem iterDeriv_zero (p : ℝ[X]) : iterDeriv p 0 = p := rfl

@[simp]
theorem iterDeriv_succ (p : ℝ[X]) (k : ℕ) :
    iterDeriv p (k + 1) = derivative (iterDeriv p k) := rfl

/-- iterDeriv of a derivative commutes. -/
theorem iterDeriv_derivative (p : ℝ[X]) (k : ℕ) :
    iterDeriv (derivative p) k = iterDeriv p (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih => simp [ih]

/-- Degree of the k-th iterated derivative is bounded. -/
theorem natDegree_iterDeriv_le (p : ℝ[X]) (k : ℕ) :
    (iterDeriv p k).natDegree ≤ p.natDegree - k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [iterDeriv_succ]
    have hd := Polynomial.natDegree_derivative_le (iterDeriv p k)
    omega

/-- Iterated derivative beyond the degree is zero. -/
theorem iterDeriv_eq_zero (p : ℝ[X]) (k : ℕ) (hk : p.natDegree < k) :
    iterDeriv p k = 0 := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [iterDeriv_succ]
    by_cases hk' : p.natDegree < k
    · rw [ih hk']; simp
    · push_neg at hk'
      have hkeq : k = p.natDegree := by omega
      subst hkeq
      have hdeg : (iterDeriv p p.natDegree).natDegree = 0 := by
        have := natDegree_iterDeriv_le p p.natDegree; omega
      have hconst := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      rw [hconst]; simp

/-- The Budan-Fourier evaluation sequence at a point x.
    Returns [p(x), p'(x), ..., p⁽ⁿ⁾(x)] as a list of reals. -/
noncomputable def budanSequence (p : ℝ[X]) (n : ℕ) (x : ℝ) : List ℝ :=
  (List.range (n + 1)).map (fun k => (iterDeriv p k).eval x)

@[simp]
theorem budanSequence_length (p : ℝ[X]) (n : ℕ) (x : ℝ) :
    (budanSequence p n x).length = n + 1 := by
  simp [budanSequence]

/-
## Part II: Sign Variation Count
-/

/-- Count adjacent pairs that differ in a list of ±1 values. -/
def countAdjacentDiffs : List ℤ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest =>
    (if a ≠ b then 1 else 0) + countAdjacentDiffs (b :: rest)

@[simp] theorem countAdjacentDiffs_nil : countAdjacentDiffs [] = 0 := rfl
@[simp] theorem countAdjacentDiffs_singleton (a : ℤ) : countAdjacentDiffs [a] = 0 := rfl

/-- Count sign changes in a list of reals, ignoring zeros.
    Filters out zeros, maps remaining to ±1, counts adjacent differences. -/
noncomputable def signChangesInList (l : List ℝ) : ℕ :=
  let nonzero := l.filter (· ≠ 0)
  let signs := nonzero.map (fun x => if x > 0 then (1 : ℤ) else -1)
  countAdjacentDiffs signs

@[simp]
theorem signChangesInList_nil : signChangesInList [] = 0 := by
  simp [signChangesInList]

/-- The number of adjacent differences in a list is at most the list length minus 1. -/
private theorem countAdjacentDiffs_le : ∀ (l : List ℤ),
    countAdjacentDiffs l ≤ l.length - 1
  | [] => by simp
  | [_] => by simp
  | _ :: b :: rest => by
    simp only [countAdjacentDiffs, List.length_cons]
    have ih := countAdjacentDiffs_le (b :: rest)
    simp only [List.length_cons] at ih
    split <;> omega

/-- Sign changes in a list are bounded by the list length minus 1. -/
private theorem signChangesInList_le_pred_length (l : List ℝ) :
    signChangesInList l ≤ l.length - 1 := by
  have : signChangesInList l =
      countAdjacentDiffs ((l.filter (· ≠ 0)).map
        (fun x => if x > 0 then (1 : ℤ) else -1)) := rfl
  rw [this]
  calc countAdjacentDiffs ((l.filter (· ≠ 0)).map _)
      ≤ ((l.filter (· ≠ 0)).map (fun x => if x > 0 then (1 : ℤ) else -1)).length - 1 :=
        countAdjacentDiffs_le _
    _ ≤ l.length - 1 := by
        simp only [List.length_map]
        exact Nat.sub_le_sub_right (List.length_filter_le _ l) 1

/-
## Part III: The Budan-Fourier Count V_p(x)
-/

/-- The Budan-Fourier sign variation count V_p(x).
    Counts sign changes in the derivative evaluation sequence at x. -/
noncomputable def budanCount (p : ℝ[X]) (x : ℝ) : ℕ :=
  signChangesInList (budanSequence p p.natDegree x)

@[simp]
theorem budanCount_zero (x : ℝ) : budanCount (0 : ℝ[X]) x = 0 := by
  unfold budanCount budanSequence
  simp [signChangesInList]

/-- V_p(x) for a constant polynomial is 0 (one entry, no sign changes). -/
theorem budanCount_C (c : ℝ) (x : ℝ) : budanCount (C c) x = 0 := by
  unfold budanCount budanSequence
  simp only [Polynomial.natDegree_C, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil]
  unfold signChangesInList
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp

/-
## Part IV: Count of Roots in Intervals
-/

/-- Count of roots of p in the half-open interval (a, b], with multiplicity. -/
noncomputable def rootsInInterval (p : ℝ[X]) (a b : ℝ) : ℕ :=
  if p = 0 then 0
  else Multiset.card (p.roots.filter (fun r => a < r ∧ r ≤ b))

@[simp]
theorem rootsInInterval_zero (a b : ℝ) : rootsInInterval (0 : ℝ[X]) a b = 0 := by
  simp [rootsInInterval]

/-- A nonzero constant has 0 roots in any interval. -/
theorem rootsInInterval_C (c : ℝ) (hc : c ≠ 0) (a b : ℝ) :
    rootsInInterval (C c) a b = 0 := by
  simp only [rootsInInterval, C_eq_zero.not.mpr hc, ↓reduceIte]
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro r hr
  exfalso
  have hmem := (mem_roots (C_ne_zero.mpr hc)).mp hr
  rw [Polynomial.IsRoot, eval_C] at hmem
  exact hc hmem

/-
## Part V: Budan's Theorem — Main Results
-/

/-- **Axiom: Budan's Theorem (Upper Bound)**

The number of roots of p in (a, b], counted with multiplicity, is at most
V_p(a) - V_p(b). The proof proceeds by strong induction on the degree,
using Rolle's theorem: between consecutive roots of p, the derivative p'
has a root, and sign changes decrease accordingly at each derivative level. -/
axiom budan_upper_bound_axiom (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b

theorem budan_upper_bound (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (hab : a < b) :
    rootsInInterval p a b ≤ budanCount p a - budanCount p b :=
  budan_upper_bound_axiom p hp a b hab

/-- **Axiom: Budan's Theorem (Parity)**

V_p(a) - V_p(b) and the number of roots in (a,b] differ by an even number.
This follows from complex roots coming in conjugate pairs: each pair of
non-real roots contributes 0 or 2 to the variation difference. -/
axiom budan_parity_axiom (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (hab : a < b) :
    Even (budanCount p a - budanCount p b - rootsInInterval p a b)

theorem budan_parity (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (hab : a < b) :
    Even (budanCount p a - budanCount p b - rootsInInterval p a b) :=
  budan_parity_axiom p hp a b hab

/-- **Budan's Theorem (Combined)**

The number of roots in (a, b] equals V_p(a) - V_p(b) minus some non-negative
even number 2k. -/
theorem budan_theorem (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (hab : a < b) :
    ∃ k : ℕ, rootsInInterval p a b + 2 * k = budanCount p a - budanCount p b := by
  have hbound := budan_upper_bound p hp a b hab
  have hparity := budan_parity p hp a b hab
  obtain ⟨m, hm⟩ := hparity
  exact ⟨m, by omega⟩

/-
## Part VI: Root Isolation Certificates
-/

/-- **Root-free certificate**: If V_p(a) = V_p(b), then p has no roots in (a,b]. -/
theorem no_roots_of_equal_budanCount (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ) (hab : a < b)
    (heq : budanCount p a = budanCount p b) :
    rootsInInterval p a b = 0 := by
  have := budan_upper_bound p hp a b hab; omega

/-- **Unique root certificate**: If V_p(a) - V_p(b) = 1, then p has exactly
    one root in (a,b].

    Proof: rootsInInterval ≤ 1 from the bound, and (1 - rootsInInterval) must
    be even by parity. Since 1 - 0 = 1 is odd, rootsInInterval ≠ 0. -/
theorem unique_root_of_budanCount_diff_one (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ)
    (hab : a < b) (hdiff : budanCount p a = budanCount p b + 1) :
    rootsInInterval p a b = 1 := by
  have hbound := budan_upper_bound p hp a b hab
  have hparity := budan_parity p hp a b hab
  have h1 : budanCount p a - budanCount p b = 1 := by omega
  rw [h1] at hbound hparity
  by_contra hne1
  have h0 : rootsInInterval p a b = 0 := by omega
  rw [h0] at hparity; simp at hparity

/-- **Two-or-zero certificate**: If V_p(a) - V_p(b) = 2, then p has 0 or 2
    roots in (a,b]. -/
theorem zero_or_two_roots_of_budanCount_diff_two (p : ℝ[X]) (hp : p ≠ 0) (a b : ℝ)
    (hab : a < b) (hdiff : budanCount p a = budanCount p b + 2) :
    rootsInInterval p a b = 0 ∨ rootsInInterval p a b = 2 := by
  have hbound := budan_upper_bound p hp a b hab
  have hparity := budan_parity p hp a b hab
  have h2 : budanCount p a - budanCount p b = 2 := by omega
  rw [h2] at hbound hparity
  interval_cases (rootsInInterval p a b) <;> simp_all

/-
## Part VII: Descartes' Rule as Special Case
-/

/-- **Axiom: For large x, V_p(x) = 0.**

    For x sufficiently large, each derivative p⁽ᵏ⁾(x) is dominated by its
    leading term, which has the same sign as the leading coefficient times
    a positive factorial. So all entries of the Budan-Fourier sequence share
    the same sign, giving 0 sign changes. -/
axiom budanCount_large_axiom (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ M : ℝ, ∀ x, x > M → budanCount p x = 0

theorem budanCount_eventually_zero (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ M : ℝ, ∀ x, x > M → budanCount p x = 0 :=
  budanCount_large_axiom p hp

/-- Every element of a finite multiset of reals is bounded above. -/
private theorem multiset_bounded_above (s : Multiset ℝ) :
    ∃ R : ℝ, ∀ r ∈ s, r ≤ R := by
  induction s using Multiset.induction with
  | empty => exact ⟨0, fun _ h => absurd h (Multiset.not_mem_zero _)⟩
  | cons a s ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨max a R, fun r hr => by
      rcases Multiset.mem_cons.mp hr with rfl | hmem
      · exact le_max_left r R
      · exact le_trans (hR r hmem) (le_max_right a R)⟩

theorem descartes_from_budan (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      Multiset.card (p.roots.filter (0 < ·)) ≤ budanCount p 0 := by
  obtain ⟨M, hM⟩ := budanCount_eventually_zero p hp
  obtain ⟨R, hR⟩ := multiset_bounded_above p.roots
  set B := max 1 (max (M + 1) (R + 1)) with hB_def
  use B
  refine ⟨by positivity, ?_⟩
  -- V(B) = 0 since B > M
  have hBM : B > M := by
    calc M < M + 1 := by linarith
    _ ≤ max (M + 1) (R + 1) := le_max_left _ _
    _ ≤ max 1 (max (M + 1) (R + 1)) := le_max_right _ _
  have hVB : budanCount p B = 0 := hM B hBM
  -- B > 0
  have hB0 : (0 : ℝ) < B := by positivity
  -- rootsInInterval p 0 B ≤ budanCount p 0 - budanCount p B = budanCount p 0
  have hbound := budan_upper_bound p hp 0 B hB0
  rw [hVB, Nat.sub_zero] at hbound
  -- Suffices: card(roots.filter (0 < ·)) ≤ rootsInInterval p 0 B
  suffices hsuff : Multiset.card (p.roots.filter (0 < ·)) ≤ rootsInInterval p 0 B by
    linarith
  -- rootsInInterval p 0 B = card(roots.filter (0 < · ∧ · ≤ B))
  simp only [rootsInInterval, hp, ↓reduceIte]
  -- The filter (0 < · ∧ · ≤ B) is a subset of filter (0 < ·) ... wait, it's the other way:
  -- Every positive root r satisfies r ≤ R < R + 1 ≤ B, so the two filters are equal
  suffices heq : p.roots.filter (fun r => 0 < r ∧ r ≤ B) = p.roots.filter (0 < ·) by
    rw [heq]
  apply Multiset.filter_congr
  intro r hr
  constructor
  · exact fun ⟨h, _⟩ => h
  · intro h
    refine ⟨h, le_trans (hR r hr) ?_⟩
    have : R ≤ R + 1 := by linarith
    calc R ≤ R + 1 := this
    _ ≤ max (M + 1) (R + 1) := le_max_right _ _
    _ ≤ B := le_max_right _ _

/-
## Part VIII: Connection to Coefficient Sign Variations

V_p(0) relates to the coefficient sign variation count because
p⁽ᵏ⁾(0) = k! · aₖ, and k! > 0 preserves signs.
-/

/-- iterDeriv equals Mathlib's iterated derivative via Function.iterate. -/
theorem iterDeriv_eq_iterate (p : ℝ[X]) (k : ℕ) :
    iterDeriv p k = derivative^[k] p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterDeriv_succ, ih]
    -- derivative (derivative^[k] p) = derivative^[k+1] p
    -- by Function.iterate_succ' : f^[n+1] = f ∘ f^[n]
    exact (congrFun (Function.iterate_succ' derivative k) p).symm

/-- General coefficient formula for iterated derivatives.
    (p⁽ᵏ⁾).coeff j = descFactorial(j+k, k) * p.coeff(j+k) -/
private theorem iterDeriv_coeff (p : ℝ[X]) (k j : ℕ) :
    (iterDeriv p k).coeff j =
      (↑((j + k).descFactorial k) : ℝ) * p.coeff (j + k) := by
  induction k generalizing j with
  | zero => simp [Nat.descFactorial]
  | succ k ih =>
    simp only [iterDeriv_succ, coeff_derivative]
    rw [ih (j + 1)]
    -- Goal involves nsmul and cast arithmetic
    -- (↑(j + 1) : ℝ) * (↑((j + 1 + k).descFactorial k) * p.coeff (j + 1 + k))
    -- = ↑((j + (k + 1)).descFactorial (k + 1)) * p.coeff (j + (k + 1))
    have hj1k : j + 1 + k = j + k + 1 := by omega
    have hjk1 : j + (k + 1) = j + k + 1 := by omega
    rw [hj1k, hjk1]
    -- Use descFactorial recurrence: n.descFactorial (k+1) = (n-k) * n.descFactorial k
    have hdf : (j + k + 1).descFactorial (k + 1) =
        (j + k + 1 - k) * (j + k + 1).descFactorial k :=
      Nat.descFactorial_succ (j + k + 1) k
    have hjk : j + k + 1 - k = j + 1 := by omega
    rw [hdf, hjk]
    push_cast
    ring

/-- p⁽ᵏ⁾(0) = k! · (coefficient k of p).

    The k-th derivative at 0 extracts the k-th coefficient up to factorial. -/
private theorem poly_eval_at_zero (q : ℝ[X]) : q.eval 0 = q.coeff 0 := by
  rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.zero_lt_succ _))
    (fun b _ hb => by simp [zero_pow hb])]
  simp

theorem iterDeriv_eval_zero (p : ℝ[X]) (k : ℕ) :
    (iterDeriv p k).eval 0 = (k.factorial : ℝ) * p.coeff k := by
  rw [poly_eval_at_zero, iterDeriv_coeff]
  simp [Nat.descFactorial_self]

/-- Pointwise positive scaling preserves sign changes.
    If each w(i) > 0, then sign changes in [w(0)*a(0), w(1)*a(1), ...] =
    sign changes in [a(0), a(1), ...]. -/
private theorem signChangesInList_pos_scale {n : ℕ}
    (a : ℕ → ℝ) (w : ℕ → ℝ) (hw : ∀ k, 0 < w k) :
    signChangesInList ((List.range n).map (fun k => w k * a k)) =
    signChangesInList ((List.range n).map a) := by
  -- Key: filtering nonzero and mapping signs both agree under positive scaling
  -- Strategy: show both sides produce the same ±1 sign list
  simp only [signChangesInList]
  -- The filter and sign-map on the scaled list equals that on the unscaled list
  -- because w k > 0 preserves zero-ness and sign of each entry
  suffices h : (((List.range n).map (fun k => w k * a k)).filter (· ≠ 0)
      ).map (fun x => if x > 0 then (1 : ℤ) else -1) =
      (((List.range n).map a).filter (· ≠ 0)
      ).map (fun x => if x > 0 then (1 : ℤ) else -1) by
    rw [h]
  -- Inline: filtering and mapping on list of w(k)*a(k) vs a(k)
  induction (List.range n) with
  | nil => simp
  | cons k ks ih =>
    by_cases hak : a k = 0
    · -- a k = 0 implies w k * a k = 0 too
      -- Both (w k * 0) and 0 are filtered out, so reduce to ih
      convert ih using 1 <;> simp [hak]
    · -- a k ≠ 0 implies w k * a k ≠ 0, and they share the same sign
      have hwak : w k * a k ≠ 0 := mul_ne_zero (ne_of_gt (hw k)) hak
      -- Both filter_cons keep the head
      -- After simp, goal should be: sign(wk*ak) :: tail = sign(ak) :: tail
      -- The filter step keeps both entries; we need sign equality + ih
      have hsign : (if w k * a k > 0 then (1 : ℤ) else -1) =
          (if a k > 0 then (1 : ℤ) else -1) := by
        by_cases hpos : a k > 0
        · simp [mul_pos (hw k) hpos, hpos]
        · push_neg at hpos
          have han : a k < 0 := lt_of_le_of_ne hpos hak
          have : w k * a k < 0 := mul_neg_of_pos_of_neg (hw k) han
          simp [not_lt.mpr (le_of_lt this), not_lt.mpr (le_of_lt han)]
      -- Convert the goal to match ih + hsign
      convert congr_arg₂ List.cons hsign ih using 2 <;> simp [hwak, hak]

/-- Since k! > 0, the sign of p⁽ᵏ⁾(0) equals the sign of aₖ.
    Therefore V_p(0) = signVariations of the coefficient sequence. -/
theorem budanCount_zero_eq_coeff_sign_changes (p : ℝ[X]) (hp : p ≠ 0) :
    budanCount p 0 = signChangesInList
      ((List.range (p.natDegree + 1)).map p.coeff) := by
  simp only [budanCount, budanSequence]
  -- Each entry: (iterDeriv p k).eval 0 = k! * p.coeff k
  have hseq : (List.range (p.natDegree + 1)).map (fun k => (iterDeriv p k).eval 0) =
      (List.range (p.natDegree + 1)).map (fun k => (k.factorial : ℝ) * p.coeff k) := by
    apply List.map_congr_left
    intro k _
    exact iterDeriv_eval_zero p k
  rw [hseq]
  exact signChangesInList_pos_scale p.coeff (fun k => (k.factorial : ℝ))
    (fun k => Nat.cast_pos.mpr (Nat.factorial_pos k))

/-
## Part IX: Structural Theorems
-/

/-- V_p(x) is bounded by the degree of p.
    (A list of n+1 entries has at most n sign changes.) -/
theorem budanCount_le_natDegree (p : ℝ[X]) (x : ℝ) :
    budanCount p x ≤ p.natDegree := by
  unfold budanCount
  have := signChangesInList_le_pred_length (budanSequence p p.natDegree x)
  simp [budanSequence_length] at this
  exact this

/-- Iterated derivative commutes with constant multiplication. -/
theorem iterDeriv_C_mul (c : ℝ) (p : ℝ[X]) (k : ℕ) :
    iterDeriv (C c * p) k = C c * iterDeriv p k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [iterDeriv_succ, ih, derivative_C_mul]

/-- Filtering zeros commutes with nonzero scaling. -/
private theorem filter_nonzero_map_mul (l : List ℝ) (c : ℝ) (hc : c ≠ 0) :
    (l.map (c * ·)).filter (· ≠ 0) = (l.filter (· ≠ 0)).map (c * ·) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    by_cases ha : a = 0
    · simp only [ha, mul_zero, List.map_cons]
      simp only [List.filter_cons, ne_eq]
      simp only [not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact ih
    · have hca : c * a ≠ 0 := mul_ne_zero hc ha
      simp only [List.map_cons, List.filter_cons, ne_eq]
      simp only [hca, not_false_eq_true, decide_true, ↓reduceIte,
        ha, List.map_cons]
      rw [ih]

/-- Negating all entries in a ±1 list preserves adjacent difference counts. -/
private theorem countAdjacentDiffs_neg : ∀ (l : List ℤ),
    countAdjacentDiffs (l.map (· * -1)) = countAdjacentDiffs l
  | [] => by simp
  | [_] => by simp
  | a :: b :: rest => by
    simp only [List.map_cons, countAdjacentDiffs, mul_neg_one]
    have ih := countAdjacentDiffs_neg (b :: rest)
    simp only [List.map_cons, mul_neg_one] at ih
    rw [ih]
    congr 1
    simp only [ne_eq, neg_inj]

/-- Sign mapping commutes with nonzero scaling: sign(c*x) determined by sign(c) and sign(x). -/
private theorem signChangesInList_nonzero_filter_scale (l' : List ℝ) (c : ℝ) (hc : c ≠ 0)
    (hl' : ∀ x ∈ l', x ≠ 0) :
    countAdjacentDiffs (l'.map (fun x => if c * x > 0 then (1 : ℤ) else -1)) =
    countAdjacentDiffs (l'.map (fun x => if x > 0 then (1 : ℤ) else -1)) := by
  rcases lt_or_gt_of_ne hc with hc_neg | hc_pos
  · -- c < 0: sign(c*x) = -sign(x), all signs flip, but diffs preserved
    have hsign : ∀ x : ℝ, x ≠ 0 →
        (if c * x > 0 then (1 : ℤ) else -1) = (if x > 0 then (1 : ℤ) else -1) * -1 := by
      intro x hx
      by_cases hxp : x > 0
      · have : c * x < 0 := mul_neg_of_neg_of_pos hc_neg hxp
        simp [not_lt.mpr (le_of_lt this), hxp]
      · push_neg at hxp
        have hxn : x < 0 := lt_of_le_of_ne hxp hx
        have : c * x > 0 := mul_pos_of_neg_of_neg hc_neg hxn
        simp [this, not_lt.mpr (le_of_lt hxn)]
    -- Replace map with composition of sign and negate
    have hmap : l'.map (fun x => if c * x > 0 then (1 : ℤ) else -1) =
        (l'.map (fun x => if x > 0 then (1 : ℤ) else -1)).map (· * -1) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro x hx
      exact hsign x (hl' x hx)
    rw [hmap]
    exact countAdjacentDiffs_neg _
  · -- c > 0: sign(c*x) = sign(x)
    congr 1
    apply List.map_congr_left
    intro x hx
    have hx' := hl' x hx
    by_cases hxp : x > 0
    · have : c * x > 0 := mul_pos hc_pos hxp
      simp [this, hxp]
    · push_neg at hxp
      have hxn : x < 0 := lt_of_le_of_ne hxp hx'
      have : c * x < 0 := mul_neg_of_pos_of_neg hc_pos hxn
      simp [not_lt.mpr (le_of_lt this), not_lt.mpr (le_of_lt hxn)]

/-- Scaling by a nonzero constant preserves sign changes in a list. -/
private theorem signChangesInList_map_mul (l : List ℝ) (c : ℝ) (hc : c ≠ 0) :
    signChangesInList (l.map (c * ·)) = signChangesInList l := by
  simp only [signChangesInList]
  rw [filter_nonzero_map_mul l c hc]
  -- After filtering, all remaining elements are nonzero
  have hmem : ∀ x ∈ l.filter (· ≠ 0), x ≠ 0 := by
    intro x hx
    have := (List.mem_filter.mp hx).2
    simpa using this
  -- The sign map applied to (c * ·) on the filtered list
  simp only [List.map_map]
  exact signChangesInList_nonzero_filter_scale (l.filter (· ≠ 0)) c hc hmem

/-- Scaling by a nonzero constant preserves the Budan count.
    Since (c·p)⁽ᵏ⁾ = c·p⁽ᵏ⁾ and c ≠ 0 preserves all signs. -/
theorem budanCount_smul (p : ℝ[X]) (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    budanCount (C c * p) x = budanCount p x := by
  simp only [budanCount, budanSequence]
  have hdeg : (C c * p).natDegree = p.natDegree := by
    by_cases hp : p = 0
    · simp [hp]
    · exact Polynomial.natDegree_C_mul hc
  rw [hdeg]
  -- The sequence for C c * p is c times the sequence for p
  have hseq : (List.range (p.natDegree + 1)).map (fun k => (iterDeriv (C c * p) k).eval x) =
      ((List.range (p.natDegree + 1)).map (fun k => (iterDeriv p k).eval x)).map (c * ·) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro k _
    simp [iterDeriv_C_mul, Polynomial.eval_mul, Polynomial.eval_C]
  rw [hseq]
  exact signChangesInList_map_mul _ c hc

/-
## Part X: Root Count Additivity
-/

/-- Root counts are additive when splitting an interval at a point. -/
theorem rootsInInterval_split (p : ℝ[X]) (hp : p ≠ 0) (a c b : ℝ)
    (hac : a < c) (hcb : c < b) :
    rootsInInterval p a b = rootsInInterval p a c + rootsInInterval p c b := by
  simp only [rootsInInterval, hp, ↓reduceIte]
  rw [← Multiset.card_add]
  congr 1
  ext x
  simp only [Multiset.count_add, Multiset.count_filter]
  by_cases ha : a < x <;> by_cases hc1 : x ≤ c <;> by_cases hb : x ≤ b <;>
      by_cases hc2 : c < x <;> simp_all <;> linarith

/-- Budan count differences are additive: V(a) - V(b) = (V(a) - V(c)) + (V(c) - V(b)).
    This is just arithmetic: the V(c) terms cancel. -/
theorem budanCount_diff_split (p : ℝ[X]) (a c b : ℝ)
    (h1 : budanCount p c ≤ budanCount p a)
    (h2 : budanCount p b ≤ budanCount p c) :
    budanCount p a - budanCount p b =
    (budanCount p a - budanCount p c) + (budanCount p c - budanCount p b) := by
  omega

/-
## Part XI: Rolle's Theorem Connection

Rolle's theorem is the key ingredient in the inductive proof of Budan's theorem.
We prove it here as a bridge between calculus and algebra.
-/

/-- Between two distinct roots of p, the derivative has a root.
    This is the polynomial version of Rolle's theorem. -/
theorem rolle_polynomial (p : ℝ[X]) (a b : ℝ) (hab : a < b)
    (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ c, a < c ∧ c < b ∧ (derivative p).eval c = 0 := by
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) :=
    p.continuous.continuousOn
  have heq : p.eval a = p.eval b := ha.trans hb.symm
  obtain ⟨c, ⟨hac, hcb⟩, hderiv⟩ := exists_deriv_eq_zero hab hcont heq
  exact ⟨c, hac, hcb, by simp only [Polynomial.deriv] at hderiv; exact hderiv⟩

/-- Between n+1 distinct ordered roots of p, the derivative has at least n roots
    (one between each consecutive pair). -/
theorem n_roots_derivative_roots (p : ℝ[X]) (n : ℕ)
    (rootsF : Fin (n + 1) → ℝ)
    (hstrict : StrictMono rootsF)
    (heval : ∀ i, p.eval (rootsF i) = 0) :
    ∀ i : Fin n, ∃ c, rootsF i.castSucc < c ∧ c < rootsF i.succ ∧
      (derivative p).eval c = 0 := by
  intro i
  have hlt : i.castSucc < i.succ := i.castSucc_lt_succ
  exact rolle_polynomial p _ _ (hstrict hlt) (heval i.castSucc) (heval i.succ)

/-
## Part XII: Sturm Chains (Framework)

Budan's theorem gives bounds with a parity gap; Sturm's theorem gives
exact counts by replacing the derivative sequence with a pseudo-remainder
sequence. We define the framework for future formalization.
-/

/-- A chain of polynomials for root counting. -/
structure PolyChain (m : ℕ) where
  polys : Fin (m + 1) → ℝ[X]

/-- The sign variation count for a polynomial chain at a point x. -/
noncomputable def chainVariation {m : ℕ} (sc : PolyChain m) (x : ℝ) : ℕ :=
  signChangesInList ((List.finRange (m + 1)).map (fun k =>
    (sc.polys k).eval x))

/-- The Budan-Fourier chain: [p, p', p'', ..., p⁽ⁿ⁾]. -/
noncomputable def budanChain (p : ℝ[X]) : PolyChain p.natDegree where
  polys k := iterDeriv p k

/-- The Budan chain's variation equals budanCount. -/
theorem chainVariation_budanChain (p : ℝ[X]) (x : ℝ) :
    chainVariation (budanChain p) x = budanCount p x := by
  simp only [chainVariation, budanChain, budanCount, budanSequence]
  congr 1
  have : (List.finRange (p.natDegree + 1)).map (fun k : Fin _ => (iterDeriv p ↑k).eval x) =
      ((List.finRange (p.natDegree + 1)).map Fin.val).map (fun k => (iterDeriv p k).eval x) := by
    rw [List.map_map]; rfl
  rw [this, List.map_coe_finRange_eq_range]

end BudanTheorem
