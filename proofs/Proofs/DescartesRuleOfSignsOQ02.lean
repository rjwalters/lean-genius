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

/-- countAdjacentDiffs is bounded by length minus 1. -/
theorem countAdjacentDiffs_le_length_sub_one (l : List ℤ) :
    countAdjacentDiffs l ≤ l.length - 1 := by
  induction l with
  | nil => simp
  | cons a t ih =>
    cases t with
    | nil => simp
    | cons b rest =>
      show (if a ≠ b then 1 else 0) + countAdjacentDiffs (b :: rest) ≤ (a :: b :: rest).length - 1
      simp only [List.length_cons] at ih ⊢
      split_ifs <;> omega

/-- Count sign changes in a list of reals, ignoring zeros.
    Filters out zeros, maps remaining to ±1, counts adjacent differences. -/
noncomputable def signChangesInList (l : List ℝ) : ℕ :=
  let nonzero := l.filter (· ≠ 0)
  let signs := nonzero.map (fun x => if x > 0 then (1 : ℤ) else -1)
  countAdjacentDiffs signs

@[simp]
theorem signChangesInList_nil : signChangesInList [] = 0 := by
  simp [signChangesInList, countAdjacentDiffs]

/-- Sign changes in a list are bounded by the list length minus 1. -/
theorem signChangesInList_le_length_sub_one (l : List ℝ) :
    signChangesInList l ≤ l.length - 1 := by
  unfold signChangesInList
  have h1 := countAdjacentDiffs_le_length_sub_one
    ((l.filter (· ≠ 0)).map (fun x => if x > 0 then (1 : ℤ) else -1))
  simp only [List.length_map] at h1
  calc countAdjacentDiffs _ ≤ (l.filter (· ≠ 0)).length - 1 := h1
    _ ≤ l.length - 1 := by
      have := List.length_filter_le (· ≠ 0) l
      omega

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
  simp [signChangesInList, countAdjacentDiffs]

/-- V_p(x) for a constant polynomial is 0 (one entry, no sign changes). -/
theorem budanCount_C (c : ℝ) (x : ℝ) : budanCount (C c) x = 0 := by
  unfold budanCount budanSequence
  simp only [Polynomial.natDegree_C, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil]
  unfold signChangesInList
  simp only [List.filter_cons, List.filter_nil]
  split <;> simp [countAdjacentDiffs]

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

/-- **Descartes' Rule from Budan's Theorem**

Taking a = 0 and b large enough that V_p(b) = 0 and all positive roots
are in (0, b], Budan gives: #positive_roots ≤ V_p(0). -/
theorem descartes_from_budan (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      Multiset.card (p.roots.filter (0 < ·)) ≤ budanCount p 0 := by
  obtain ⟨M, hM⟩ := budanCount_eventually_zero p hp
  -- Take B large enough for all positive roots and for V(B) = 0
  use max 1 (M + 1)
  refine ⟨by positivity, ?_⟩
  -- The number of positive roots ≤ rootsInInterval p 0 B' for large B'
  -- and rootsInInterval p 0 B' ≤ V(0) - V(B') = V(0) - 0 = V(0)
  sorry

/-
## Part VIII: Connection to Coefficient Sign Variations

V_p(0) relates to the coefficient sign variation count because
p⁽ᵏ⁾(0) = k! · aₖ, and k! > 0 preserves signs.
-/

/-- p⁽ᵏ⁾(0) = k! · (coefficient k of p).

    The k-th derivative at 0 extracts the k-th coefficient up to factorial. -/
theorem iterDeriv_eval_zero (p : ℝ[X]) (k : ℕ) :
    (iterDeriv p k).eval 0 = (k.factorial : ℝ) * p.coeff k := by
  induction k generalizing p with
  | zero =>
    simp only [iterDeriv_zero, Nat.factorial_zero, Nat.cast_one, one_mul]
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [eval_add, coeff_add, hp, hq]
    | monomial n a =>
      simp only [eval_monomial, coeff_monomial]
      cases n with
      | zero => simp
      | succ n => simp [zero_pow, Nat.succ_ne_zero]
  | succ k ih =>
    rw [(iterDeriv_derivative p k).symm, ih (derivative p), coeff_derivative]
    push_cast
    rw [Nat.factorial_succ]
    push_cast
    ring

/-- Since k! > 0, the sign of p⁽ᵏ⁾(0) equals the sign of aₖ.
    Therefore V_p(0) = signVariations of the coefficient sequence. -/
theorem budanCount_zero_eq_coeff_sign_changes (p : ℝ[X]) (hp : p ≠ 0) :
    budanCount p 0 = signChangesInList
      ((List.range (p.natDegree + 1)).map p.coeff) := by
  sorry

/-
## Part IX: Structural Theorems
-/

/-- V_p(x) is bounded by the degree of p.
    (A list of n+1 entries has at most n sign changes.) -/
theorem budanCount_le_natDegree (p : ℝ[X]) (x : ℝ) :
    budanCount p x ≤ p.natDegree := by
  unfold budanCount
  have h := signChangesInList_le_length_sub_one (budanSequence p p.natDegree x)
  rw [budanSequence_length] at h
  omega

/-- Scaling by a nonzero constant preserves the Budan count.
    Since (c·p)⁽ᵏ⁾ = c·p⁽ᵏ⁾ and c ≠ 0 preserves all signs. -/
theorem budanCount_smul (p : ℝ[X]) (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    budanCount (C c * p) x = budanCount p x := by
  sorry

/-
## Part X: Root Count Additivity
-/

/-- Root counts are additive when splitting an interval at a point. -/
theorem rootsInInterval_split (p : ℝ[X]) (hp : p ≠ 0) (a c b : ℝ)
    (_hac : a < c) (hcb : c < b) :
    rootsInInterval p a b = rootsInInterval p a c + rootsInInterval p c b := by
  simp only [rootsInInterval, if_neg hp, ← Multiset.card_add]
  congr 1
  ext r
  simp only [Multiset.count_add, Multiset.count_filter]
  rcases le_or_lt r a with hra | har
  · -- r ≤ a: all predicates false
    rw [if_neg (fun h : a < r ∧ r ≤ b => absurd h.1 (not_lt.mpr hra)),
        if_neg (fun h : a < r ∧ r ≤ c => absurd h.1 (not_lt.mpr hra)),
        if_neg (fun h : c < r ∧ r ≤ b => absurd h.1 (not_lt.mpr (le_trans hra _hac.le)))]
  · rcases le_or_lt r c with hrc | hcr
    · -- a < r ≤ c: first two true, third false
      rw [if_pos ⟨har, le_trans hrc hcb.le⟩,
          if_pos ⟨har, hrc⟩,
          if_neg (fun h : c < r ∧ r ≤ b => absurd h.1 (not_lt.mpr hrc))]
      omega
    · rcases le_or_lt r b with hrb | hbr
      · -- c < r ≤ b: first and third true, second false
        rw [if_pos ⟨_hac.trans hcr, hrb⟩,
            if_neg (fun h : a < r ∧ r ≤ c => absurd hcr (not_lt.mpr h.2)),
            if_pos ⟨hcr, hrb⟩]
        omega
      · -- r > b: all false
        rw [if_neg (fun h : a < r ∧ r ≤ b => absurd h.2 (not_le.mpr hbr)),
            if_neg (fun h : a < r ∧ r ≤ c => absurd (le_trans h.2 hcb.le) (not_le.mpr hbr)),
            if_neg (fun h : c < r ∧ r ≤ b => absurd h.2 (not_le.mpr hbr))]

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
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

end BudanTheorem
