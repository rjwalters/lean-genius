/-
  Lamé's Theorem, Sharp Side: Fibonacci Pairs Are the Exact Euclidean Worst Case
  Open Question OQ-01 from GCDAlgorithmOQ01OQ03

  The parent entry (gcd-algorithm-oq-01-oq-03, "Binet's Formula and Lamé's
  5-Digit Bound") proves the *upper* side of Lamé's theorem: the number of
  Euclidean steps on inputs below 10^k is O(k), because Fibonacci numbers grow
  at least geometrically (fib(5k+2) ≥ 10^k).

  This file proves the matching *sharp* side — that consecutive Fibonacci pairs
  realize the worst case exactly:

      euclidSteps (fib (n+2)) (fib (n+1)) = n        (for n ≥ 1)

  Together with the upper bound, this pins the Euclidean worst case to the
  Fibonacci sequence: no input of a given size forces more steps, and the
  Fibonacci pair forces exactly that many. This is the original content of
  Lamé (1844), historically the first complexity analysis of an algorithm.

  We additionally prove the *minimality* direction:

      0 < b < a  ∧  euclidSteps a b = n  →  fib (n+1) ≤ b  ∧  fib (n+2) ≤ a

  i.e. any pair taking n steps is at least as large as the n-th Fibonacci pair,
  so the Fibonacci pairs are the smallest inputs achieving each step count.

  Proof idea (exact count): the Euclidean recursion on (fib(n+2), fib(n+1))
  reduces in one step to (fib(n+1), fib(n+2) mod fib(n+1)) = (fib(n+1), fib n),
  because fib(n+2) = fib(n+1) + fib n with 0 ≤ fib n < fib(n+1). Induction.

  References:
  - Lamé, G. (1844). Note sur la limite du nombre des divisions dans la
    recherche du plus grand commun diviseur entre deux nombres entiers.
  - GCDAlgorithmOQ01OQ03.lean (the digit-count upper bound).
  - BinaryGcdOQ01.lean (definition of euclidSteps).
-/
import Mathlib
import Proofs.BinaryGcdOQ01

namespace GCDAlgorithmOQ01OQ03OQ01

open Nat BinaryGcdOQ01

-- ═══════════════════════════════════════════════════════════════════
-- PART I: BASIC RECURSION LEMMAS FOR euclidSteps
-- ═══════════════════════════════════════════════════════════════════

/-- `euclidSteps a 0 = 0`: a run with second argument zero takes no steps. -/
private lemma euclidSteps_zero_right (a : ℕ) : euclidSteps a 0 = 0 := by
  cases a with
  | zero => exact euclidSteps.eq_1 0
  | succ a' => exact euclidSteps.eq_2 _ (by omega)

/-- Clean recursion for the Euclidean step counter when `0 < b < a`:
    `euclidSteps a b = 1 + euclidSteps b (a % b)`.

    The definition `euclidSteps` branches on `b' + 1 ≤ a'` (i.e. `b < a`); the
    hypothesis `b < a` selects exactly the first branch. -/
private theorem euclidSteps_step (a b : ℕ) (hb : 0 < b) (hba : b < a) :
    euclidSteps a b = 1 + euclidSteps b (a % b) := by
  obtain ⟨a', rfl⟩ : ∃ k, a = k + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
  rw [euclidSteps.eq_3, if_pos (by omega : b' + 1 ≤ a')]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE FIBONACCI MOD IDENTITY
-- ═══════════════════════════════════════════════════════════════════

/-- `fib (n+1) < fib (n+2)` for `n ≥ 1` (strict monotonicity above index 1). -/
private lemma fib_succ_lt (n : ℕ) (hn : 1 ≤ n) : fib (n + 1) < fib (n + 2) :=
  Nat.fib_lt_fib_succ (show 2 ≤ n + 1 by omega)

/-- The Euclidean reduction step on a Fibonacci pair:
    `fib (n+2) % fib (n+1) = fib n` for `n ≥ 2`.

    Because `fib (n+2) = fib n + fib (n+1)` with `0 ≤ fib n < fib (n+1)`. -/
private lemma fib_mod (n : ℕ) (hn : 2 ≤ n) : fib (n + 2) % fib (n + 1) = fib n := by
  have hadd : fib (n + 2) = fib n + fib (n + 1) := Nat.fib_add_two
  have hlt : fib n < fib (n + 1) := Nat.fib_lt_fib_succ hn
  calc fib (n + 2) % fib (n + 1)
      = (fib n + fib (n + 1)) % fib (n + 1) := by rw [hadd]
    _ = fib n % fib (n + 1) := by rw [Nat.add_mod_right]
    _ = fib n := Nat.mod_eq_of_lt hlt

-- ═══════════════════════════════════════════════════════════════════
-- PART III: EXACT WORST-CASE STEP COUNT (LAMÉ SHARPNESS)
-- ═══════════════════════════════════════════════════════════════════

/-- **Main Theorem (Lamé sharpness).** Consecutive Fibonacci numbers realize the
    Euclidean worst case exactly:

        euclidSteps (fib (n+2)) (fib (n+1)) = n        for every n ≥ 1.

    Proof by induction from the base `n = 1`:
    `euclidSteps (fib 3) (fib 2) = euclidSteps 2 1 = 1`, and the inductive step
    uses `euclidSteps_step` together with `fib (n+3) % fib (n+2) = fib (n+1)`. -/
theorem euclidSteps_fib (n : ℕ) (hn : 1 ≤ n) :
    euclidSteps (fib (n + 2)) (fib (n + 1)) = n := by
  induction n, hn using Nat.le_induction with
  | base =>
    -- fib 3 = 2, fib 2 = 1; euclidSteps 2 1 = 1 + euclidSteps 1 0 = 1
    have hf2 : fib 2 = 1 := by decide
    have hf3 : fib 3 = 2 := by decide
    rw [show (1 : ℕ) + 2 = 3 from rfl, show (1 : ℕ) + 1 = 2 from rfl, hf3, hf2,
        euclidSteps_step 2 1 (by norm_num) (by norm_num),
        show (2 : ℕ) % 1 = 0 from rfl, euclidSteps_zero_right]
  | succ n hn ih =>
    have hpos : 0 < fib (n + 2) := Nat.fib_pos.mpr (by omega)
    have hlt : fib (n + 2) < fib (n + 3) := fib_succ_lt (n + 1) (by omega)
    rw [euclidSteps_step (fib (n + 3)) (fib (n + 2)) hpos hlt,
        fib_mod (n + 1) (by omega), ih]
    omega

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: MINIMALITY — FIBONACCI PAIRS ARE THE SMALLEST WORST CASES
-- ═══════════════════════════════════════════════════════════════════

/-- **Minimality (Lamé lower bound).** Any pair `0 < b < a` whose Euclidean run
    takes `n` steps is at least as large as the n-th Fibonacci pair:

        euclidSteps a b = n  →  fib (n + 1) ≤ b  ∧  fib (n + 2) ≤ a.

    Hence the Fibonacci pair `(fib (n+2), fib (n+1))` is the *smallest* input
    forcing `n` Euclidean steps — the sharp form of Lamé's theorem.

    Proof: strong induction on `a`. One Euclidean step sends `(a, b)` to
    `(b, a % b)` with `a % b < b`, decreasing the first argument; the inductive
    hypothesis bounds the smaller pair by Fibonacci numbers, and
    `a ≥ b + (a % b)` (since the quotient is `≥ 1` as `b ≤ a`) lifts the bound
    via the Fibonacci recurrence `fib (n+2) = fib (n+1) + fib n`. -/
theorem fib_le_of_euclidSteps (a : ℕ) :
    ∀ b n, 0 < b → b < a → euclidSteps a b = n →
      fib (n + 1) ≤ b ∧ fib (n + 2) ≤ a := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b n hb hba hsteps
    -- Peel one Euclidean step.
    rw [euclidSteps_step a b hb hba] at hsteps
    have hr_lt : a % b < b := Nat.mod_lt a hb
    -- a ≥ b + a % b, since the quotient a / b ≥ 1.
    have hq1 : 1 ≤ a / b := (Nat.one_le_div_iff hb).mpr (le_of_lt hba)
    have hdm : b * (a / b) + a % b = a := Nat.div_add_mod a b
    have hq : b ≤ b * (a / b) := le_mul_of_one_le_right (Nat.zero_le b) hq1
    have hge : b + a % b ≤ a := by omega
    cases n with
    | zero =>
      -- 1 + euclidSteps b (a % b) = 0 is impossible.
      exact absurd hsteps (by omega)
    | succ m =>
      have hsteps' : euclidSteps b (a % b) = m := by omega
      rcases Nat.eq_zero_or_pos (a % b) with hr0 | hrpos
      · -- a % b = 0: the run ends, so m = 0 and n = 1.
        rw [hr0, euclidSteps_zero_right] at hsteps'
        subst hsteps'
        -- need fib 2 ≤ b and fib 3 ≤ a, i.e. 1 ≤ b and 2 ≤ a
        refine ⟨by simpa using hb, ?_⟩
        have : 2 ≤ a := by omega
        simpa using this
      · -- a % b > 0: apply IH to (b, a % b) with b < a.
        obtain ⟨hr_fib, hb_fib⟩ := ih b hba (a % b) m hrpos hr_lt hsteps'
        -- hr_fib : fib (m+1) ≤ a % b,  hb_fib : fib (m+2) ≤ b
        refine ⟨hb_fib, ?_⟩
        -- fib (m+3) = fib (m+1) + fib (m+2) ≤ (a % b) + b ≤ a
        have hrec : fib (m + 3) = fib (m + 1) + fib (m + 2) := Nat.fib_add_two
        calc fib (m + 1 + 2) = fib (m + 3) := by ring_nf
          _ = fib (m + 1) + fib (m + 2) := hrec
          _ ≤ a % b + b := Nat.add_le_add hr_fib hb_fib
          _ = b + a % b := by ring
          _ ≤ a := hge

-- ═══════════════════════════════════════════════════════════════════
-- PART V: COMBINED SHARP CHARACTERIZATION
-- ═══════════════════════════════════════════════════════════════════

/-- **Sharp Lamé characterization.** For `n ≥ 1`, the Fibonacci pair
    `(fib (n+2), fib (n+1))` takes exactly `n` Euclidean steps, and every pair
    `0 < b < a` taking `n` steps satisfies `fib (n+2) ≤ a` and `fib (n+1) ≤ b`.
    So the Fibonacci pair is a minimal `n`-step input. -/
theorem lame_sharp (n : ℕ) (hn : 1 ≤ n) :
    euclidSteps (fib (n + 2)) (fib (n + 1)) = n ∧
    (∀ a b, 0 < b → b < a → euclidSteps a b = n → fib (n + 2) ≤ a ∧ fib (n + 1) ≤ b) := by
  refine ⟨euclidSteps_fib n hn, ?_⟩
  intro a b hb hba hsteps
  obtain ⟨h1, h2⟩ := fib_le_of_euclidSteps a b n hb hba hsteps
  exact ⟨h2, h1⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: CONCRETE VERIFICATIONS
-- ═══════════════════════════════════════════════════════════════════

-- The exact worst-case counts, verified computationally:
example : euclidSteps (fib 3) (fib 2) = 1 := by native_decide
example : euclidSteps (fib 6) (fib 5) = 4 := by native_decide
example : euclidSteps (fib 10) (fib 9) = 8 := by native_decide
example : euclidSteps (fib 12) (fib 11) = 10 := by native_decide

-- Minimality witness: (fib 7, fib 6) = (13, 8) takes 5 steps; no smaller pair does.
example : euclidSteps (fib 7) (fib 6) = 5 := by native_decide

end GCDAlgorithmOQ01OQ03OQ01
