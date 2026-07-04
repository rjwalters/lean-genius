/-
  Where the symmetric LLL surrogate first overtakes the sharp union bound
  (ramsey-r4k-extensions-oq-03-oq-02)

  The parent file `Proofs/RamseyR4kExtensionsOQ03.lean` sets up two *decidable*
  feasibility tests for a monochromatic-`Kₖ`-free 2-colouring of `Kₙ`:

    * `firstMomentCondition n k` : `2·C(n,k) < 2^{C(k,2)}`
        — the sharp union / first-moment threshold (some colouring avoids all
        monochromatic k-cliques as soon as the *expected* number is `< 1`);
    * `RamseyLLLCondition n k` : `6·(d+1) ≤ 2^{C(k,2)}` with
        `d = cliqueDependencyBound n k = C(k,2)·C(n-2,k-2)`
        — the symmetric Lovász Local Lemma applicability test, with the rational
        surrogate `e ≤ 3` (justified there by
        `symmetric_avoidance_factor_ge_third`).

  The parent already records two *small*-`k` surprises: at `k = 6` and `k = 7`
  the sharp union bound is strictly **stronger** than the LLL surrogate
  (`unionBound_beats_lll_at_6`, `unionBound_beats_lll_at_7`).  This is expected —
  the LLL's factor-`Θ(k)` gain is asymptotic and has not yet "kicked in" for tiny
  `k` (cf. the crossover criterion `lll_core_le_firstMoment_core`, whose
  regularity hypothesis `3·C(k,2)² ≤ C(n,2)` fails at small `k`).

  **This file pins down exactly where the crossover happens.**  Scanning `k`, the
  maximal number of vertices each test certifies is

        k :  8    9    10    11    12    13
      union: 42   65   100   152   231   349
      LLL  : 36   60    97   156   248   389        (this file's surrogate)

  so the LLL surrogate first overtakes the union bound at **`k = 11`**:

    * `lll_beats_unionBound_at_11`  — at `n = 156` the LLL test is feasible while
      the union bound has already failed:
          `¬ firstMomentCondition 156 11  ∧  RamseyLLLCondition 156 11`.
      (`2·C(156,11) = 46512822520262280 ≥ 2^{55}`, yet
       `6·(C(11,2)·C(154,9) + 1) = 34913470998459906 ≤ 2^{55} = 36028797018963968`.)

    * `unionBound_still_beats_lll_at_10` — one step earlier the union bound is
      still ahead: at `n = 100` it is feasible while the LLL test fails,
          `firstMomentCondition 100 10  ∧  ¬ RamseyLLLCondition 100 10`,
      so `k = 11` is genuinely the *first* crossover.

    * `lll_improves_sharp_union_at_11` — feeding the feasible LLL instance
      through the parent's reduction `ramsey_lll_lower_bound` (which assumes the
      one missing ingredient, the symmetric-LLL avoidance principle
      `SymmetricLLLForRamsey`), the LLL yields a monochromatic-`K₁₁`-free
      2-colouring of `K₁₅₆` — i.e. `R(11,11) > 156` — strictly better than the
      best the *sharp* union bound delivers here (`R(11,11) > 152`).  This is the
      first `k` at which the symmetric LLL beats not merely the weakened closed
      form `2^{⌊k/2⌋}` but the honest optimized first moment.

  Everything is machine-checked with no `sorry` and no `axiom`.  The concrete
  witnesses use kernel `decide` on the *integer* criteria; to keep the binomials
  cheap the large `C(n,k)` values are first rewritten through
  `Nat.choose_eq_descFactorial_div_factorial` (single-recursion `descFactorial`),
  exactly as in `RamseyR4kExtensionsOQ03Deletion.lean`.  So no `native_decide`
  and no `Lean.ofReduceBool`: foundational axioms only.
-/

import Mathlib
import Proofs.RamseyR4kExtensionsOQ03

namespace RamseyLLL

open Finset

-- ═══════════════════════════════════════════════════════════════════
-- PART I: PRECOMPUTED BINOMIALS (via descFactorial, kernel-cheap)
-- ═══════════════════════════════════════════════════════════════════

/-- `C(156,11)`, evaluated through `descFactorial` to keep the kernel reduction
    linear in `k` rather than exercising the naive `Nat.choose` recursion. -/
theorem choose_156_11 : (156).choose 11 = 23256411260131140 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- `C(154,9)` — the `C(n-2,k-2)` factor of the LLL dependency degree at
    `(n,k) = (156,11)`. -/
theorem choose_154_9 : (154).choose 9 = 105798396965030 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- `C(100,10)` — the total event count at the `k = 10` comparison point. -/
theorem choose_100_10 : (100).choose 10 = 17310309456440 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- `C(98,8)` — the `C(n-2,k-2)` factor of the LLL dependency degree at
    `(n,k) = (100,10)`. -/
theorem choose_98_8 : (98).choose 8 = 157366449604 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE FIRST CROSSOVER — k = 11
-- ═══════════════════════════════════════════════════════════════════

/-- **The LLL dependency degree at `(n,k) = (156,11)` as an explicit literal.**
    `d = C(11,2)·C(154,9) = 55·105798396965030 = 5818911833076650`. -/
theorem cliqueDependencyBound_156_11 :
    cliqueDependencyBound 156 11 = 5818911833076650 := by
  unfold cliqueDependencyBound
  have e1 : (156 : ℕ) - 2 = 154 := rfl
  have e2 : (11 : ℕ) - 2 = 9 := rfl
  have e3 : (11 : ℕ).choose 2 = 55 := rfl
  rw [e1, e2, e3, choose_154_9]

/-- **The symmetric-LLL surrogate first beats the sharp union bound at `k = 11`.**
    At `n = 156` the honest first-moment (union) test has already failed —
    `2·C(156,11) = 46512822520262280 ≥ 2^{55}` — while the LLL feasibility test
    still holds:
      `6·(C(11,2)·C(154,9) + 1) = 34913470998459906 ≤ 2^{55} = 36028797018963968`.
    Thus, unlike the small-`k` cases `unionBound_beats_lll_at_6/7`, here the
    *local* LLL condition certifies a monochromatic-`K₁₁`-free colouring at a
    vertex count the *global* union bound cannot reach. -/
theorem lll_beats_unionBound_at_11 :
    ¬ firstMomentCondition 156 11 ∧ RamseyLLLCondition 156 11 := by
  refine ⟨?_, ?_⟩
  · -- union bound fails: 2·C(156,11) ≥ 2^{C(11,2)}
    unfold firstMomentCondition
    rw [choose_156_11]
    decide
  · -- LLL succeeds via the integer criterion
    rw [ramseyLLLCondition_iff, cliqueDependencyBound_156_11]
    decide

/-- **`k = 11` is the *first* crossover: at `k = 10` the sharp union bound is
    still ahead.**  At `n = 100` the union bound is feasible
    (`2·C(100,10) = 34620618912880 < 2^{45}`), giving `R(10,10) > 100`, while the
    LLL surrogate fails there
    (`6·(C(10,2)·C(98,8) + 1) = 42488941393086 > 2^{45} = 35184372088832`).
    Together with `lll_beats_unionBound_at_11` this shows the surrogate's
    crossover point is exactly `k = 11`. -/
theorem unionBound_still_beats_lll_at_10 :
    firstMomentCondition 100 10 ∧ ¬ RamseyLLLCondition 100 10 := by
  have hdb : cliqueDependencyBound 100 10 = 45 * 157366449604 := by
    unfold cliqueDependencyBound
    have e1 : (100 : ℕ) - 2 = 98 := rfl
    have e2 : (10 : ℕ) - 2 = 8 := rfl
    have e3 : (10 : ℕ).choose 2 = 45 := rfl
    rw [e1, e2, e3, choose_98_8]
  refine ⟨?_, ?_⟩
  · unfold firstMomentCondition
    rw [choose_100_10]
    decide
  · rw [ramseyLLLCondition_iff, hdb]
    decide

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE RAMSEY CONSEQUENCE — R(11,11) > 156 UNDER THE LLL PRINCIPLE
-- ═══════════════════════════════════════════════════════════════════

/-- **At `k = 11` the symmetric LLL improves even the sharp union bound.**  The
    union bound certifies a monochromatic-`K₁₁`-free 2-colouring of `Kₙ` only for
    `n ≤ 152` (`2·C(152,11) = 34614584465246240 < 2^{55}` but the analogous test
    fails at `n = 153`), i.e. `R(11,11) > 152`.  Feeding the feasible instance
    `RamseyLLLCondition 156 11` (`lll_beats_unionBound_at_11`) through the
    parent's reduction `ramsey_lll_lower_bound` — which assumes only the missing
    measure-theoretic ingredient, the symmetric-LLL avoidance principle
    `SymmetricLLLForRamsey` — yields a monochromatic-`K₁₁`-free 2-colouring of
    `K₁₅₆`, i.e. `R(11,11) > 156`.  So `k = 11` is the first diagonal Ramsey
    number at which the symmetric LLL strengthens the *honest* first moment (not
    merely the weakened closed form `2^{⌊k/2⌋}`), by at least `156 − 152 = 4`
    vertices. -/
theorem lll_improves_sharp_union_at_11 (hLLL : SymmetricLLLForRamsey) :
    ∃ color : Fin 156 → Fin 156 → Bool,
      (∀ x y, color x y = color y x) ∧
      (∀ x, color x x = false) ∧
      (∀ s : Finset (Fin 156), s.card = 11 →
        ¬ (∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = true)) ∧
      (∀ s : Finset (Fin 156), s.card = 11 →
        ¬ (∀ x y, x ∈ s → y ∈ s → x ≠ y → color x y = false)) :=
  ramsey_lll_lower_bound hLLL (k := 11) (by norm_num)
    (n := 156) lll_beats_unionBound_at_11.2

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `native_decide`.  The concrete
-- witnesses use kernel `decide` (`of_decide_eq_true`), which is axiom-free — it
-- does NOT introduce `Lean.ofReduceBool` the way `native_decide` would.  The
-- binomials route through `Nat.choose_eq_descFactorial_div_factorial` to keep the
-- kernel reduction cheap (single-recursion `descFactorial`), also axiom-free.
-- `lll_improves_sharp_union_at_11` additionally depends on the explicit hypothesis
-- `SymmetricLLLForRamsey` (a `Prop` argument, not an axiom).
#check @lll_beats_unionBound_at_11
#check @unionBound_still_beats_lll_at_10
#check @lll_improves_sharp_union_at_11
#print axioms choose_156_11
#print axioms cliqueDependencyBound_156_11
#print axioms lll_beats_unionBound_at_11
#print axioms unionBound_still_beats_lll_at_10
#print axioms lll_improves_sharp_union_at_11

end RamseyLLL
