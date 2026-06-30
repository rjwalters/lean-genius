/-
Erdős Problem #305 — companion: the Egyptian-representation existence axiom is a theorem.

The gallery entry `Erdos305Problem.lean` (Erdős #305, "Maximum Denominator in
Egyptian Fraction Representations") states the *existence* of an Egyptian
fraction representation for every proper fraction a/b as an `axiom`:

    axiom egyptian_representation_exists (a b : ℕ) (hab : 0 < a) (hlt : a < b) :
      ∃ S : Finset ℕ, isEgyptianRepresentation S a b

But this existence statement is itself a classical theorem — the
Fibonacci–Sylvester greedy algorithm — and needs no axiom. This file discharges
it: `egyptian_representation_exists` is proved from scratch, eliminating one
assumption from the Erdős #305 development.

The remaining `sorry` in `Erdos305Problem.lean` (`erdos_305_solved`) is the deep
asymptotic bound D(b) ≪ b(log b)^{1+o(1)} of Yokota (1988) / Liu–Sawhney (2024)
and is genuinely out of reach; this file does NOT touch it. It addresses only
the elementary existence axiom.

Method (greedy / Fibonacci–Sylvester). For 0 < a < b put n = ⌈b/a⌉ =
(b+a-1)/a. Then a*n - b < a, so subtracting the unit fraction 1/n strictly
decreases the numerator; recurse. A short interval estimate shows the next
denominator strictly exceeds n, which guarantees the denominators are distinct
(automatic, since they form a `Finset`) — and indeed strictly increasing. The
representation is built by strong induction on the numerator a.

Note `isEgyptianFraction S := ∀ n ∈ S, n ≥ 1` requires only positivity of the
denominators; distinctness is built into `Finset`.

Fully machine-checked: 0 sorries, 0 axioms (only foundational propext,
Classical.choice, Quot.sound).
-/

import Mathlib

open Finset

namespace Erdos305EgyptianExists

/-- A finite set of denominators is a (positive) Egyptian-fraction support: every
denominator is at least `1`. Distinctness is automatic for a `Finset`. -/
def isEgyptianFraction (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, n ≥ 1

/-- The sum `∑_{n ∈ S} 1/n` of unit fractions, as a rational. The guard
`if n = 0` keeps the definition total; on Egyptian supports it is never taken. -/
noncomputable def unitFractionSum (S : Finset ℕ) : ℚ :=
  S.sum fun n => if n = 0 then 0 else 1 / n

/-- `S` represents `a/b` as an Egyptian fraction: `a < b`, `b > 0`, every
denominator is positive, and the unit fractions sum to `a/b`. -/
def isEgyptianRepresentation (S : Finset ℕ) (a b : ℕ) : Prop :=
  a < b ∧ b > 0 ∧ isEgyptianFraction S ∧ unitFractionSum S = a / b

/-- **Greedy existence, strengthened.** For `0 < a < b` there is a finite set of
denominators, each at least the greedy choice `⌈b/a⌉ = (b+a-1)/a`, whose unit
fractions sum to `a/b`. The lower bound on denominators is the induction
strengthening that forces the freshly inserted denominator to be new. -/
theorem exists_egyptian_aux :
    ∀ a : ℕ, 0 < a → ∀ b : ℕ, a < b →
      ∃ S : Finset ℕ, (∀ m ∈ S, (b + a - 1) / a ≤ m) ∧
        unitFractionSum S = (a : ℚ) / (b : ℚ) := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a IH =>
    intro ha b hab
    set n := (b + a - 1) / a with hn
    -- Ceiling estimates: `b ≤ a*n ≤ b + a - 1`.
    have hdm := Nat.div_add_mod (b + a - 1) a
    have hmod : (b + a - 1) % a < a := Nat.mod_lt _ ha
    rw [← hn] at hdm
    -- `hdm : a * n + (b + a - 1) % a = b + a - 1`
    have hub : a * n ≤ b + a - 1 := by omega
    have hlb : b ≤ a * n := by omega
    have hn_pos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · rw [h, Nat.mul_zero] at hlb; omega
      · exact h
    have han : a * n < b + a := by omega
    set a' := a * n - b with ha'
    by_cases hcase : a' = 0
    · -- `a*n = b`, so `a/b = 1/n`.
      have hbeq : b = a * n := by omega
      refine ⟨{n}, ?_, ?_⟩
      · intro m hm
        rw [Finset.mem_singleton] at hm
        omega
      · rw [unitFractionSum, Finset.sum_singleton, if_neg (by omega)]
        have hnQ : (n : ℚ) ≠ 0 := by positivity
        have haQ : (a : ℚ) ≠ 0 := by positivity
        rw [hbeq, Nat.cast_mul]
        field_simp
    · -- `0 < a' < a`: recurse on `a'/(b*n)`.
      have ha'pos : 0 < a' := Nat.pos_of_ne_zero hcase
      have ha'lt : a' < a := by omega
      have ha'ltb : a' < b := lt_trans ha'lt hab
      have hb' : a' < b * n := by
        calc a' < a := ha'lt
          _ < b := hab
          _ ≤ b * n := Nat.le_mul_of_pos_right b hn_pos
      obtain ⟨S', hS'lb, hS'sum⟩ := IH a' ha'lt ha'pos (b * n) hb'
      -- Every denominator of `S'` strictly exceeds `n`, so `n ∉ S'`.
      have hgt : ∀ m ∈ S', n < m := by
        intro m hm
        have hmlb := hS'lb m hm
        set q := (b * n + a' - 1) / a' with hq
        have hqdm := Nat.div_add_mod (b * n + a' - 1) a'
        have hqmod : (b * n + a' - 1) % a' < a' := Nat.mod_lt _ ha'pos
        rw [← hq] at hqdm
        -- `a' * q ≥ b * n`
        have hqge : b * n ≤ a' * q := by omega
        -- `a' * n < b * n` since `a' < b` and `0 < n`
        have hcmp : a' * n < b * n := (Nat.mul_lt_mul_right hn_pos).mpr ha'ltb
        have : a' * n < a' * q := lt_of_lt_of_le hcmp hqge
        have hnq : n < q := Nat.lt_of_mul_lt_mul_left this
        omega
      have hnotin : n ∉ S' := fun hin => lt_irrefl n (hgt n hin)
      refine ⟨insert n S', ?_, ?_⟩
      · intro m hm
        rcases Finset.mem_insert.mp hm with h | h
        · omega
        · have := hgt m h; omega
      · rw [unitFractionSum, Finset.sum_insert hnotin, if_neg (by omega)]
        have hsum' : unitFractionSum S' = (a' : ℚ) / (b * n : ℕ) := hS'sum
        rw [unitFractionSum] at hsum'
        rw [hsum']
        have hnQ : (n : ℚ) ≠ 0 := by positivity
        have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have ha'castQ : (a' : ℚ) = (a : ℚ) * n - b := by
          rw [ha', Nat.cast_sub hlb, Nat.cast_mul]
        rw [ha'castQ, Nat.cast_mul]
        field_simp
        ring

/-- **Existence of Egyptian fraction representations** (the former `axiom` of
`Erdos305Problem.lean`, now a theorem). Every proper fraction `a/b` with
`0 < a < b` has a finite Egyptian-fraction representation. -/
theorem egyptian_representation_exists (a b : ℕ) (hab : 0 < a) (hlt : a < b) :
    ∃ S : Finset ℕ, isEgyptianRepresentation S a b := by
  obtain ⟨S, hSlb, hSsum⟩ := exists_egyptian_aux a hab b hlt
  refine ⟨S, hlt, by omega, ?_, hSsum⟩
  -- positivity of every denominator: each is at least `(b+a-1)/a ≥ 1`
  have hge1 : 1 ≤ (b + a - 1) / a := by
    rw [Nat.le_div_iff_mul_le hab, one_mul]
    omega
  intro m hm
  have := hSlb m hm
  omega

end Erdos305EgyptianExists
