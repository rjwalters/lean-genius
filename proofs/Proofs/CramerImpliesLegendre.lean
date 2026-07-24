/-
# Cramér's Conjecture Implies Legendre's Conjecture Up To Finitely Many Cases

Legendre's conjecture (1798, open): for every `n ≥ 1` there is a prime in
`(n², (n+1)²)`. Cramér's conjecture (1936, open): consecutive prime gaps
satisfy `p_{k+1} - p_k = O((log p_k)²)`.

This file formalizes the classical implication chain (S5-ACT-A/B/C of the
`bertrands-postulate-oq-02` research thread):

  Cramér's conjecture
    ⟹ [ACT-A: analytic estimate `C·(log x)² ≤ √x − 1` eventually]
  the sqrt prime-gap bound `p_{k+1} - p_k ≤ 2·√p_k + 1` for all primes `p_k ≥ M`
    ⟹ [ACT-C: `legendreAt_of_sqrt_gap_above` from
       `LegendrePrimeGapSqrtBoundSuffices.lean`]
  `LegendreAt n` for all sufficiently large `n`.

## Main results

* `CramerConjecture` — the upper-bound form of Cramér's conjecture, as a
  `Prop`: some `C > 0` bounds all sufficiently late prime gaps by
  `C·(log p_k)²`. Stated, never assumed.
* `eventually_mul_log_sq_le_sqrt_sub_one` — ACT-A: for every real `C`,
  eventually `C·(log x)² ≤ √x − 1` (from Mathlib's `(log x)^r = o(x^s)`).
* `cramerGapBound_to_sqrt_gap` — ACT-B: a Cramér gap bound yields a threshold
  `M` beyond which the sqrt gap bound `p_{k+1} - p_k ≤ 2·Nat.sqrt p_k + 1`
  holds.
* `cramer_implies_legendre_eventually` — ACT-C: under `CramerConjecture`
  there is an `N` with `LegendreAt n` for all `n ≥ N`.
* `cramer_exceptions_finite` — equivalently, the exception set
  `{n | 1 ≤ n ∧ ¬LegendreAt n}` is finite.
* `cramer_reduces_legendre_to_finite` — the full conditional composition:
  under Cramér, Legendre's conjecture reduces to finitely many explicit cases
  (`∃ N`, checking `n < N` suffices).

## Why "eventually", not Legendre outright

Cramér's conjecture is an *asymptotic* statement (`∃ C, ∃ k₀, ∀ k ≥ k₀, …`).
The constants `C, k₀` are existentially quantified, so no fixed finite
verification (such as `LegendrePartial.lean`'s `n = 1..20`) can discharge the
small-`n` tail *uniformly in the witness*: for each concrete `(C, k₀)` the
tail is finite and checkable, but the statement `CramerConjecture` alone pins
no bound on it. `cramer_reduces_legendre_to_finite` is the honest strongest
form: Cramér reduces Legendre to a finite (existentially bounded) check.
For the numerically expected constants the tail is tiny — for `C = 1` the
analytic crossover is at `p ≈ 121`, covered by `LegendrePartial.lean`'s
verified range (see the iter-6 audit memo in
`research/problems/bertrands-postulate-oq-02/`).

## Axioms

This file introduces **0 new axioms** and **0 sorries**. `CramerConjecture`
is a defined `Prop` appearing only as an explicit hypothesis.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
import Proofs.LegendrePrimeGapSqrtBoundSuffices

namespace CramerImpliesLegendre

open Legendre LegendrePrimeGapSqrtBoundSuffices Filter

/-! ## Cramér's conjecture as a hypothesis -/

/-- Cramér-type prime-gap bound with constant `C` from index `k₀` on:
`p_{k+1} - p_k ≤ C·(log p_k)²` for all `k ≥ k₀`
(where `p_k := Nat.nth Nat.Prime k`). -/
def CramerGapBound (C : ℝ) (k₀ : ℕ) : Prop :=
  ∀ k, k₀ ≤ k →
    ((Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k : ℕ) : ℝ)
      ≤ C * Real.log (Nat.nth Nat.Prime k) ^ 2

/-- **Cramér's conjecture** (upper-bound form, 1936): some constant `C > 0`
bounds all sufficiently late consecutive prime gaps by `C·(log p_k)²`.
OPEN — stated as a `Prop`, never assumed. -/
def CramerConjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, CramerGapBound C k₀

/-! ## S5-ACT-A: the analytic estimate -/

/-- For any real constant `C`, eventually (as `x → ∞`)
`C · (log x)² ≤ √x − 1`. The content is Mathlib's
`Real.isLittleO_log_rpow_rpow_atTop`: `(log x)² = o(x^{1/2})`. -/
theorem eventually_mul_log_sq_le_sqrt_sub_one (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, C * Real.log x ^ 2 ≤ Real.sqrt x - 1 := by
  set D : ℝ := max C 1 with hD_def
  have hD1 : (1 : ℝ) ≤ D := le_max_right _ _
  have hCD : C ≤ D := le_max_left _ _
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  -- `(log x)^2 = o(x^{1/2})` (rpow exponents)
  have hlo : (fun x : ℝ => Real.log x ^ (2 : ℝ)) =o[atTop]
      fun x : ℝ => x ^ ((1 : ℝ) / 2) :=
    isLittleO_log_rpow_rpow_atTop 2 (by norm_num)
  have hbound := hlo.def (show (0 : ℝ) < 1 / (2 * D) by positivity)
  filter_upwards [hbound, eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (4 : ℝ)] with x hx hx1 hx4
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  -- rewrite the rpow forms as `(log x)^2` (monoid power) and `√x`
  have hrw_log : Real.log x ^ (2 : ℝ) = Real.log x ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hrw_sqrt : x ^ ((1 : ℝ) / 2) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  rw [hrw_log, hrw_sqrt, Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (Real.sqrt_nonneg x)] at hx
  -- `√x ≥ 2` for `x ≥ 4`
  have hsqrt2 : (2 : ℝ) ≤ Real.sqrt x := by
    have : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt hx4
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      at this
  -- chain: C·log²x ≤ D·log²x ≤ √x/2 ≤ √x − 1
  have h1 : C * Real.log x ^ 2 ≤ D * Real.log x ^ 2 := by
    have := sq_nonneg (Real.log x)
    nlinarith
  have h2 : D * Real.log x ^ 2 ≤ Real.sqrt x / 2 := by
    have := mul_le_mul_of_nonneg_left hx (le_of_lt hD0)
    calc D * Real.log x ^ 2 ≤ D * (1 / (2 * D) * Real.sqrt x) := this
      _ = Real.sqrt x / 2 := by field_simp
  linarith

/-- Nat-side threshold: for any `C` there is `M` such that every natural
`p ≥ M` satisfies `C·(log p)² ≤ 2·Nat.sqrt p + 1` (in `ℝ`). Uses
`√p < Nat.sqrt p + 1`. -/
theorem exists_nat_sqrt_threshold (C : ℝ) :
    ∃ M : ℕ, ∀ p : ℕ, M ≤ p →
      C * Real.log p ^ 2 ≤ 2 * (Nat.sqrt p : ℝ) + 1 := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp (eventually_mul_log_sq_le_sqrt_sub_one C)
  refine ⟨⌈a⌉₊, fun p hp => ?_⟩
  have hpa : a ≤ (p : ℝ) := le_trans (Nat.le_ceil a) (by exact_mod_cast hp)
  have h1 := ha (p : ℝ) hpa
  -- `√p < Nat.sqrt p + 1` since `p < (Nat.sqrt p + 1)²`
  have hs : Real.sqrt p < (Nat.sqrt p : ℝ) + 1 := by
    rw [Real.sqrt_lt' (by positivity)]
    have hnat : p < (Nat.sqrt p + 1) ^ 2 := by
      have := Nat.lt_succ_sqrt' p
      nlinarith
    calc (p : ℝ) < (((Nat.sqrt p + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((Nat.sqrt p : ℝ) + 1) ^ 2 := by push_cast; ring
  have hnn : (0 : ℝ) ≤ (Nat.sqrt p : ℝ) := Nat.cast_nonneg _
  linarith

/-! ## S5-ACT-B: Cramér gap bound ⇒ eventual sqrt gap bound -/

/-- A Cramér-type gap bound yields a threshold `M` beyond which the
(Nat-valued) sqrt prime-gap bound holds: for every `k` with `p_k ≥ M`,
`p_{k+1} - p_k ≤ 2·Nat.sqrt p_k + 1`. -/
theorem cramerGapBound_to_sqrt_gap {C : ℝ} {k₀ : ℕ} (h : CramerGapBound C k₀) :
    ∃ M : ℕ, ∀ k, M ≤ Nat.nth Nat.Prime k →
      Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k
        ≤ 2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1 := by
  obtain ⟨M₀, hM₀⟩ := exists_nat_sqrt_threshold C
  refine ⟨max M₀ (Nat.nth Nat.Prime k₀), fun k hk => ?_⟩
  -- `p_k ≥ p_{k₀}` forces `k ≥ k₀` (strict monotonicity of `Nat.nth`)
  have hk₀ : k₀ ≤ k := by
    rcases lt_or_ge k k₀ with hlt | h
    · exfalso
      have hmono : Nat.nth Nat.Prime k < Nat.nth Nat.Prime k₀ :=
        Nat.nth_strictMono Nat.infinite_setOf_prime hlt
      have hmax := le_max_right M₀ (Nat.nth Nat.Prime k₀)
      omega
    · exact h
  have hgap := h k hk₀
  have hthr := hM₀ (Nat.nth Nat.Prime k) (le_trans (le_max_left _ _) hk)
  have hcast : ((Nat.nth Nat.Prime (k + 1) - Nat.nth Nat.Prime k : ℕ) : ℝ)
      ≤ ((2 * Nat.sqrt (Nat.nth Nat.Prime k) + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hcast

/-! ## S5-ACT-C: composition — Cramér ⇒ Legendre eventually -/

/-- **Cramér's conjecture implies Legendre's conjecture for all sufficiently
large `n`**: under `CramerConjecture` there is an `N` such that for every
`n ≥ N` there is a prime in `(n², (n+1)²)`. Unconditional in the small-`n`
regime — no hypothesis about small cases is needed. -/
theorem cramer_implies_legendre_eventually (h : CramerConjecture) :
    ∃ N : ℕ, ∀ n, N ≤ n → LegendreAt n := by
  obtain ⟨C, _hC, k₀, hgap⟩ := h
  obtain ⟨M, hM⟩ := cramerGapBound_to_sqrt_gap hgap
  refine ⟨2 * M + 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hself : n ≤ n ^ 2 := by nlinarith
  exact legendreAt_of_sqrt_gap_above M hM hn2 (by omega)

/-- Under Cramér's conjecture, the set of exceptions to Legendre's conjecture
is finite. -/
theorem cramer_exceptions_finite (h : CramerConjecture) :
    {n : ℕ | 1 ≤ n ∧ ¬ LegendreAt n}.Finite := by
  obtain ⟨N, hN⟩ := cramer_implies_legendre_eventually h
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  rintro n ⟨-, hnot⟩
  rw [Set.mem_Iio]
  rcases lt_or_ge n N with h | hge
  · exact h
  · exact absurd (hN n hge) hnot

/-- **Full conditional composition**: under Cramér's conjecture, Legendre's
conjecture reduces to finitely many explicit cases — there is a single `N`
such that verifying `LegendreAt n` for the finitely many `1 ≤ n < N` yields
the full conjecture. -/
theorem cramer_reduces_legendre_to_finite (h : CramerConjecture) :
    ∃ N : ℕ, (∀ n, 1 ≤ n → n < N → LegendreAt n) → LegendreConjecture := by
  obtain ⟨N, hN⟩ := cramer_implies_legendre_eventually h
  exact ⟨N, fun hsmall n hn =>
    (lt_or_ge n N).elim (hsmall n hn) (fun hge => hN n hge)⟩

/-! ## Summary

Proved, all axiom-free and sorry-free:

1. `CramerConjecture` — Cramér's 1936 conjecture as a defined `Prop`
   (upper-bound form `∃ C > 0, ∃ k₀, ∀ k ≥ k₀, p_{k+1} − p_k ≤ C·(log p_k)²`).
2. `eventually_mul_log_sq_le_sqrt_sub_one` — `C·(log x)² ≤ √x − 1`
   eventually (S5-ACT-A).
3. `cramerGapBound_to_sqrt_gap` — Cramér bound ⇒ sqrt gap bound above a
   threshold (S5-ACT-B).
4. `cramer_implies_legendre_eventually` / `cramer_exceptions_finite` /
   `cramer_reduces_legendre_to_finite` — Cramér ⇒ Legendre up to finitely
   many explicit cases (S5-ACT-C).

### What this does NOT prove

Neither conjecture. Both remain open; Cramér appears only as an explicit
hypothesis. The reduction is one-directional: Legendre is *weaker* than
Cramér in the eventual regime, and nothing here bounds the exceptional `N`
without a concrete Cramér witness `(C, k₀)`.
-/

end CramerImpliesLegendre
