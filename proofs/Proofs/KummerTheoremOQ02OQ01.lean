/-
Kummer's Theorem OQ-02-OQ-01: q-Kummer for q-Multinomial Coefficients

The parent entry `KummerTheoremOQ02` ("q-Kummer Theorem: Cyclotomic
Factorization of q-Binomials") establishes the q-analog of Kummer's theorem for
q-*binomial* coefficients:

  [n choose k]_q = ∏_{d ≥ 2} Φ_d(q) ^ (⌊n/d⌋ - ⌊k/d⌋ - ⌊(n-k)/d⌋).

This file answers the parent's first listed open question — *"Can the q-Kummer
theorem be extended to q-multinomial coefficients?"* — in the affirmative, by
lifting the result from two parts to an arbitrary number of parts:

  [k₁ + ⋯ + kᵣ ; k₁, …, kᵣ]_q = [n]_q! / ([k₁]_q! ⋯ [kᵣ]_q!).

The mechanism is the one the question hints at: the q-multinomial telescopes
into a chain of q-binomials,

  [k₁+⋯+kᵣ ; k₁,…,kᵣ]_q = [k₁+⋯+kᵣ choose k₁]_q · [k₂+⋯+kᵣ ; k₂,…,kᵣ]_q,

so applying the parent's q-Kummer factorization to each q-binomial factor and
multiplying gives the multinomial cyclotomic factorization, with exponent

  multiDeficiency(k₁,…,kᵣ ; d) = ⌊(Σ kᵢ)/d⌋ - Σ ⌊kᵢ/d⌋

(the total number of carries when adding k₁, …, kᵣ in base d).

## Axioms (the parent's q-binomial interface)

The three facts this extension consumes from the parent are stated here as
`axiom`s rather than imported, because the parent source file
`KummerTheoremOQ02.lean` uses the pre-`∈` big-operator notation and several
since-renamed `Nat`/`Finset` lemmas, so it no longer compiles under the current
Mathlib (v4.26.0) toolchain (a repository-wide bit-rot affecting the legacy
`∑ … in` files; out of scope for this entry).  The axioms are exactly the
parent's `theorem`s `qBinomial_factorial`, `qKummer`, and `qFactorial_eval_one`,
which are mathematically established there:

* `qBinomial_factorial`  — the quotient formula `[n choose k]_q · [k]_q! · [n-k]_q! = [n]_q!`.
* `qKummer`              — the two-part q-Kummer cyclotomic factorization.
* `qFactorial_eval_one`  — `[n]_q!` evaluated at `q = 1` equals `n!`.

Everything in `Part XI` (the q-multinomial results) is proved from these with
**no `sorry`s**; the only assumptions are the three axioms above.

## New results (Part XI)
* `qMultinomial`            — the q-multinomial as a chain of q-binomials.
* `qMultinomial_factorial`  — quotient form `qMultinomial · ∏[kᵢ]_q! = [Σkᵢ]_q!`.
* `qMultinomial_cyclotomic` — **the q-Kummer theorem for q-multinomials**.
* `qMultinomial_eval_one`   — at `q = 1`, recovers `multinomial · ∏ kᵢ! = (Σkᵢ)!`.
-/

import Mathlib

namespace KummerTheoremOQ02OQ01

open Polynomial Finset Nat

-- ══════════════════════════════════════════════════════════════════
-- § Definitions (q-number, q-factorial, q-binomial, floor deficiency)
-- ══════════════════════════════════════════════════════════════════

/-- The q-number `[n]_q = 1 + q + q² + ⋯ + q^(n-1)` as a polynomial in `ℤ[X]`. -/
noncomputable def qNumber (n : ℕ) : ℤ[X] :=
  ∑ i ∈ Finset.range n, X ^ i

/-- The q-factorial `[n]_q! = [1]_q · [2]_q · ⋯ · [n]_q`. -/
noncomputable def qFactorial : ℕ → ℤ[X]
  | 0 => 1
  | n + 1 => qFactorial n * qNumber (n + 1)

/-- The q-binomial (Gaussian binomial) coefficient, via the q-Pascal recurrence. -/
noncomputable def qBinomial : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => qBinomial n k + X ^ (k + 1) * qBinomial n (k + 1)

/-- The two-part floor deficiency `⌊n/d⌋ - ⌊k/d⌋ - ⌊(n-k)/d⌋` (carry count for the
q-binomial). -/
def floorDeficiency (n k d : ℕ) : ℕ := n / d - k / d - (n - k) / d

-- ══════════════════════════════════════════════════════════════════
-- § Parent interface (axiomatized — see header)
-- ══════════════════════════════════════════════════════════════════

/-- Quotient formula (parent `KummerTheoremOQ02.qBinomial_factorial`):
`[n choose k]_q · [k]_q! · [n-k]_q! = [n]_q!`. -/
axiom qBinomial_factorial (n k : ℕ) (hkn : k ≤ n) :
    qBinomial n k * qFactorial k * qFactorial (n - k) = qFactorial n

/-- The two-part q-Kummer cyclotomic factorization (parent `KummerTheoremOQ02.qKummer`):
`[n choose k]_q = ∏_{d=2}^{n} Φ_d ^ floorDeficiency(n,k,d)`. -/
axiom qKummer (n k : ℕ) (hkn : k ≤ n) :
    qBinomial n k = ∏ d ∈ Icc 2 n, (cyclotomic d ℤ) ^ floorDeficiency n k d

/-- Evaluation of the q-factorial at `q = 1` (parent `KummerTheoremOQ02.qFactorial_eval_one`):
`[n]_q!|_{q=1} = n!`. -/
axiom qFactorial_eval_one (n : ℕ) : (qFactorial n).eval 1 = (n ! : ℤ)

-- ══════════════════════════════════════════════════════════════════
-- § Floor-division arithmetic (self-contained)
-- ══════════════════════════════════════════════════════════════════

/-- Subadditivity of floor division: `⌊a/d⌋ + ⌊b/d⌋ ≤ ⌊(a+b)/d⌋`. -/
private lemma div_add_div_le (a b d : ℕ) (hd : 0 < d) : a / d + b / d ≤ (a + b) / d := by
  rw [Nat.le_div_iff_mul_le hd]
  calc (a / d + b / d) * d = a / d * d + b / d * d := by ring
    _ ≤ a + b := Nat.add_le_add (Nat.div_mul_le_self a d) (Nat.div_mul_le_self b d)

/-- The sum of the parts' floor-divisions is at most the floor-division of the
total: `Σ ⌊kᵢ/d⌋ ≤ ⌊(Σ kᵢ)/d⌋` (iterated subadditivity). -/
private lemma sum_div_le : ∀ (ks : List ℕ) (d : ℕ), 0 < d →
    (ks.map (· / d)).sum ≤ ks.sum / d
  | [], _, _ => by simp
  | k :: ks, d, hd => by
    have ih := sum_div_le ks d hd
    simp only [List.map_cons, List.sum_cons]
    calc k / d + (ks.map (· / d)).sum
          ≤ k / d + ks.sum / d := Nat.add_le_add_left ih _
      _ ≤ (k + ks.sum) / d := div_add_div_le k ks.sum d hd

-- ══════════════════════════════════════════════════════════════════
-- § Part XI: q-Multinomial Coefficients  (NEW — OQ-02-OQ-01)
-- ══════════════════════════════════════════════════════════════════

/-- The **q-multinomial coefficient** of a list of parts `[k₁, …, kᵣ]`, defined by
the telescoping chain of q-binomials

  `[k₁+⋯+kᵣ ; k₁,…,kᵣ]_q = [k₁+⋯+kᵣ choose k₁]_q · [k₂+⋯+kᵣ ; k₂,…,kᵣ]_q`,

so the empty list gives `1`.  This is a polynomial in `q` with integer coefficients. -/
noncomputable def qMultinomial : List ℕ → ℤ[X]
  | [] => 1
  | k :: ks => qBinomial (k + ks.sum) k * qMultinomial ks

/-- The **multinomial floor deficiency** at `d`:
`multiDeficiency(k₁,…,kᵣ ; d) = ⌊(Σ kᵢ)/d⌋ - Σ ⌊kᵢ/d⌋`, the total number of
carries when adding `k₁, …, kᵣ` in base `d`. -/
def multiDeficiency (ks : List ℕ) (d : ℕ) : ℕ :=
  ks.sum / d - (ks.map (· / d)).sum

/-- The deficiency obeys the chain recursion mirroring the q-multinomial:
`multiDeficiency(k::ks ; d) = floorDeficiency(k+Σks, k, d) + multiDeficiency(ks ; d)`,
where `floorDeficiency` is the parent's two-part (q-binomial) carry count. -/
theorem multiDeficiency_cons (k : ℕ) (ks : List ℕ) (d : ℕ) (hd : 0 < d) :
    multiDeficiency (k :: ks) d
      = floorDeficiency (k + ks.sum) k d + multiDeficiency ks d := by
  have hbc := div_add_div_le k ks.sum d hd
  have htc := sum_div_le ks d hd
  simp only [multiDeficiency, floorDeficiency, List.map_cons, List.sum_cons,
    Nat.add_sub_cancel_left]
  omega

/-- The q-analog of `multinomial · k₁! ⋯ kᵣ! = (Σ kᵢ)!`:
`qMultinomial ks · ∏ᵢ [kᵢ]_q! = [Σ kᵢ]_q!`.  This shows the chain definition is
the genuine q-multinomial (the quotient `[n]_q! / ∏ [kᵢ]_q!` performed honestly
inside `ℤ[X]`). -/
theorem qMultinomial_factorial : ∀ ks : List ℕ,
    qMultinomial ks * (ks.map qFactorial).prod = qFactorial ks.sum
  | [] => by simp [qMultinomial, qFactorial]
  | k :: ks => by
    have ih := qMultinomial_factorial ks
    have hbf := qBinomial_factorial (k + ks.sum) k (Nat.le_add_right k ks.sum)
    simp only [Nat.add_sub_cancel_left] at hbf
    rw [show qMultinomial (k :: ks)
          = qBinomial (k + ks.sum) k * qMultinomial ks from rfl,
        List.map_cons, List.prod_cons, List.sum_cons]
    linear_combination (qBinomial (k + ks.sum) k * qFactorial k) * ih + hbf

/-- **The q-Kummer Theorem for q-multinomial coefficients.**

  `qMultinomial ks = ∏_{d=2}^{Σ kᵢ} Φ_d(q) ^ multiDeficiency(ks ; d)`.

Each factor's exponent counts carries in base `d` when adding the parts; this
generalizes the parent's two-part q-Kummer theorem to arbitrarily many parts.
The proof is induction along the q-binomial chain: apply the parent `qKummer`
to the head q-binomial, fold in the inductive factorization of the tail, and
merge exponents via `multiDeficiency_cons`. -/
theorem qMultinomial_cyclotomic : ∀ ks : List ℕ,
    qMultinomial ks
      = ∏ d ∈ Icc 2 ks.sum, (cyclotomic d ℤ) ^ multiDeficiency ks d
  | [] => by
    simp only [List.sum_nil, qMultinomial]
    rw [Finset.Icc_eq_empty (by decide : ¬ (2 : ℕ) ≤ 0)]
    simp
  | k :: ks => by
    have ih := qMultinomial_cyclotomic ks
    have hbin := qKummer (k + ks.sum) k (Nat.le_add_right k ks.sum)
    -- Extend the tail's factorization from `Icc 2 (Σks)` up to `Icc 2 (k+Σks)`:
    -- the new factors carry exponent 0 since their `d` exceeds `Σks`.
    have ih' : (∏ d ∈ Icc 2 ks.sum, (cyclotomic d ℤ) ^ multiDeficiency ks d)
        = ∏ d ∈ Icc 2 (k + ks.sum), (cyclotomic d ℤ) ^ multiDeficiency ks d := by
      apply Finset.prod_subset (Finset.Icc_subset_Icc_right (Nat.le_add_left ks.sum k))
      intro d hd hdS
      simp only [Finset.mem_Icc] at hd hdS
      have hdgt : ks.sum < d := by omega
      have hz : multiDeficiency ks d = 0 := by
        simp [multiDeficiency, Nat.div_eq_of_lt hdgt]
      rw [hz, pow_zero]
    rw [show qMultinomial (k :: ks)
          = qBinomial (k + ks.sum) k * qMultinomial ks from rfl,
        List.sum_cons, hbin, ih, ih', ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro d hd
    simp only [Finset.mem_Icc] at hd
    rw [← pow_add, multiDeficiency_cons k ks d (by omega)]

/-- Evaluating a chain of q-factorials at `q = 1` gives the chain of ordinary
factorials. -/
private theorem eval_one_prod_qFactorial : ∀ l : List ℕ,
    (Polynomial.eval (1 : ℤ)) (l.map qFactorial).prod
      = (l.map (fun k => (k ! : ℤ))).prod
  | [] => by simp
  | a :: as => by
    simp [List.map_cons, List.prod_cons, Polynomial.eval_mul, qFactorial_eval_one,
      eval_one_prod_qFactorial as]

/-- **Specialization at `q = 1`.**  The q-multinomial evaluated at `q = 1` is the
ordinary multinomial coefficient, witnessed by

  `(qMultinomial ks)(1) · ∏ᵢ kᵢ! = (Σ kᵢ)!`.

Together with `qMultinomial_cyclotomic`, this exhibits `[n]_q! / ∏ [kᵢ]_q!` as a
genuine polynomial recovering `(Σ kᵢ)! / ∏ kᵢ!` at `q = 1`. -/
theorem qMultinomial_eval_one (ks : List ℕ) :
    (qMultinomial ks).eval 1 * (ks.map (fun k => (k ! : ℤ))).prod
      = ((ks.sum)! : ℤ) := by
  have h := congrArg (Polynomial.eval (1 : ℤ)) (qMultinomial_factorial ks)
  rw [Polynomial.eval_mul, qFactorial_eval_one, eval_one_prod_qFactorial ks] at h
  exact h

#check @qMultinomial
#check @qMultinomial_factorial
#check @qMultinomial_cyclotomic
#check @qMultinomial_eval_one

end KummerTheoremOQ02OQ01
