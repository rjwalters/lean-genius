/-
  Sufficiency reduction for Legendre's three-square theorem.

  `Proofs.ThreeSquares` formalizes Legendre's three-square theorem but leaves the
  SUFFICIENCY direction as an axiom:

      axiom not_excluded_form_is_sum_three_sq {n : ℕ} (h : ¬IsExcludedForm n) :
          ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n        (ThreeSquares.lean:1665)

  This file SHRINKS that axiom. It proves the full sufficiency statement from a
  single, sharply isolated number-theoretic ingredient — the existence of a
  Dirichlet witness `(d, p)` for each non-excluded `n` not divisible by `4`:

      Hwit : ¬IsExcludedForm m → ¬(4 ∣ m) → 1 < m →
             ∃ d p : ℕ, 0 < d ∧ p = d * m - 1 ∧ p.Prime ∧ legendreSym p (-d : ℤ) = 1

  Everything ELSE in the sufficiency proof — the `4`-power descent, the small
  cases, and the assembly via `dirichlet_key_lemma` — is discharged here with no
  new axioms and no `sorry`, reusing only lemmas already proved in
  `Proofs.ThreeSquares`:

    * `excluded_form_four_mul_iff`  — `IsExcludedForm (4 * n) ↔ IsExcludedForm n`
    * `four_mul_sum_three_sq`       — `(∃ … = n) → (∃ … = 4 * n)`
    * `dirichlet_key_lemma`         — Dirichlet's 1850 representation lemma (axiom)

  CONSEQUENCE FOR THE AXIOM BUDGET.  `not_excluded_form_is_sum_three_sq` is *not*
  an independent assumption: it follows from `dirichlet_key_lemma` together with
  `Hwit`.  The witness property `Hwit` is the genuine remaining open content; it
  is exactly Dirichlet's theorem on primes in arithmetic progressions (available
  in Mathlib as `Nat.infinite_setOf_prime_and_eq_mod`) combined with a quadratic
  reciprocity computation choosing the residue class so that `-d` is a quadratic
  residue mod `p`.  Discharging `Hwit` would eliminate the sufficiency axiom from
  `ThreeSquares.lean` entirely, turning two axioms into one.

  STATUS: reduction is unconditional given `Hwit`; the `Hwit` hypothesis is the
  only open piece and is stated, not assumed as a global axiom.
-/
import Proofs.ThreeSquares

namespace ThreeSquares

/-- The Dirichlet witness property: for every `n > 1` that is not of excluded
form and is not divisible by `4`, there is a multiplier `d` and a prime
`p = d * n - 1` with `-d` a quadratic residue mod `p`.

This is precisely the input needed by `dirichlet_key_lemma`. It is the classical
Dirichlet-1850 selection step (Dirichlet's theorem on primes in AP + quadratic
reciprocity) and is the sole open ingredient of the sufficiency direction. -/
def DirichletWitnessProperty : Prop :=
  ∀ {m : ℕ}, ¬IsExcludedForm m → ¬(4 ∣ m) → 1 < m →
    ∃ d p : ℕ, 0 < d ∧ p = d * m - 1 ∧ Nat.Prime p ∧ legendreSym p (-d : ℤ) = 1

/-- **Sufficiency from the Dirichlet witness.**

Assuming the Dirichlet witness property, every natural number that is not of the
excluded form `4^a (8b + 7)` is a sum of three integer squares.

The proof is strong induction on `n`, mirroring the descent in the proven
necessity theorem `excluded_form_not_sum_three_sq`:

* small cases `n ≤ 1` are explicit;
* if `4 ∣ n`, write `n = 4 * m`; then `¬IsExcludedForm m`
  (by `excluded_form_four_mul_iff`), so the induction hypothesis represents `m`
  and `four_mul_sum_three_sq` lifts the representation back to `n`;
* otherwise `n > 1` and `4 ∤ n`, so the witness `(d, p)` exists and
  `dirichlet_key_lemma` represents `n` directly. -/
theorem three_sq_of_dirichlet_witness
    (Hwit : DirichletWitnessProperty) {n : ℕ} (hne : ¬IsExcludedForm n) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h4 : 4 ∣ n
    · -- 4 ∣ n: descend to m = n / 4
      obtain ⟨m, hm⟩ := h4
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- m = 0 ⟹ n = 0 = 0² + 0² + 0²
        exact ⟨0, 0, 0, by rw [hm, hm0]; norm_num⟩
      · -- m ≥ 1 ⟹ m < n, recurse
        have hmlt : m < n := by omega
        have hmne : ¬IsExcludedForm m := by
          intro hmm
          apply hne
          rw [hm]
          exact excluded_form_four_mul_iff.mpr hmm
        have hrec := ih m hmlt hmne
        have h4m := four_mul_sum_three_sq hrec
        rw [hm]
        exact h4m
    · -- 4 ∤ n
      by_cases hle : n ≤ 1
      · -- n ∈ {0, 1}
        interval_cases n
        · exact ⟨0, 0, 0, by norm_num⟩
        · exact ⟨1, 0, 0, by norm_num⟩
      · -- n > 1 and 4 ∤ n: invoke the Dirichlet witness
        push_neg at hle
        obtain ⟨d, p, hd, hp, hpp, hqr⟩ := Hwit hne h4 hle
        haveI : Fact (Nat.Prime p) := ⟨hpp⟩
        exact dirichlet_key_lemma (n := n) (d := d) (p := p) hle hd hp hqr

/-- **The sufficiency axiom is redundant given the Dirichlet witness.**

This is the restatement matching `ThreeSquares.not_excluded_form_is_sum_three_sq`,
showing that axiom is derivable rather than independent: it follows from
`dirichlet_key_lemma` (imported axiom) plus `DirichletWitnessProperty`. -/
theorem not_excluded_form_is_sum_three_sq_of_witness
    (Hwit : DirichletWitnessProperty) {n : ℕ} (h : ¬IsExcludedForm n) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n :=
  three_sq_of_dirichlet_witness Hwit h

/-- **Conditional Legendre three-square theorem.**

Combining the proven necessity (`excluded_form_not_sum_three_sq`) with the
conditional sufficiency above: assuming the Dirichlet witness property, `n` is a
sum of three integer squares iff `n` is not of excluded form. -/
theorem legendre_three_squares_of_witness
    (Hwit : DirichletWitnessProperty) (n : ℕ) :
    (∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = n) ↔ ¬IsExcludedForm n :=
  ⟨fun hrep hf => excluded_form_not_sum_three_sq hf hrep,
   three_sq_of_dirichlet_witness Hwit⟩

end ThreeSquares
