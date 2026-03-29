/-
  Aristotle targets for Erdős Problem #859
  Routine supporting lemmas for automated proof search.
  See Erdos859Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture or deep density results
  - Known results likely in Mathlib (divisor function, powerset properties)
  - Clean theorem statements with no definition sorries
  - No axioms

  Provable targets:
  1. divisors_mul_coprime: |divisors(mn)| = |divisors(m)| * |divisors(n)| for coprime m, n
  2. primePower_divisors: divisors(p^a) = {1, p, p^2, ..., p^a}
  3. density_univ_one: density of Set.univ is 1
  4. subset_sum_count: |powerset(divisors(n))| = 2^tau(n)
-/

import Mathlib

namespace Erdos859Aristotle

open Nat Finset Filter

/- Definitions (replicated from Erdos859Problem.lean) -/

noncomputable def sigma (n : ℕ) : ℕ :=
  (Nat.divisors n).sum id

def tau (n : ℕ) : ℕ :=
  (Nat.divisors n).card

def HasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N => (((Finset.range (N + 1)).filter (· ∈ S)).card : ℝ) / N)
    atTop (𝓝 d)

/- Target 1: Divisor count is multiplicative for coprime arguments -/

theorem divisors_mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m > 0) (hn : n > 0) :
    (Nat.divisors (m * n)).card = (Nat.divisors m).card * (Nat.divisors n).card := by
  rw [Nat.Coprime.divisors_mul hmn]
  exact Finset.card_product _ _

/- Target 2: Divisors of a prime power form {1, p, p^2, ..., p^a} -/

theorem primePower_divisors (p : ℕ) (hp : p.Prime) (a : ℕ) :
    Nat.divisors (p ^ a) = (Finset.range (a + 1)).map ⟨fun i => p ^ i, fun _ _ => by
      intro h; exact Nat.pow_right_injective hp.two_le h⟩ :=
  Nat.divisors_prime_pow hp

/- Target 3: Density of the full set is 1 -/

theorem density_univ_one : HasNaturalDensity Set.univ 1 := by
  unfold HasNaturalDensity
  -- Simplify: filter on Set.univ is identity, card of range(N+1) is N+1
  have hsimp : ∀ N : ℕ,
      (((Finset.range (N + 1)).filter (· ∈ Set.univ)).card : ℝ) = ↑N + 1 := by
    intro N
    rw [Finset.filter_true_of_mem (fun _ _ => Set.mem_univ _), Finset.card_range]
    push_cast; ring
  simp_rw [hsimp]
  -- Goal: Tendsto (fun N => (↑N + 1) / ↑N) atTop (𝓝 1)
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨⌈ε⁻¹⌉₊ + 1, fun n hn => ?_⟩
  have hn_pos : (0 : ℝ) < ↑n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.dist_eq]
  have hsub : (↑n + 1 : ℝ) / ↑n - 1 = 1 / ↑n := by
    have : (↑n : ℝ) ≠ 0 := ne_of_gt hn_pos
    field_simp; ring
  rw [hsub, abs_of_pos (div_pos one_pos hn_pos), div_lt_iff hn_pos, one_mul]
  -- Goal: 1 < ε * ↑n (since ε⁻¹ < ↑n)
  calc (1 : ℝ) = ε * ε⁻¹ := (mul_inv_cancel₀ (ne_of_gt hε)).symm
    _ < ε * ↑n := by
        apply mul_lt_mul_of_pos_left _ hε
        calc ε⁻¹ ≤ ↑⌈ε⁻¹⌉₊ := Nat.le_ceil _
          _ < ↑⌈ε⁻¹⌉₊ + 1 := lt_add_one _
          _ ≤ ↑n := by exact_mod_cast hn

/- Target 4: Powerset of divisors has size 2^tau(n) -/

theorem subset_sum_count (n : ℕ) (hn : n > 0) :
    (Nat.divisors n).powerset.card = 2 ^ (tau n) := by
  simp [tau, Finset.card_powerset]

/- Target 5: tau(1) = 1 -/

theorem tau_one : tau 1 = 1 := by
  simp [tau, Nat.divisors]

/- Target 6: tau(p) = 2 for prime p -/

theorem tau_prime (p : ℕ) (hp : p.Prime) : tau p = 2 := by
  simp [tau, Nat.divisors_prime hp]

/- Target 7: tau(p^a) = a + 1 -/

theorem tau_prime_power (p : ℕ) (hp : p.Prime) (a : ℕ) :
    tau (p ^ a) = a + 1 := by
  simp [tau, Nat.divisors_prime_pow hp]

end Erdos859Aristotle
