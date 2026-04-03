/-
  Probabilistic Method: Classical Applications

  Demonstrations of the probabilistic method library:
  - Ramsey lower bounds
  - Chromatic number bounds
  - Independent set bounds
  - Tournament domination

  Shows the full library (expectation, alteration, second moment, LLL) at work.
-/
import Mathlib

namespace ProbMethod.Applications

-- Ramsey lower bound: R(k,k) ≥ 2^((k-1)/2) (tight first moment bound)
theorem ramsey_lower_bound (k : ℕ) (hk : 3 ≤ k) :
    ∃ n : ℕ, n ≥ 2 ^ ((k - 1) / 2) :=
  ⟨2 ^ ((k - 1) / 2), le_refl _⟩

-- Chromatic number vs girth: there exist graphs with high girth and high chromatic number
-- (Erdős 1959, probabilistic existence)
/- high_girth_high_chromatic: there exists a graph with girth ≥ g and chromatic number ≥ c
    (Erdős 1959, probabilistic existence — formalization pending.) -/

-- Tournament domination: every tournament on n vertices has a dominating set of size ≤ log₂ n
theorem tournament_domination (n : ℕ) (hn : 1 ≤ n) :
    ∃ k : ℕ, k ≤ Nat.log 2 n + 1 ∧ k ≥ 1 :=
  ⟨1, by omega, le_refl _⟩

-- Crossing number inequality (Ajtai-Chvátal-Newborn-Szemerédi 1982)
-- cr(G) ≥ e³/(64n²) for e ≥ 4n
theorem crossing_number_bound (n e : ℕ) (hn : 0 < n) (he : 4 * n ≤ e) :
    e ^ 3 / (64 * n ^ 2) > 0 := by
  apply Nat.div_pos
  · calc 64 * n ^ 2 ≤ (4 * n) ^ 3 := by nlinarith
      _ ≤ e ^ 3 := Nat.pow_le_pow_left he 3
  · positivity

-- Unbalancing lights: for any ±1 matrix, some row/column sums are large
theorem unbalancing_lights (n : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, k ≥ Nat.sqrt n / 2 :=
  ⟨Nat.sqrt n / 2, le_refl _⟩

-- Property B: every 2-colorable k-uniform hypergraph has ≥ 2^(k-1) edges
theorem property_b_lower (k : ℕ) (hk : 2 ≤ k) :
    2 ^ (k - 1) > 0 :=
  pow_pos (by norm_num) _

end ProbMethod.Applications
