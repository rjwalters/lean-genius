/-
# Erdős Problem #1021 — Open Question 01
## Does ex(n, G_k) = o(n^{3/2}) for any k ≥ 4?

Erdős Problem #1021 asks: for every k ≥ 3, does there exist c_k > 0 such that
ex(n, G_k) ≪ n^{3/2 - c_k}?

This open question (OQ-01) focuses on the weaker version: for any fixed k ≥ 4,
is ex(n, G_k) = o(n^{3/2})?

## Background

G_k is the bipartite graph with:
- k "primary" vertices {y₁,...,y_k}
- C(k,2) "pair" vertices {z₁,...,z_{C(k,2)}}, each z_j adjacent to exactly one pair {y_a, y_b}

The trivial upper bound is ex(n, G_k) = O(n^{3/2}), from the Kővári-Sós-Turán theorem
(since G_k contains K_{2, C(k,2)}).

The question is whether the exponent can be beaten:
- Strong form: ∃ c_k > 0, ex(n, G_k) ≪ n^{3/2 - c_k}
- Weak form (OQ-01): ex(n, G_k) = o(n^{3/2})

## Known Results

- **k = 3**: G_3 = C_6, and ex(n, C_6) ≪ n^{7/6} (Bondy-Simonovits). So k=3 is solved.
- **k ≥ 4**: Both the strong and weak forms are OPEN.
- **Density lower bound**: The probabilistic method gives ex(n, G_k) ≫ n^{3/2 - 1/(k-1)},
  showing the trivial bound is nearly tight in some sense.
- **Zarankiewicz connection**: This is a Zarankiewicz-type problem.

## Status

OPEN for all k ≥ 4. The strong form (c_k > 0) is conjectured true by Erdős-Simonovits.
The weak form (o(n^{3/2})) is also open, and even this is not known for any k ≥ 4.

## References

- Bondy, J.A., Simonovits, M. (1974). "Cycles of even length in graphs." J. Combin. Theory 16.
- Kővári, T., Sós, V., Turán, P. (1954). "On a problem of K. Zarankiewicz." Coll. Math. 3:50–57.
- Füredi, Z. (1991). "On the number of edges of quadrilateral-free graphs." J. Combin. Theory 68.
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Proofs.Erdos1021Problem

open Erdos1021

namespace Erdos1021OQ01

/-! ## Part I: The OQ-01 Question -/

/-- **OQ-01**: For any fixed k ≥ 4, is ex(n, G_k) = o(n^{3/2})?

    This is a restriction of the parent's `weak_conjecture` to the open cases k ≥ 4. -/
def weakConjectureK4 : Prop :=
  ∀ k : ℕ, k ≥ 4 → isLittleO (fun n => exGk k n) (fun n => (n : ℝ) ^ (3/2 : ℝ))

/-- OQ-01 is implied by the parent's weak conjecture. -/
theorem oq01_from_weak : weak_conjecture → weakConjectureK4 := by
  intro hweak k hk
  exact hweak k (by omega)

/-- The parent's strong conjecture implies OQ-01 (via the parent's strong→weak chain). -/
theorem oq01_from_strong : erdos_1021_conjecture → weakConjectureK4 :=
  fun hstrong => oq01_from_weak (strong_implies_weak hstrong)

/-! ## Part II: The Trivial Bound vs o(n^{3/2}) -/

/-- The trivial upper bound O(n^{3/2}) does NOT imply o(n^{3/2}).
    These are strictly different asymptotic classes. -/
theorem big_O_not_implies_little_o :
    ∃ f : ℕ → ℝ,
      (∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, f n ≤ C * (n : ℝ) ^ (3/2 : ℝ)) ∧
      ¬isLittleO f (fun n => (n : ℝ) ^ (3/2 : ℝ)) := by
  -- Witness: f(n) = n^(3/2) itself satisfies f ≪ n^(3/2) but NOT f = o(n^(3/2))
  use fun n => (n : ℝ) ^ (3/2 : ℝ)
  constructor
  · -- f(n) = n^(3/2) satisfies f ≪ n^(3/2) (trivially with C = 1)
    exact ⟨1, one_pos, 0, fun n _ => by simp⟩
  · -- But f(n) / n^(3/2) = 1 ↛ 0
    intro h
    obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
    -- For n ≥ N with n > 0, f(n) = n^(3/2) > (1/2) * n^(3/2), contradiction
    have hn : ∃ m : ℕ, m ≥ N ∧ (m : ℝ) ^ (3/2 : ℝ) > 0 := by
      use N + 1
      exact ⟨Nat.le_succ N, Real.rpow_pos_of_pos (by positivity) _⟩
    obtain ⟨m, hm_ge, hm_pos⟩ := hn
    have := hN m hm_ge
    linarith

/-- The Kővári-Sós-Turán (KST) theorem gives the trivial bound O(n^{3/2}) for ex(n, G_k).
    This is the best unconditional upper bound known.

    Reference: Kővári-Sós-Turán (1954).
    The bound follows because G_k contains K_{2, C(k,2)} as a subgraph. -/
axiom kst_trivial_bound (k : ℕ) (hk : k ≥ 4) :
    ∃ C > 0, ∀ n : ℕ, exGk k n ≤ C * (n : ℝ) ^ (3/2 : ℝ)

/-- OQ-01 asks for something strictly beyond the KST trivial bound. -/
theorem oq01_strictly_beyond_kst (k : ℕ) (hk : k ≥ 4)
    (hoq01 : isLittleO (fun n => exGk k n) (fun n => (n : ℝ) ^ (3/2 : ℝ))) :
    ∃ C > 0, ∀ n : ℕ, exGk k n ≤ C * (n : ℝ) ^ (3/2 : ℝ) := by
  -- o(n^{3/2}) implies O(n^{3/2}) (taking ε = 1 in the o() definition)
  obtain ⟨N, hN⟩ := hoq01 1 one_pos
  -- For n < N, bound is finite, take max
  use max 1 (Finset.sup (Finset.range N)
    (fun n => if (n : ℝ) ^ (3/2 : ℝ) > 0 then ⌈exGk k n / (n : ℝ) ^ (3/2 : ℝ)⌉₊ else 1) + 1)
  intro n
  sorry -- The o() definition gives a uniform O() bound

/-! ## Part III: The k = 3 Case is Settled -/

/-- The k = 3 case (G_3 ≅ C_6) satisfies both the strong and weak conjectures.
    This is the only case where the exponent below 3/2 is explicitly known.

    Bondy-Simonovits: ex(n, C_6) ≪ n^{7/6}. -/
def k3_weak_holds : Prop :=
  isLittleO (fun n => exGk 3 n) (fun n => (n : ℝ) ^ (3/2 : ℝ))

/-- For k = 3, the strong conjecture (c₃ = 1/3) implies the weak conjecture. -/
theorem k3_strong_implies_weak : k3_weak_holds := by
  -- Use strong_implies_weak from the parent, specialized to k = 3
  have := strong_implies_weak
  sorry -- Requires k3_case_solved (itself a sorry in the parent)

/-! ## Part IV: Independence of Cases -/

/-- If OQ-01 holds for k, it does not automatically hold for k+1.
    Larger G_k are harder to avoid (fewer edges allowed), so ex(n, G_{k+1}) ≥ ex(n, G_k)
    if G_{k+1} ⊇ G_k as a minor, but the bipartite pair graph relationship is not monotone. -/
theorem ex_not_obviously_monotone_in_k :
    ¬(∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → ∀ n : ℕ, exGk k₁ n ≤ exGk k₂ n) := by
  sorry -- The monotonicity of extremal numbers in k is non-trivial for pair graphs

/-! ## Part V: Lower Bound Obstruction -/

/-- The probabilistic method gives ex(n, G_k) ≥ c·n^{3/2 - 1/(k-1)} for some constant c > 0.
    This shows the trivial bound n^{3/2} is approximately tight.

    For k = 4: ex(n, G_4) ≥ c·n^{4/3}
    For k = 5: ex(n, G_5) ≥ c·n^{5/4}

    Reference: Alon, Krivelevich, Sudakov (2003), or probabilistic method.
    This lower bound is known but deep; we axiomatize it. -/
axiom probabilistic_lower_bound (k : ℕ) (hk : k ≥ 4) :
    ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, exGk k n ≥ c * (n : ℝ) ^ (3/2 - 1/(k - 1 : ℝ))

/-- The lower bound exponent 3/2 - 1/(k-1) approaches 3/2 from below as k → ∞.
    This means the gap between upper (3/2) and lower bound (3/2 - 1/(k-1)) shrinks. -/
theorem lower_bound_exponent_approach (k : ℕ) (hk : k ≥ 2) :
    (3 : ℝ)/2 - 1/(k - 1 : ℝ) < 3/2 := by
  have hk1 : (k : ℝ) - 1 > 0 := by exact_mod_cast Nat.sub_pos_of_lt (by omega)
  linarith [div_pos one_pos hk1]

/-- As k → ∞, the lower bound exponent 3/2 - 1/(k-1) → 3/2. -/
theorem lower_bound_exponent_tendsto :
    Filter.Tendsto (fun k : ℕ => (3 : ℝ)/2 - 1/((k : ℝ) - 1)) Filter.atTop (nhds (3/2)) := by
  -- Step 1: (k : ℝ) - 1 → ∞
  have h_sub : Filter.Tendsto (fun k : ℕ => (k : ℝ) - 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    exact ⟨Nat.ceil (b + 2), fun k hk => by
      have : b + 2 ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hk)
      linarith⟩
  -- Step 2: 1/((k:ℝ) - 1) → 0  have h_inv : Filter.Tendsto (fun k : ℕ => 1/((k : ℝ) - 1)) Filter.atTop (nhds 0) := by
    simp_rw [one_div]
    exact tendsto_inv_atTop_zero.comp h_sub
  -- Step 3: 3/2 - 1/((k:ℝ)-1) → 3/2 - 0 = 3/2
  have h := Filter.Tendsto.sub (tendsto_const_nhds (x := (3 : ℝ)/2)) h_inv
  simp only [sub_zero] at h
  exact h

/-! ## Part VI: The OQ-01 in Context -/

/-- **Summary of OQ-01 status**:

    Known:
    - k = 3: SOLVED (ex(n, G_3) = ex(n, C_6) ≪ n^{7/6} < n^{3/2})
    - k ≥ 4: OPEN (even o(n^{3/2}) is not known)

    Trivial bound: KST gives ex(n, G_k) ≪ n^{3/2} for all k ≥ 3.
    Lower bound: probabilistic method gives ex(n, G_k) ≥ c·n^{3/2 - 1/(k-1)}.

    OQ-01 (weak form): for any k ≥ 4, ex(n, G_k) = o(n^{3/2})?

    This file contains:
    - 2 provable results (big_O ≠ little_o, lower bound exponent approaches 3/2)
    - 1 axiomatic result: KST trivial bound
    - 1 axiomatic result: probabilistic lower bound
    - 3 sorry results: k3 weak conjecture proof, k3/k independence, and o() bound uniformity

    Status: SURVEY + INFRASTRUCTURE
-/

end Erdos1021OQ01
