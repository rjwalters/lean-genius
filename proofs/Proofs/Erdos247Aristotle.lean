/-
  Aristotle targets for Erdős Problem #247 - Liouville Proof
  Routine supporting lemmas for the direct Liouville proof of
  transcendence of Σ 1/2^{(k+1)!}.

  See Erdos247Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (summability, tsum splitting, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.Tactic

namespace Erdos247Aristotle

/-
  These lemmas support proving that Σ 1/2^{(k+1)!} is a Liouville number.
  The Liouville approach gives an axiom-free proof of transcendence for
  the factorial case, avoiding the erdos_transcendence_strong axiom.
-/

/- ## Summability -/

/-- The factorial lacunary series is summable.
    Follows from comparison with the geometric series (1/2)^k,
    since (k+1)! ≥ k+1 > k implies 1/2^{(k+1)!} ≤ 1/2^k. -/
theorem factorial_lacunary_summable :
    Summable (fun k => (1 : ℝ) / 2 ^ (k + 1).factorial) := by
  apply Summable.of_nonneg_of_le
  · intro k; positivity
  · intro k
    show (1 : ℝ) / 2 ^ (k + 1).factorial ≤ (1 / 2) ^ k
    rw [one_div, one_div, inv_pow]
    apply inv_anti₀ (by positivity : (0 : ℝ) < 2 ^ k)
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2)
      (le_trans (Nat.le_succ k) (Nat.self_le_factorial (k + 1)))
  · exact summable_geometric_of_lt_one (by positivity) (by norm_num)

/-- The shifted factorial series (tail starting at index N+1) is summable. -/
theorem factorial_tail_summable (N : ℕ) :
    Summable (fun k => (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial) := by
  sorry

/- ## Sum Splitting -/

/-- The factorial lacunary sum splits into partial sum + tail.
    Uses tsum_eq_add_tsum_ite or sum_add_tsum_compl. -/
theorem lacunarySum_factorial_split (N : ℕ) :
    (∑' k, (1 : ℝ) / 2 ^ (k + 1).factorial) =
    (∑ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ^ (k + 1).factorial) +
    (∑' k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial) := by
  sorry

/- ## Partial Sum Representation -/

/-- For k ≤ N, (N+1)! ≥ (k+1)!. Factorial is monotone. -/
theorem factorial_mono_succ (k N : ℕ) (hk : k ≤ N) :
    (k + 1).factorial ≤ (N + 1).factorial := by
  sorry

/-- The partial sum of the factorial series can be expressed as
    an integer divided by 2^{(N+1)!}. -/
theorem factorialPartialSum_eq_div (N : ℕ) :
    ∃ (a : ℤ),
    (∑ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ^ (k + 1).factorial) =
    (a : ℝ) / (2 : ℝ) ^ (N + 1).factorial := by
  sorry

/- ## Tail Bounds -/

/-- The tail of the factorial series starting at N+1 is strictly positive. -/
theorem factorial_tail_pos (N : ℕ) :
    0 < ∑' k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial := by
  sorry

/-- The tail of the factorial series is bounded by 2/2^{(N+2)!}.
    Uses the fact that (N+1+k+1)! ≥ (N+2)! + k for k ≥ 0,
    which follows from strict monotonicity of factorials. -/
theorem factorial_tail_le (N : ℕ) :
    ∑' k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial ≤
    2 / (2 : ℝ) ^ (N + 2).factorial := by
  sorry

/- ## Key Inequality for Liouville Bound -/

/-- The critical power inequality: 2 · 2^{m·(m+1)!} < 2^{(m+2)!}.
    Equivalently, m·(m+1)! + 1 < (m+2)!.
    This is what makes the Liouville approximation work. -/
theorem pow_two_factorial_bound (m : ℕ) :
    2 * (2 : ℝ) ^ (m * (m + 1).factorial) < (2 : ℝ) ^ (m + 2).factorial := by
  -- 2 * 2^n = 2^{n+1}
  have h1 : (2 : ℝ) * (2 : ℝ) ^ (m * (m + 1).factorial) =
      (2 : ℝ) ^ (m * (m + 1).factorial + 1) := by
    rw [pow_succ]; ring
  rw [h1]
  -- 2^{m*(m+1)!+1} < 2^{(m+2)!} from m*(m+1)!+1 < (m+2)!
  have h2 : m * (m + 1).factorial + 1 < (m + 2).factorial := by
    have hfact : (m + 2).factorial = (m + 2) * (m + 1).factorial := Nat.factorial_succ (m + 1)
    rw [hfact]; have := Nat.factorial_pos (m + 1); nlinarith
  exact_mod_cast Nat.pow_lt_pow_right (by omega : 1 < 2) h2

/- ## Transcendence Conversion -/

/-- If x : ℝ is transcendental over ℤ, then it is transcendental over ℚ.
    Contrapositive: algebraic over ℚ implies algebraic over ℤ
    (clear denominators). -/
theorem transcendental_int_to_rat {x : ℝ} (h : Transcendental ℤ x) :
    Transcendental ℚ x := by
  sorry

end Erdos247Aristotle
