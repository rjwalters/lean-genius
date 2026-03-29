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
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.Tactic

set_option maxHeartbeats 800000

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
  apply Summable.of_nonneg_of_le
  · intro k; positivity
  · intro k
    show (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial ≤ (1 / 2) ^ k
    rw [one_div, one_div, inv_pow]
    apply inv_anti₀ (by positivity : (0 : ℝ) < 2 ^ k)
    have hk_le : k ≤ (N + 1 + k + 1).factorial := by
      calc k ≤ N + 1 + k + 1 := by omega
        _ ≤ (N + 1 + k + 1).factorial := Nat.self_le_factorial _
    exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk_le
  · exact summable_geometric_of_lt_one (by positivity) (by norm_num)

/- ## Sum Splitting -/

/-- The factorial lacunary sum splits into partial sum + tail.
    Uses tsum_eq_add_tsum_ite or sum_add_tsum_compl. -/
theorem lacunarySum_factorial_split (N : ℕ) :
    (∑' k, (1 : ℝ) / 2 ^ (k + 1).factorial) =
    (∑ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ^ (k + 1).factorial) +
    (∑' k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial) := by
  induction N with
  | zero =>
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [factorial_lacunary_summable.tsum_eq_zero_add]
    congr 1
    apply tsum_congr; intro k; congr 1; congr 1; congr 1; omega
  | succ n ih =>
    rw [ih]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [add_assoc]
    congr 1
    have h := (factorial_tail_summable n).tsum_eq_zero_add
    simp only [show n + 1 + 0 + 1 = n + 1 + 1 from by omega] at h
    rw [h]
    congr 1
    apply tsum_congr; intro k
    simp only [show n + 1 + (k + 1) + 1 = n + 1 + 1 + k + 1 from by omega]

/- ## Partial Sum Representation -/

/-- For k ≤ N, (N+1)! ≥ (k+1)!. Factorial is monotone. -/
theorem factorial_mono_succ (k N : ℕ) (hk : k ≤ N) :
    (k + 1).factorial ≤ (N + 1).factorial := by
  exact Nat.factorial_le (by omega)

/-- The partial sum of the factorial series can be expressed as
    an integer divided by 2^{(N+1)!}. -/
theorem factorialPartialSum_eq_div (N : ℕ) :
    ∃ (a : ℤ),
    (∑ k ∈ Finset.range (N + 1), (1 : ℝ) / 2 ^ (k + 1).factorial) =
    (a : ℝ) / (2 : ℝ) ^ (N + 1).factorial := by
  induction N with
  | zero =>
    exact ⟨1, by simp⟩
  | succ n ih =>
    obtain ⟨a, ha⟩ := ih
    have hle : (n + 1).factorial ≤ (n + 2).factorial :=
      Nat.factorial_le (by omega)
    set d := (n + 2).factorial - (n + 1).factorial with hd_def
    refine ⟨a * (2 : ℤ) ^ d + 1, ?_⟩
    rw [Finset.sum_range_succ, ha]
    have h2pos : (2 : ℝ) ^ (n + 1).factorial ≠ 0 := by positivity
    have h2pos' : (2 : ℝ) ^ (n + 1 + 1).factorial ≠ 0 := by positivity
    have hpow : (2 : ℝ) ^ (n + 1 + 1).factorial =
        (2 : ℝ) ^ (n + 1).factorial * (2 : ℝ) ^ d := by
      rw [show (n + 1 + 1).factorial = (n + 1).factorial + d from
        (Nat.add_sub_cancel' hle).symm]
      exact pow_add 2 (n + 1).factorial d
    rw [hpow]
    push_cast
    field_simp

/- ## Tail Bounds -/

/-- The tail of the factorial series starting at N+1 is strictly positive. -/
theorem factorial_tail_pos (N : ℕ) :
    0 < ∑' k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial := by
  exact (factorial_tail_summable N).tsum_pos (fun k => by positivity) 0 (by positivity)

/-- The tail of the factorial series is bounded by 2/2^{(N+2)!}.
    Uses the fact that (N+1+k+1)! ≥ (N+2)! + k for k ≥ 0,
    which follows from strict monotonicity of factorials. -/
theorem factorial_tail_le (N : ℕ) :
    ∑' k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial ≤
    2 / (2 : ℝ) ^ (N + 2).factorial := by
  have hfact_bound : ∀ k, (N + 2).factorial + k ≤ (N + 1 + k + 1).factorial := by
    intro k
    rw [show N + 1 + k + 1 = N + 2 + k from by omega]
    calc (N + 2).factorial + k
        ≤ (N + 2).factorial * (k + 1) := by nlinarith [Nat.factorial_pos (N + 2)]
      _ ≤ (N + 2 + k).factorial := by
          induction k with
          | zero => simp
          | succ m ihm =>
            calc (N + 2).factorial * (m + 1 + 1)
                = (N + 2).factorial * (m + 1) + (N + 2).factorial := by ring
              _ ≤ (N + 2 + m).factorial + (N + 2 + m).factorial :=
                  add_le_add ihm (Nat.factorial_le (by omega))
              _ ≤ (N + 2 + m).factorial * (N + 2 + m + 1) := by
                  nlinarith [Nat.factorial_pos (N + 2 + m)]
              _ = (N + 2 + m + 1).factorial := by
                  rw [Nat.factorial_succ]; ring
  have hle : ∀ k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial ≤
      (1 / 2 ^ (N + 2).factorial) * (1 / 2) ^ k := by
    intro k
    have hrw : (1 : ℝ) / 2 ^ (N + 2).factorial * (1 / 2) ^ k =
        1 / 2 ^ ((N + 2).factorial + k) := by
      rw [pow_add, one_div, one_div, inv_pow, ← mul_inv]; ring_nf
    rw [hrw]
    exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
      (by positivity : (0 : ℝ) < 2 ^ ((N + 2).factorial + k))
      (by exact_mod_cast Nat.pow_le_pow_right (by omega : 1 ≤ 2) (hfact_bound k))
  have hgeo_summable : Summable (fun k => (1 / 2 ^ (N + 2).factorial) * ((1 : ℝ) / 2) ^ k) :=
    Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) (by norm_num))
  calc ∑' k, (1 : ℝ) / 2 ^ (N + 1 + k + 1).factorial
      ≤ ∑' k, (1 / 2 ^ (N + 2).factorial) * ((1 : ℝ) / 2) ^ k :=
        hasSum_le hle (factorial_tail_summable N).hasSum hgeo_summable.hasSum
    _ = (1 / 2 ^ (N + 2).factorial) * ∑' k, ((1 : ℝ) / 2) ^ k := tsum_mul_left
    _ = (1 / 2 ^ (N + 2).factorial) * 2 := by
        rw [tsum_geometric_of_lt_one (by positivity) (by norm_num)]; norm_num
    _ = 2 / (2 : ℝ) ^ (N + 2).factorial := by ring

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
    Transcendental ℚ x :=
  fun halg => h ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr halg)

end Erdos247Aristotle
