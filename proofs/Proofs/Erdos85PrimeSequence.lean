import Proofs.Erdos85PrimeFamily
import Mathlib.Data.Nat.Prime.Nth

/-!
# An unbounded exact subsequence for Erdős Problem 85

The finite-field polarity construction, specialized to prime fields, gives an
explicit strictly increasing sequence of orders on which `minDegreeForC4` is
known exactly and its values are themselves strictly increasing.
-/

namespace Erdos85

/-- The zero-indexed sequence of prime numbers. -/
noncomputable def erdos85Prime (k : ℕ) : ℕ := k.nth Nat.Prime

/-- The projective-plane order associated with the `k`-th prime field. -/
noncomputable def polarityOrder (k : ℕ) : ℕ :=
  erdos85Prime k ^ 2 + erdos85Prime k + 1

theorem erdos85Prime_prime (k : ℕ) : Nat.Prime (erdos85Prime k) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k

theorem erdos85Prime_strictMono : StrictMono erdos85Prime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

theorem polarityOrder_strictMono : StrictMono polarityOrder := by
  intro i j hij
  have hp : erdos85Prime i < erdos85Prime j := erdos85Prime_strictMono hij
  simp only [polarityOrder]
  nlinarith

/-- Exact value of the Erdős 85 threshold at every prime projective-plane
order. -/
theorem minDegreeForC4_polarityOrder (k : ℕ) :
    minDegreeForC4 (polarityOrder k) = erdos85Prime k + 1 := by
  let p := erdos85Prime k
  have hp : Nat.Prime p := erdos85Prime_prime k
  simpa [polarityOrder, p] using Polarity.minDegreeForC4_prime p hp

/-- Along the prime-field polarity orders, the exact Erdős 85 thresholds are
strictly increasing. -/
theorem minDegreeForC4_polarityOrder_strictMono :
    StrictMono (fun k ↦ minDegreeForC4 (polarityOrder k)) := by
  intro i j hij
  change minDegreeForC4 (polarityOrder i) < minDegreeForC4 (polarityOrder j)
  rw [minDegreeForC4_polarityOrder, minDegreeForC4_polarityOrder]
  exact Nat.add_lt_add_right (erdos85Prime_strictMono hij) 1

/-- Publication-facing package: there are strictly increasing orders with
strictly increasing, exactly known Erdős 85 thresholds, and these threshold
values exceed every prescribed bound. -/
theorem exists_unbounded_exact_strict_sequence :
    ∃ N D : ℕ → ℕ,
      StrictMono N ∧ StrictMono D ∧
      (∀ k, minDegreeForC4 (N k) = D k) ∧
      (∀ B, ∃ k, B < D k) := by
  refine ⟨polarityOrder, fun k ↦ erdos85Prime k + 1,
    polarityOrder_strictMono, ?_, minDegreeForC4_polarityOrder, ?_⟩
  · exact erdos85Prime_strictMono.add_const 1
  · intro B
    refine ⟨B + 1, ?_⟩
    have hle : B + 1 ≤ erdos85Prime (B + 1) :=
      Nat.le_nth (fun hf => (Nat.infinite_setOf_prime hf).elim)
    change B < erdos85Prime (B + 1) + 1
    omega

/-- In particular, exact values occur arbitrarily far out with both the graph
order and the threshold larger than any prescribed bound. -/
theorem exists_arbitrarily_large_exact_value (B : ℕ) :
    ∃ n d, B < n ∧ B < d ∧ minDegreeForC4 n = d := by
  let k := B + 1
  have hle : k ≤ erdos85Prime k :=
    Nat.le_nth (fun hf => (Nat.infinite_setOf_prime hf).elim)
  refine ⟨polarityOrder k, erdos85Prime k + 1, ?_, ?_, minDegreeForC4_polarityOrder k⟩
  · have hpB : B < erdos85Prime k := by omega
    simp only [polarityOrder]
    omega
  · omega

end Erdos85
