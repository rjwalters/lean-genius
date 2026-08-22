import Proofs.Erdos85RealBottomEigenvalueBipartite

/-!
# Strict bottom spectral gap for connected nonbipartite regular graphs

The elementary maximum-coordinate estimate places every real adjacency
eigenvalue of a `k`-regular graph in `[-k,k]`.  The already-banked equality
case says that a connected graph with eigenvalue `-k` is bipartite.  Thus a
connected nonbipartite regular graph has the strict lower bound `-k < μ`.
For the binary-square pairing `theta² = k-μ`, this gives `theta² < 2k`.
-/

open SimpleGraph

namespace Erdos85

/-- Every real eigenvalue of a finite regular graph is at least the negative
degree. -/
theorem neg_degree_le_real_eigenvalue_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (μ : ℝ) (w : V → ℝ) (hw : w ≠ 0)
    (heigen : ∀ x, ∑ y ∈ D.neighborFinset x, w y = μ * w x) :
    -(k : ℝ) ≤ μ := by
  letI : Nonempty V := Function.ne_iff.mp hw |>.nonempty
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max (fun x => |w x|)
  let amplitude : ℝ := |w x₀|
  have hmax : ∀ x, |w x| ≤ amplitude := hx₀
  have hamp : 0 < amplitude := by
    have ha0 : 0 ≤ amplitude := abs_nonneg _
    apply lt_of_le_of_ne ha0
    intro ha
    apply hw
    funext x
    have hx : |w x| = 0 := le_antisymm (by simpa [← ha] using hmax x)
      (abs_nonneg _)
    exact abs_eq_zero.mp hx
  have hsum : |∑ y ∈ D.neighborFinset x₀, w y| ≤
      (k : ℝ) * amplitude := by
    calc
      |∑ y ∈ D.neighborFinset x₀, w y| ≤
          ∑ y ∈ D.neighborFinset x₀, |w y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _y ∈ D.neighborFinset x₀, amplitude :=
        Finset.sum_le_sum fun y _ => hmax y
      _ = (k : ℝ) * amplitude := by
        rw [Finset.sum_const, D.card_neighborFinset_eq_degree, hreg,
          nsmul_eq_mul]
  have hmul : |μ| * amplitude ≤ (k : ℝ) * amplitude := by
    rw [heigen x₀, abs_mul, show |w x₀| = amplitude from rfl] at hsum
    exact hsum
  have habs : |μ| ≤ (k : ℝ) := by
    nlinarith
  nlinarith [neg_abs_le μ]

/-- The bottom eigenvalue inequality is strict for a connected
nonbipartite regular graph. -/
theorem neg_degree_lt_real_eigenvalue_of_connected_nonbipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) (hnotbip : ¬D.IsBipartite)
    (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (μ : ℝ) (w : V → ℝ) (hw : w ≠ 0)
    (heigen : ∀ x, ∑ y ∈ D.neighborFinset x, w y = μ * w x) :
    -(k : ℝ) < μ := by
  have hle := neg_degree_le_real_eigenvalue_of_regular
    D k hreg μ w hw heigen
  apply lt_of_le_of_ne hle
  intro heq
  apply hnotbip
  apply isBipartite_of_real_negativeDegree_eigenvector D hconn k hreg w hw
  intro x
  rw [heigen x, ← heq]

/-- A paired adjacency root over a connected nonbipartite `k`-regular
defect graph satisfies the strict square bound `theta² < 2k`. -/
theorem paired_root_sq_lt_two_mul_degree_of_connected_nonbipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) (hnotbip : ¬D.IsBipartite)
    (k : ℕ) (hreg : ∀ x, D.degree x = k)
    (μ θ : ℝ) (w : V → ℝ) (hw : w ≠ 0)
    (heigen : ∀ x, ∑ y ∈ D.neighborFinset x, w y = μ * w x)
    (hpair : θ ^ 2 = (k : ℝ) - μ) :
    θ ^ 2 < 2 * k := by
  have hμ := neg_degree_lt_real_eigenvalue_of_connected_nonbipartite
    D hconn hnotbip k hreg μ w hw heigen
  rw [hpair]
  push_cast
  linarith

end Erdos85

#print axioms Erdos85.neg_degree_le_real_eigenvalue_of_regular
#print axioms Erdos85.neg_degree_lt_real_eigenvalue_of_connected_nonbipartite
#print axioms
  Erdos85.paired_root_sq_lt_two_mul_degree_of_connected_nonbipartite
