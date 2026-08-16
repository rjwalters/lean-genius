import Proofs.Erdos85FiniteDropCapstone

/-!
# Plane-order criterion for a negative solution of Erdős 85

The order-49 program is the `q = 7` instance of a scalable negative route.
If, for unbounded `q`, a degree-`q` C4-free witness exists on `q² - 1`
vertices but not on `q²` vertices, then the threshold drops at arbitrarily
large orders and Erdős 85 has a negative answer.
-/

namespace Erdos85

theorem erdos85Negation_of_unbounded_planeOrder_witness_gap
    (hgap : ∀ N : Nat, ∃ q : Nat,
      3 ≤ q ∧ N ≤ q * q - 1 ∧
      C4FreeMinDegreeWitness (q * q - 1) q ∧
      ¬ C4FreeMinDegreeWitness (q * q) q) :
    Erdos85Negation := by
  intro N
  obtain ⟨q, hq, hN, hw, hno⟩ := hgap N
  have hqpos : 1 ≤ q * q := by nlinarith
  have hsucc : q * q - 1 + 1 = q * q := Nat.sub_add_cancel hqpos
  have hnoSucc : ¬ C4FreeMinDegreeWitness (q * q - 1 + 1) q := by
    rw [hsucc]
    exact hno
  refine ⟨q * q - 1, hN, ?_⟩
  exact minDegreeForC4_drop_of_witness_of_no_succ_witness
    (n := q * q - 1) (d := q) (by nlinarith) hw hnoSucc

/-- It is enough to construct the plane-order gaps cofinally in `q`; the
order itself is then automatically unbounded. -/
theorem erdos85Negation_of_eventual_planeOrder_witness_gap
    (hgap : ∀ᶠ q in Filter.atTop,
      C4FreeMinDegreeWitness (q * q - 1) q ∧
      ¬ C4FreeMinDegreeWitness (q * q) q) :
    Erdos85Negation := by
  apply erdos85Negation_of_unbounded_planeOrder_witness_gap
  intro N
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.1 hgap
  let q := max Q (N + 3)
  have hqQ : Q ≤ q := Nat.le_max_left _ _
  have hqN : N + 3 ≤ q := Nat.le_max_right _ _
  have hcert := hQ q hqQ
  refine ⟨q, by omega, ?_, hcert.1, hcert.2⟩
  have hq1 : 1 ≤ q := by omega
  have hqq : q ≤ q * q := Nat.le_mul_of_pos_right q hq1
  omega

end Erdos85
