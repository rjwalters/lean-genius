import Proofs.Erdos85FiniteDropWitnesses

/-!
# Cofinal plane-order drops imply the negation of Erdős 85

The order-49 program is the `q = 7` instance of a natural uniform target:
construct a `q`-regular-enough C4-free graph on `q² - 1` vertices and rule
out minimum degree `q` on `q²` vertices.  This file proves that a cofinal
family of such instances gives arbitrarily large strict drops, which is the
literal negation of eventual monotonicity in Erdős Problem 85.
-/

namespace Erdos85

open Filter

structure PlaneOrderDropWitness (q : Nat) : Prop where
  three_le : 3 ≤ q
  previous : C4FreeMinDegreeWitness (q * q - 1) q
  no_square : ¬ C4FreeMinDegreeWitness (q * q) q

theorem PlaneOrderDropWitness.strict_drop {q : Nat}
    (h : PlaneOrderDropWitness q) :
    minDegreeForC4 (q * q) < minDegreeForC4 (q * q - 1) := by
  have hsq : 9 ≤ q * q := by nlinarith [h.three_le]
  have hsucc : q * q - 1 + 1 = q * q := by omega
  have hdrop := minDegreeForC4_drop_of_witness_of_no_succ_witness
    (n := q * q - 1) (d := q) (by omega) h.previous
    (by
      rw [hsucc]
      exact h.no_square)
  rw [hsucc] at hdrop
  exact hdrop

/-- Plane orders carrying the two graph-theoretic inputs occur beyond every
natural-number bound.  The bound is placed directly on the drop location
`q² - 1`, so no auxiliary growth lemma is needed by consumers. -/
def CofinalPlaneOrderDropFamily : Prop :=
  ∀ N : Nat, ∃ q : Nat, N ≤ q * q - 1 ∧ PlaneOrderDropWitness q

theorem erdos85Negation_of_cofinalPlaneOrderDropFamily
    (h : CofinalPlaneOrderDropFamily) : Erdos85Negation := by
  intro N
  obtain ⟨q, hN, hq⟩ := h N
  refine ⟨q * q - 1, hN, ?_⟩
  have hsq : 9 ≤ q * q := by nlinarith [hq.three_le]
  have hsucc : q * q - 1 + 1 = q * q := by omega
  rw [hsucc]
  exact hq.strict_drop

theorem not_erdos85Question_of_cofinalPlaneOrderDropFamily
    (h : CofinalPlaneOrderDropFamily) : ¬ Erdos85Question := by
  intro hquestion
  obtain ⟨N, hN⟩ := eventually_atTop.1 hquestion
  obtain ⟨n, hn, hdrop⟩ :=
    erdos85Negation_of_cofinalPlaneOrderDropFamily h N
  exact (Nat.not_lt_of_ge (hN n hn)) hdrop

/-- The checked order-48 graph and the order-49 nonexistence goal instantiate
the uniform plane-order package at `q = 7`. -/
theorem planeOrderDropWitness_seven
    (hno49 : ¬ C4FreeMinDegreeWitness 49 7) :
    PlaneOrderDropWitness 7 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · norm_num
    exact boza48_degreeSeven_witness
  · norm_num
    exact hno49

end Erdos85
