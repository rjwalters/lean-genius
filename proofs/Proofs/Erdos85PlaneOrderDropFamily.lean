import Proofs.Erdos85FiniteDropWitnesses
import Proofs.Erdos85PolarityEven
import Mathlib.FieldTheory.Finite.GaloisField

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

theorem erdos85Negation_iff_not_question :
    Erdos85Negation ↔ ¬ Erdos85Question := by
  constructor
  · intro hneg hquestion
    obtain ⟨N, hN⟩ := eventually_atTop.1 hquestion
    obtain ⟨n, hn, hdrop⟩ := hneg N
    exact (Nat.not_lt_of_ge (hN n hn)) hdrop
  · intro hnot N
    by_contra hnone
    apply hnot
    apply eventually_atTop.2
    refine ⟨N, fun n hn => ?_⟩
    by_contra hmono
    have hdrop : minDegreeForC4 (n + 1) < minDegreeForC4 n :=
      Nat.lt_of_not_ge hmono
    exact hnone ⟨n, hn, hdrop⟩

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

/-- For characteristic-two finite fields, the entire `(q² - 1)` existence
half is already supplied by the deleted polarity graph.  Consequently only
the square-order nonexistence statement remains to produce a drop. -/
theorem planeOrderDropWitness_of_evenField
    (K : Type*) [Field K] [Finite K] [DecidableEq K]
    (hq : 3 ≤ Nat.card K) (h2 : (2 : K) = 0)
    (hnoSquare : ¬ C4FreeMinDegreeWitness
      (Nat.card K * Nat.card K) (Nat.card K)) :
    PlaneOrderDropWitness (Nat.card K) := by
  exact ⟨hq,
    Polarity.c4FreeMinDegreeWitness_even_delete_absolute_nucleus K h2,
    hnoSquare⟩

universe u

/-- A cofinal supply of finite characteristic-two fields for which the
square-order witness is impossible.  The polarity construction discharges
the companion existence theorem automatically. -/
def CofinalEvenFieldSquareExclusion : Prop :=
  ∀ N : Nat,
    ∃ (K : Type u) (_ : Field K) (_ : Finite K) (_ : DecidableEq K),
      N ≤ Nat.card K * Nat.card K - 1 ∧
      3 ≤ Nat.card K ∧
      (2 : K) = 0 ∧
      ¬ C4FreeMinDegreeWitness (Nat.card K * Nat.card K) (Nat.card K)

theorem cofinalPlaneOrderDropFamily_of_evenFieldSquareExclusion
    (h : CofinalEvenFieldSquareExclusion) :
    CofinalPlaneOrderDropFamily := by
  intro N
  obtain ⟨K, fieldK, finiteK, decEqK, hN, hq, h2, hno⟩ := h N
  letI : Field K := fieldK
  letI : Finite K := finiteK
  letI : DecidableEq K := decEqK
  exact ⟨Nat.card K, hN,
    planeOrderDropWitness_of_evenField K hq h2 hno⟩

theorem erdos85Negation_of_evenFieldSquareExclusion
    (h : CofinalEvenFieldSquareExclusion) : Erdos85Negation :=
  erdos85Negation_of_cofinalPlaneOrderDropFamily
    (cofinalPlaneOrderDropFamily_of_evenFieldSquareExclusion h)

theorem not_erdos85Question_of_evenFieldSquareExclusion
    (h : CofinalEvenFieldSquareExclusion) : ¬ Erdos85Question :=
  not_erdos85Question_of_cofinalPlaneOrderDropFamily
    (cofinalPlaneOrderDropFamily_of_evenFieldSquareExclusion h)

/-- The exact uniform square-order obstruction along binary prime powers from
`q = 8` onward.  The omitted `k = 2` case is genuinely false: `f(16) = 5`,
so order 16 has a C4-free minimum-degree-four witness. -/
def BinarySquareOrderExclusion : Prop :=
  ∀ k : Nat, 3 ≤ k →
    ¬ C4FreeMinDegreeWitness ((2 ^ k) * (2 ^ k)) (2 ^ k)

theorem cofinalEvenFieldSquareExclusion_of_binary
    (h : BinarySquareOrderExclusion) :
    CofinalEvenFieldSquareExclusion.{0} := by
  intro N
  let k := N + 3
  let K := GaloisField 2 k
  letI : DecidableEq K := Classical.decEq K
  have hk : k ≠ 0 := by simp [k]
  have hk3 : 3 ≤ k := by simp [k]
  have hcard : Nat.card K = 2 ^ k := GaloisField.card 2 k hk
  have hpow : 2 * k ≤ 2 ^ k :=
    Nat.mul_le_pow (a := 2) (by decide : 2 ≠ 1) k
  have hq4 : 4 ≤ Nat.card K := by
    rw [hcard]
    omega
  refine ⟨K, inferInstance, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · apply Nat.le_sub_of_add_le
    rw [hcard]
    have hNq : N + 1 ≤ 2 ^ k := by
      dsimp [k] at hpow ⊢
      omega
    exact hNq.trans (Nat.le_mul_of_pos_right _ (by positivity))
  · omega
  · exact CharP.cast_eq_zero K 2
  · simpa [hcard] using h k hk3

theorem erdos85Negation_of_binarySquareOrderExclusion
    (h : BinarySquareOrderExclusion) : Erdos85Negation :=
  erdos85Negation_of_evenFieldSquareExclusion
    (cofinalEvenFieldSquareExclusion_of_binary h)

theorem not_erdos85Question_of_binarySquareOrderExclusion
    (h : BinarySquareOrderExclusion) : ¬ Erdos85Question :=
  not_erdos85Question_of_evenFieldSquareExclusion
    (cofinalEvenFieldSquareExclusion_of_binary h)

end Erdos85
