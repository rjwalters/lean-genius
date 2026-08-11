import Mathlib

/-!
# Degree-sixteen zero-layer reduced partition classification

This module isolates the finite Presburger classification used by the
zero-layer census.  A sorted eight-slot partition of sixteen whose nonzero
parts are at least two is one of exactly fifty-five patterns.
-/

namespace Erdos85

/-- The fifty-five positive partitions of sixteen with every part at least
two, represented in nonincreasing order and padded by zeroes to eight
slots. -/
def ZeroLayerReducedPartitionPattern
    (a b c d e f g h : ℕ) : Prop :=
  match a with
  | 16 =>
      (b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0)
  | 14 =>
      (b = 2 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0)
  | 13 =>
      (b = 3 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0)
  | 12 =>
      (b = 4 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 2 ∧ c = 2 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0)
  | 11 =>
      (b = 5 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 2 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0)
  | 10 =>
      (b = 6 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 2 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 3 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 2 ∧ c = 2 ∧ d = 2 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0)
  | 9 =>
      (b = 7 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 5 ∧ c = 2 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 3 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 2 ∧ d = 2 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0)
  | 8 =>
      (b = 8 ∧ c = 0 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 6 ∧ c = 2 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 5 ∧ c = 3 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 4 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 2 ∧ d = 2 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 3 ∧ d = 2 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 2 ∧ c = 2 ∧ d = 2 ∧ e = 2 ∧ f = 0 ∧ g = 0 ∧ h = 0)
  | 7 =>
      (b = 7 ∧ c = 2 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 6 ∧ c = 3 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 5 ∧ c = 4 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 5 ∧ c = 2 ∧ d = 2 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 3 ∧ d = 2 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 3 ∧ d = 3 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 2 ∧ d = 2 ∧ e = 2 ∧ f = 0 ∧ g = 0 ∧ h = 0)
  | 6 =>
      (b = 6 ∧ c = 4 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 6 ∧ c = 2 ∧ d = 2 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 5 ∧ c = 5 ∧ d = 0 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 5 ∧ c = 3 ∧ d = 2 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 4 ∧ d = 2 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 3 ∧ d = 3 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 2 ∧ d = 2 ∧ e = 2 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 3 ∧ d = 2 ∧ e = 2 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 2 ∧ c = 2 ∧ d = 2 ∧ e = 2 ∧ f = 2 ∧ g = 0 ∧ h = 0)
  | 5 =>
      (b = 5 ∧ c = 4 ∧ d = 2 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 5 ∧ c = 3 ∧ d = 3 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 5 ∧ c = 2 ∧ d = 2 ∧ e = 2 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 4 ∧ d = 3 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 3 ∧ d = 2 ∧ e = 2 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 3 ∧ d = 3 ∧ e = 2 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 2 ∧ d = 2 ∧ e = 2 ∧ f = 2 ∧ g = 0 ∧ h = 0)
  | 4 =>
      (b = 4 ∧ c = 4 ∧ d = 4 ∧ e = 0 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 4 ∧ d = 2 ∧ e = 2 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 3 ∧ d = 3 ∧ e = 2 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 4 ∧ c = 2 ∧ d = 2 ∧ e = 2 ∧ f = 2 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 3 ∧ d = 3 ∧ e = 3 ∧ f = 0 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 3 ∧ d = 2 ∧ e = 2 ∧ f = 2 ∧ g = 0 ∧ h = 0) ∨
      (b = 2 ∧ c = 2 ∧ d = 2 ∧ e = 2 ∧ f = 2 ∧ g = 2 ∧ h = 0)
  | 3 =>
      (b = 3 ∧ c = 3 ∧ d = 3 ∧ e = 2 ∧ f = 2 ∧ g = 0 ∧ h = 0) ∨
      (b = 3 ∧ c = 2 ∧ d = 2 ∧ e = 2 ∧ f = 2 ∧ g = 2 ∧ h = 0)
  | 2 =>
      (b = 2 ∧ c = 2 ∧ d = 2 ∧ e = 2 ∧ f = 2 ∧ g = 2 ∧ h = 2)
  | _ => False
set_option maxHeartbeats 2000000 in
/-- Every sorted reduced used-order list at degree sixteen belongs to the
explicit fifty-five-pattern census. -/
theorem zeroLayer_reduced_partition_classification
    (a b c d e f g h : ℕ)
    (hsum : a + b + c + d + e + f + g + h = 16)
    (hsorted : a ≥ b ∧ b ≥ c ∧ c ≥ d ∧ d ≥ e ∧ e ≥ f ∧ f ≥ g ∧ g ≥ h)
    (hparts : (a = 0 ∨ 2 ≤ a) ∧ (b = 0 ∨ 2 ≤ b) ∧
      (c = 0 ∨ 2 ≤ c) ∧ (d = 0 ∨ 2 ≤ d) ∧
      (e = 0 ∨ 2 ≤ e) ∧ (f = 0 ∨ 2 ≤ f) ∧
      (g = 0 ∨ 2 ≤ g) ∧ (h = 0 ∨ 2 ≤ h)) :
    ZeroLayerReducedPartitionPattern a b c d e f g h := by
  have ha : a ≤ 16 := by omega
  have hb : b ≤ 16 := by omega
  have hc : c ≤ 16 := by omega
  have hd : d ≤ 16 := by omega
  have he : e ≤ 16 := by omega
  have hf : f ≤ 16 := by omega
  have hg : g ≤ 16 := by omega
  have hh : h ≤ 16 := by omega
  interval_cases a <;> try omega
  all_goals interval_cases b <;> try omega
  all_goals interval_cases c <;> try omega
  all_goals interval_cases d <;> try omega
  all_goals interval_cases e <;> try omega
  all_goals interval_cases f <;> try omega
  all_goals interval_cases g <;> try omega
  all_goals interval_cases h <;>
    simp [ZeroLayerReducedPartitionPattern] at *

end Erdos85
