/-!
# Erdős Problem #196: Monotone 4-Term APs in Permutations

Must every permutation of ℕ contain a monotone 4-term arithmetic progression?

## Key Results

- **k = 3**: YES, every permutation has a monotone 3-AP (DEGS 1977)
- **k = 4**: OPEN (the main conjecture)
- **k = 5**: NO, there exist permutations avoiding monotone 5-APs (DEGS 1977)
- LeSaulnier–Vijay (2011): odd-CD 4-APs can be avoided; 3-AP with odd CD always exists

## References

- Davis, Entringer, Graham, Simmons (1977)
- LeSaulnier, Vijay (2011)
- [ErGr79], [ErGr80]
- <https://erdosproblems.com/196>
-/

import Mathlib.Logic.Equiv.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

open Function

/-! ## Core Definitions -/

/-- A permutation of ℕ is a bijection ℕ → ℕ. -/
abbrev Perm := ℕ ≃ ℕ

/-- Three values form an arithmetic progression: b − a = c − b with a < b < c. -/
def IsAP3 (a b c : ℕ) : Prop :=
  b - a = c - b ∧ a < b ∧ b < c

/-- Four values form an arithmetic progression. -/
def IsAP4 (a b c d : ℕ) : Prop :=
  b - a = c - b ∧ c - b = d - c ∧ a < b ∧ b < c ∧ c < d

/-- Five values form an arithmetic progression. -/
def IsAP5 (a b c d e : ℕ) : Prop :=
  IsAP4 a b c d ∧ d - c = e - d ∧ d < e

/-! ## Monotone APs in Permutations -/

/-- A permutation contains a monotone 3-term AP. -/
def HasMonotone3AP (x : Perm) : Prop :=
  ∃ i j k : ℕ, (i < j ∧ j < k ∨ i > j ∧ j > k) ∧
    IsAP3 (x i) (x j) (x k)

/-- A permutation contains a monotone 4-term AP. -/
def HasMonotone4AP (x : Perm) : Prop :=
  ∃ i j k l : ℕ, (i < j ∧ j < k ∧ k < l ∨ i > j ∧ j > k ∧ k > l) ∧
    IsAP4 (x i) (x j) (x k) (x l)

/-- A permutation contains a monotone 5-term AP. -/
def HasMonotone5AP (x : Perm) : Prop :=
  ∃ i j k l m : ℕ, (i < j ∧ j < k ∧ k < l ∧ l < m ∨
    i > j ∧ j > k ∧ k > l ∧ l > m) ∧
    IsAP5 (x i) (x j) (x k) (x l) (x m)

/-! ## Main Conjecture -/

/-- **Erdős Problem #196** (OPEN): Every permutation of ℕ contains
    a monotone 4-term arithmetic progression. -/
axiom erdos_196_conjecture :
  ∀ x : Perm, HasMonotone4AP x

/-! ## Known Results -/

/-- **DEGS (1977)**: Every permutation of ℕ contains a monotone 3-AP. -/
axiom degs_3ap_theorem :
  ∀ x : Perm, HasMonotone3AP x

/-- **DEGS (1977)**: There exists a permutation avoiding monotone 5-APs. -/
axiom degs_5ap_counterexample :
  ∃ x : Perm, ¬HasMonotone5AP x

/-- The 4-AP conjecture implies the 3-AP theorem. -/
theorem conjecture_implies_3ap (hconj : ∀ x : Perm, HasMonotone4AP x) :
    ∀ x : Perm, HasMonotone3AP x := by
  intro x
  obtain ⟨i, j, k, l, hmon, hap⟩ := hconj x
  use i, j, k
  constructor
  · cases hmon with
    | inl hinc => left; exact ⟨hinc.1, hinc.2.1⟩
    | inr hdec => right; exact ⟨hdec.1, hdec.2.1⟩
  · unfold IsAP3 IsAP4 at *; omega

/-! ## Common Difference Parity -/

/-- A 4-AP has odd common difference. -/
def IsAP4OddCD (a b c d : ℕ) : Prop :=
  IsAP4 a b c d ∧ (b - a) % 2 = 1

/-- A 4-AP has even common difference. -/
def IsAP4EvenCD (a b c d : ℕ) : Prop :=
  IsAP4 a b c d ∧ (b - a) % 2 = 0

/-- **LeSaulnier–Vijay (2011)**: There exists a permutation avoiding
    all monotone 4-APs with odd common difference. -/
axiom lesaulnier_vijay_odd_avoidable :
  ∃ x : Perm, ¬∃ i j k l : ℕ,
    (i < j ∧ j < k ∧ k < l ∨ i > j ∧ j > k ∧ k > l) ∧
    IsAP4OddCD (x i) (x j) (x k) (x l)

/-- Every 4-AP has either odd or even common difference. -/
theorem ap4_parity (a b c d : ℕ) (h : IsAP4 a b c d) :
    IsAP4OddCD a b c d ∨ IsAP4EvenCD a b c d := by
  unfold IsAP4OddCD IsAP4EvenCD
  by_cases hp : (b - a) % 2 = 1
  · left; exact ⟨h, hp⟩
  · right; exact ⟨h, by omega⟩

/-- Key structural reduction: the conjecture is equivalent to saying that
    permutations avoiding odd-CD 4-APs must contain even-CD 4-APs. -/
axiom conjecture_equiv_even_forced :
  (∀ x : Perm, HasMonotone4AP x) ↔
    ∀ x : Perm,
      (¬∃ i j k l : ℕ, (i < j ∧ j < k ∧ k < l ∨ i > j ∧ j > k ∧ k > l) ∧
        IsAP4OddCD (x i) (x j) (x k) (x l)) →
      ∃ i j k l : ℕ, (i < j ∧ j < k ∧ k < l ∨ i > j ∧ j > k ∧ k > l) ∧
        IsAP4EvenCD (x i) (x j) (x k) (x l)

/-! ## Non-Extendability -/

/-- If a permutation avoids monotone 4-APs, every 3-AP is non-extendable:
    the value a + 3d is forbidden at all later monotone indices. -/
axiom non_extendable_constraint :
  ∀ (x : Perm), ¬HasMonotone4AP x →
    ∀ (i j k : ℕ), i < j → j < k →
      IsAP3 (x i) (x j) (x k) →
      ∀ l : ℕ, l > k → x l ≠ x k + (x j - x i)

/-! ## Erdős–Szekeres Connection -/

/-- **Erdős–Szekeres (1935)**: Every sequence of (r−1)(s−1)+1 distinct
    numbers contains an increasing subsequence of length r or a decreasing
    one of length s. This guarantees long monotone subsequences but not APs. -/
axiom erdos_szekeres :
  ∀ (n r s : ℕ), n > (r - 1) * (s - 1) →
    ∀ (seq : Fin n → ℕ), Injective seq →
      (∃ indices : Fin r → Fin n, StrictMono indices ∧ StrictMono (seq ∘ indices)) ∨
      (∃ indices : Fin s → Fin n, StrictMono indices ∧ StrictAnti (seq ∘ indices))
