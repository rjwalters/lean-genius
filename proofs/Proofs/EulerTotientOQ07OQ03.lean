import Mathlib

/-
# Coprimality and gcd of a finite family of Euler totients

**Open Question (`euler-totient-oq-07-oq-03`)**: generalize the two-argument
coprimality characterisation `gcd(φ m, φ n) = 1 ↔ m ∈ {1,2} ∨ n ∈ {1,2}`
(`euler-totient-oq-07`) to a *finite family* `{φ(nᵢ)}_{i ∈ s}`:

* When is the family **pairwise coprime**?
* When is the gcd of the **whole family** a fixed power of `2`?

## The driving observation

`φ(k)` is even for every `k > 2` (`Nat.totient_even`), and `φ(0) = 0` is also
even, while `φ(1) = φ(2) = 1`.  So call an argument **non-unital** when
`k ∉ {1, 2}` (equivalently `φ(k) ≠ 1`); every non-unital argument has
`2 ∣ φ(k)`.  Two totients are coprime exactly when at least one argument is
unital (`Nat.totient_coprime_totient_iff`).  This immediately scales to families:

* **Pairwise coprime ⇔ at most one non-unital argument.**  If two distinct
  indices were both non-unital their totients would share the factor `2`; if at
  most one is non-unital every pair contains a unital argument with `φ = 1`.

* **Whole-family gcd.**  If *every* argument is non-unital the family gcd is
  even (`2` divides every member); for arguments `≥ 3` it is therefore `≥ 2`.

* **Powers of two.**  If every `φ(nᵢ)` is itself a power of `2`, then so is the
  family gcd — a divisor of a prime power is a prime power.  This pins the
  "fixed power of `2`" sub-question: the gcd is a power of `2` whenever the
  individual totients are (e.g. for products of distinct Fermat primes).

## Contents

* `two_dvd_totient_of_not_unital` — `n ∉ {1,2} ⟹ 2 ∣ φ n` (covers `n = 0`).
* `pairwise_coprime_totient_iff`  — **headline**: the family `{φ(nᵢ)}` is
  pairwise coprime iff at most one index is non-unital.
* `two_dvd_family_gcd_of_forall_not_unital` — all non-unital ⟹ `2 ∣ gcd`.
* `two_le_family_gcd_of_forall_three_le`     — nonempty, all `≥ 3` ⟹ `2 ≤ gcd`.
* `family_gcd_isPowerOfTwo`        — all `φ(nᵢ)` powers of `2` ⟹ family gcd is a
  power of `2`.

Fully machine-checked: `0` sorries, `0` axioms (the `decide` calls in the
examples are kernel reductions over concrete small naturals, not `native_decide`).
-/

namespace EulerTotientOQ07OQ03

open Nat Finset

/-- An argument is **unital** when its totient is `1`, i.e. `n ∈ {1, 2}`. -/
def Unital (n : ℕ) : Prop := n = 1 ∨ n = 2

instance : DecidablePred Unital := fun n => by unfold Unital; infer_instance

/-- `φ n = 1 ↔ n ∈ {1, 2}`, the totient-level meaning of `Unital`. -/
theorem totient_eq_one_iff_unital (n : ℕ) : φ n = 1 ↔ Unital n :=
  Nat.totient_eq_one_iff

/-- **Even totient for non-unital arguments.**  If `n ∉ {1, 2}` then `2 ∣ φ n`.
This unifies the two ways an argument can be non-unital: `n = 0` (where
`φ 0 = 0`) and `n ≥ 3` (where `Nat.totient_even` applies). -/
theorem two_dvd_totient_of_not_unital {n : ℕ} (hn : ¬ Unital n) : 2 ∣ φ n := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · -- `n ≥ 1`, and `n ≠ 1`, `n ≠ 2`, so `n ≥ 3`.
    unfold Unital at hn
    push_neg at hn
    exact (Nat.totient_even (by omega)).two_dvd

/-- Two totients are coprime iff at least one argument is unital — the
two-argument characterisation, restated through `Unital`. -/
theorem coprime_totient_iff_unital (m n : ℕ) :
    (φ m).Coprime (φ n) ↔ Unital m ∨ Unital n := by
  rw [Nat.totient_coprime_totient_iff]; rfl

/-- **Headline (Part A).**  The finite family of totients `{φ(nᵢ)}_{i ∈ s}` is
pairwise coprime **iff at most one index is non-unital** — i.e. the non-unital
indices form a set of size `≤ 1`.  Two distinct non-unital arguments would share
the factor `2`; conversely if at most one argument is non-unital every pair
contains a unital argument, whose totient `1` is coprime to everything. -/
theorem pairwise_coprime_totient_iff {ι : Type*} (s : Finset ι) (n : ι → ℕ) :
    (Set.Pairwise ↑s (fun i j => (φ (n i)).Coprime (φ (n j)))) ↔
      (s.filter (fun i => ¬ Unital (n i))).card ≤ 1 := by
  rw [Finset.card_le_one]
  constructor
  · -- pairwise coprime ⟹ at most one non-unital index
    intro hpw a ha b hb
    simp only [Finset.mem_filter] at ha hb
    by_contra hab
    -- `a, b` distinct, both non-unital, both in `s`: contradiction with coprimality
    have hcop := hpw (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1) hab
    simp only [coprime_totient_iff_unital] at hcop
    rcases hcop with h | h
    · exact ha.2 h
    · exact hb.2 h
  · -- at most one non-unital index ⟹ pairwise coprime
    intro hcard i hi j hj hij
    rw [coprime_totient_iff_unital]
    by_contra hcon
    push_neg at hcon
    -- both `i, j` non-unital ⟹ both in the filter ⟹ they must be equal
    have hi' : i ∈ s.filter (fun i => ¬ Unital (n i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hi, hcon.1⟩
    have hj' : j ∈ s.filter (fun i => ¬ Unital (n i)) :=
      Finset.mem_filter.mpr ⟨Finset.mem_coe.mp hj, hcon.2⟩
    exact hij (hcard i hi' j hj')

/-- **Part B (divisibility).**  If *every* argument is non-unital, the gcd of the
whole family `{φ(nᵢ)}_{i ∈ s}` is even: `2` divides each member, hence the gcd. -/
theorem two_dvd_family_gcd_of_forall_not_unital {ι : Type*} (s : Finset ι)
    (n : ι → ℕ) (h : ∀ i ∈ s, ¬ Unital (n i)) :
    2 ∣ s.gcd (fun i => φ (n i)) :=
  Finset.dvd_gcd fun i hi => two_dvd_totient_of_not_unital (h i hi)

/-- **Part B (lower bound).**  For a nonempty family all of whose arguments are
`≥ 3`, the gcd of the totients is at least `2`: they share a nontrivial common
factor.  (Restricting to `≥ 3` keeps every member positive, so the gcd is
positive.) -/
theorem two_le_family_gcd_of_forall_three_le {ι : Type*} (s : Finset ι)
    (n : ι → ℕ) (hne : s.Nonempty) (h : ∀ i ∈ s, 3 ≤ n i) :
    2 ≤ s.gcd (fun i => φ (n i)) := by
  have hpos : s.gcd (fun i => φ (n i)) ≠ 0 := by
    rw [Ne, Finset.gcd_eq_zero_iff]
    push_neg
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, hi, (Nat.totient_pos.mpr (by have := h i hi; omega)).ne'⟩
  have hdvd : 2 ∣ s.gcd (fun i => φ (n i)) :=
    two_dvd_family_gcd_of_forall_not_unital s n
      (fun i hi => by unfold Unital; have := h i hi; omega)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hdvd

/-- **Part D (powers of two).**  If every totient `φ(nᵢ)` in a nonempty family is
a power of `2`, then the gcd of the whole family is also a power of `2`.  A
divisor of `2 ^ k` is a power of `2` (`Nat.dvd_prime_pow`), and the family gcd
divides any one member.  This answers the "fixed power of `2`" sub-question: it
holds precisely when the individual totients are powers of `2` (as for products
of distinct Fermat primes, where `φ` is a power of `2`). -/
theorem family_gcd_isPowerOfTwo {ι : Type*} (s : Finset ι) (n : ι → ℕ)
    (hne : s.Nonempty) (h : ∀ i ∈ s, ∃ k, φ (n i) = 2 ^ k) :
    ∃ K, s.gcd (fun i => φ (n i)) = 2 ^ K := by
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨k, hk⟩ := h i₀ hi₀
  have hdvd : s.gcd (fun i => φ (n i)) ∣ 2 ^ k := by
    have hd := Finset.gcd_dvd (f := fun i => φ (n i)) hi₀
    simpa only [hk] using hd
  obtain ⟨K, _, hK⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨K, hK⟩

/-! ### Worked examples -/

-- A pairwise-coprime family with exactly one non-unital index: `n = (1, 2, 9)`.
-- Only `9` is non-unital, so the totients `φ1 = 1, φ2 = 1, φ9 = 6` are pairwise
-- coprime.
example :
    Set.Pairwise (↑({0, 1, 2} : Finset (Fin 3)))
      (fun i j => (φ (![1, 2, 9] i)).Coprime (φ (![1, 2, 9] j))) := by
  rw [pairwise_coprime_totient_iff]
  decide

-- A family that is NOT pairwise coprime: `n = (9, 15)`, two non-unital indices,
-- `φ9 = 6` and `φ15 = 8` share the factor `2`.
example :
    ¬ Set.Pairwise (↑({0, 1} : Finset (Fin 2)))
        (fun i j => (φ (![9, 15] i)).Coprime (φ (![9, 15] j))) := by
  rw [pairwise_coprime_totient_iff]
  decide

-- Whole-family gcd is even when all arguments are `≥ 3`: for `n = (5, 7, 9)`,
-- `φ = (4, 6, 6)` and `gcd = 2`.
example : 2 ≤ (({0, 1, 2} : Finset (Fin 3))).gcd (fun i => φ (![5, 7, 9] i)) :=
  two_le_family_gcd_of_forall_three_le _ _ (by decide) (by decide)

-- Powers of two: for the Fermat primes `n = (3, 5, 17)`, `φ = (2, 4, 16)`, all
-- powers of `2`, so the family gcd `= 2` is a power of `2`.
example : ∃ K, (({0, 1, 2} : Finset (Fin 3))).gcd (fun i => φ (![3, 5, 17] i)) = 2 ^ K :=
  family_gcd_isPowerOfTwo _ _ (by decide)
    (by
      intro i hi
      fin_cases i
      · exact ⟨1, by decide⟩
      · exact ⟨2, by decide⟩
      · exact ⟨4, by decide⟩)

end EulerTotientOQ07OQ03
