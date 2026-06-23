import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic
import Proofs.AngleTrisectionOQ04
import Proofs.AngleTrisectionOQ05OQ01

/-
# Regular Polygons Constructible with Multi-Fold Origami but Not Marked Ruler

## Open Question (angle-trisection-oq-04-oq-04)

"Which regular polygons are constructible with multi-fold origami
but cannot be constructed with a marked ruler (neusis)?"

## Key Result

The regular 11-gon witnesses the strict gap between 1-fold (= marked ruler) and 2-fold origami:
- φ(11) = 10 = 2 · 5, which is **5-smooth** (2-fold origami constructible)
- but **not 3-smooth** (not marked-ruler-constructible, since 5 > 3)

Since single-fold origami ≡ marked ruler (Alperin-Lang 2006), this shows 2-fold origami
is strictly more powerful than single-fold origami = marked ruler.

## The Constructibility Hierarchy

| Tool | Algebraic Condition on φ(n) | Examples |
|------|-----------------------------|----------|
| Compass-and-straightedge | φ(n) = 2^k | 3, 4, 5, 6, 15, 17, ... |
| Marked ruler = 1-fold origami | φ(n) \| 2^a · 3^b | 7, 9, 13, 14, 19, 21, ... |
| 2-fold origami | φ(n) \| 2^a · 3^b · 5^c | 11, 23, 25, 31, ... |
| k-fold origami | IsKFoldConstructible φ(n) k | increases at each prime level |

## Status
- 0 sorries
- 0 axioms

## Builds On
- AngleTrisectionOQ04.lean: IsTwoThreeNumber, NeusisDegrees
- AngleTrisectionOQ05OQ01.lean: IsKFoldConstructible, degree_ten_2fold,
  degree_eleven_4fold, fold_2_bound, fold_4_bound
-/

namespace AngleTrisectionOQ04OQ04

open AngleTrisectionOQ04 AngleTrisectionOQ05OQ01

/-! ## Euler Totient Values -/

theorem totient_11_eq : Nat.totient 11 = 10 := by decide

theorem totient_23_eq : Nat.totient 23 = 22 := by decide

/-! ## General Principle: Large Prime Factor Blocks Neusis Constructibility -/

/-- If a prime q > 3 divides d, then d does not divide any 2^a · 3^b.
    Since marked-ruler constructibility requires d | 2^a · 3^b, this
    rules out neusis for any degree with such a prime factor. -/
theorem not_twoThree_of_large_prime_dvd {d q : ℕ}
    (hq : Nat.Prime q) (hq3 : q > 3) (hqd : q ∣ d) :
    ¬ IsTwoThreeNumber d := by
  rintro ⟨-, a, b, hdvd⟩
  have hq_dvd : q ∣ 2 ^ a * 3 ^ b := dvd_trans hqd hdvd
  rcases hq.dvd_mul.mp hq_dvd with h | h
  · have : q ≤ 2 := Nat.le_of_dvd (by omega) (hq.dvd_of_dvd_pow h)
    omega
  · have : q ≤ 3 := Nat.le_of_dvd (by omega) (hq.dvd_of_dvd_pow h)
    omega

/-! ## The Regular 11-Gon -/

/-- φ(11) = 10 has prime factor 5 > 3, so the 11-gon is NOT marked-ruler-constructible. -/
theorem ngon_11_not_neusis : ¬ IsTwoThreeNumber (Nat.totient 11) :=
  totient_11_eq ▸ not_twoThree_of_large_prime_dvd
    (by decide : Nat.Prime 5) (by omega) (by norm_num : (5 : ℕ) ∣ 10)

/-- φ(11) = 10 = 2 · 5 is 5-smooth, so the 11-gon IS 2-fold origami constructible. -/
theorem ngon_11_2fold : IsKFoldConstructible (Nat.totient 11) 2 :=
  totient_11_eq ▸ degree_ten_2fold

/-- The 11-gon: 2-fold origami constructible, but NOT marked-ruler-constructible. -/
theorem ngon_11_2fold_not_neusis :
    IsKFoldConstructible (Nat.totient 11) 2 ∧ ¬ IsTwoThreeNumber (Nat.totient 11) :=
  ⟨ngon_11_2fold, ngon_11_not_neusis⟩

/-! ## The Regular 23-Gon -/

/-- φ(23) = 22 has prime factor 11 > 3, so the 23-gon is NOT marked-ruler-constructible. -/
theorem ngon_23_not_neusis : ¬ IsTwoThreeNumber (Nat.totient 23) :=
  totient_23_eq ▸ not_twoThree_of_large_prime_dvd
    (by decide : Nat.Prime 11) (by omega) (by norm_num : (11 : ℕ) ∣ 22)

/-- φ(23) = 22 = 2 · 11 is 11-smooth, so the 23-gon IS 4-fold origami constructible. -/
theorem ngon_23_4fold : IsKFoldConstructible (Nat.totient 23) 4 := by
  rw [totient_23_eq]
  refine ⟨by omega, by omega, fun q hq hd => ?_⟩
  rw [fold_4_bound]
  have h22 : 22 = 2 * 11 := by norm_num
  rw [h22] at hd
  rcases hq.dvd_mul.mp hd with h2 | h11
  · have := Nat.le_of_dvd (by omega) h2; omega
  · have := Nat.le_of_dvd (by omega) h11; omega

/-- The 23-gon: 4-fold origami constructible, but NOT marked-ruler-constructible. -/
theorem ngon_23_4fold_not_neusis :
    IsKFoldConstructible (Nat.totient 23) 4 ∧ ¬ IsTwoThreeNumber (Nat.totient 23) :=
  ⟨ngon_23_4fold, ngon_23_not_neusis⟩

/-! ## Main Theorem -/

/-- Multi-fold origami is strictly more powerful than the marked ruler:
    the regular 11-gon is constructible with 2-fold origami but not with a marked ruler.

    Note: 1-fold origami = marked ruler = neusis, so this says 2-fold > 1-fold. -/
theorem multi_fold_strictly_stronger_than_neusis :
    ∃ n : ℕ, n ≥ 3 ∧
      (∃ k : ℕ, k ≥ 2 ∧ IsKFoldConstructible (Nat.totient n) k) ∧
      ¬ IsTwoThreeNumber (Nat.totient n) :=
  ⟨11, by omega, ⟨2, by omega, ngon_11_2fold⟩, ngon_11_not_neusis⟩

/-- For each k ≥ 2, there exists an n-gon constructible at fold level k but not marked-ruler.
    The 11-gon works for all k ≥ 2 (by monotonicity: 2-fold ⊆ k-fold for k ≥ 2). -/
theorem exists_ngon_at_each_level (k : ℕ) (hk : k ≥ 2) :
    ∃ n : ℕ, n ≥ 3 ∧
      IsKFoldConstructible (Nat.totient n) k ∧
      ¬ IsTwoThreeNumber (Nat.totient n) := by
  refine ⟨11, by omega, ?_, ngon_11_not_neusis⟩
  -- 11-gon is 2-fold; for k ≥ 2 apply constructible_mono (k-2) times
  have key : ∀ j : ℕ, IsKFoldConstructible (Nat.totient 11) (j + 2) := by
    intro j
    induction j with
    | zero => exact ngon_11_2fold
    | succ j ih => exact constructible_mono (by omega) ih
  rw [← Nat.sub_add_cancel hk]
  exact key (k - 2)

/-! ## Summary -/

-- Key results:
-- 1. not_twoThree_of_large_prime_dvd: general principle for non-neusis
-- 2. ngon_11_2fold_not_neusis: the 11-gon witnesses the gap
-- 3. ngon_23_4fold_not_neusis: the 23-gon witnesses a higher-level gap
-- 4. multi_fold_strictly_stronger_than_neusis: main theorem
-- 5. exists_ngon_at_each_level: for every fold level k ≥ 2, such an n-gon exists

#check @not_twoThree_of_large_prime_dvd
#check @ngon_11_2fold_not_neusis
#check @ngon_23_4fold_not_neusis
#check @multi_fold_strictly_stronger_than_neusis
#check @exists_ngon_at_each_level

end AngleTrisectionOQ04OQ04
