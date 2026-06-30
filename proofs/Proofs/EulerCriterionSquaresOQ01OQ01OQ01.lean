/-
  Counting `k`-th power residues mod a prime: for `k ∣ p − 1`, an odd prime
  `p` has exactly `(p − 1)/k` nonzero `k`-th power residues in `ZMod p`.

  This generalizes the quadratic count of `EulerCriterionSquaresOQ01OQ01`
  (the case `k = 2`, giving `(p − 1)/2`) to arbitrary exponents `k` dividing
  `p − 1`.

  The mechanism is the `k`-th power endomorphism `u ↦ u^k` of the *cyclic*
  unit group `(ZMod p)ˣ`.  Because `(ZMod p)ˣ` is cyclic of order `p − 1`,
  Mathlib's `IsCyclic.card_powMonoidHom_ker` / `card_powMonoidHom_range` give

      |ker (·^k)| = gcd(p − 1, k),     |image (·^k)| = (p − 1)/gcd(p − 1, k).

  When `k ∣ p − 1` we have `gcd(p − 1, k) = k`, so the kernel has size exactly
  `k` (the `k`-th roots of unity) and the image — the nonzero `k`-th power
  residues — has size exactly `(p − 1)/k`.  Translating "lies in the image of
  the unit power map" to "is a nonzero `k`-th power in `ZMod p`" gives the
  residue count.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open ZMod

namespace EulerCriterionSquaresOQ01OQ01OQ01

variable (p k : ℕ) [Fact p.Prime] [Fact (2 < p)]

omit [Fact (2 < p)] in
/-- The order of the unit group `(ZMod p)ˣ` is `p − 1`. -/
theorem card_units_eq : Nat.card (ZMod p)ˣ = p - 1 := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units]

omit [Fact p.Prime] [Fact (2 < p)] in
/-- For `k ∣ p − 1`, the gcd of `p − 1` and `k` is `k`. -/
theorem gcd_eq (hk : k ∣ p - 1) : (p - 1).gcd k = k := by
  rw [Nat.gcd_comm]; exact Nat.gcd_eq_left hk

/-- **Kernel count.** For `k ∣ p − 1`, the kernel of the `k`-th power map on
`(ZMod p)ˣ` — the `k`-th roots of unity — has cardinality exactly `k`.  This is
`gcd(p − 1, k) = k`. -/
theorem card_kHom_ker (hk : k ∣ p - 1) :
    Nat.card (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).ker = k := by
  rw [IsCyclic.card_powMonoidHom_ker, card_units_eq, gcd_eq p k hk]

/-- **Image count (units form).** For `k ∣ p − 1`, the image of the `k`-th
power map on `(ZMod p)ˣ` — the `k`-th power residues among the units — has
cardinality `(p − 1)/k`. -/
theorem card_kHom_range (hk : k ∣ p - 1) :
    Nat.card (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range = (p - 1) / k := by
  rw [IsCyclic.card_powMonoidHom_range, card_units_eq, gcd_eq p k hk]

omit [Fact (2 < p)] in
/-- A nonzero residue characterisation: for a unit `u`, the field element `↑u`
is a `k`-th power in `ZMod p` iff `u` lies in the image of the unit `k`-th
power map. -/
theorem isKthPower_coe_iff_mem_range (hk0 : k ≠ 0) {u : (ZMod p)ˣ} :
    (∃ x : ZMod p, x ^ k = (↑u : ZMod p)) ↔
      u ∈ (powMonoidHom k : (ZMod p)ˣ →* (ZMod p)ˣ).range := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hk0] at hr
      exact u.ne_zero hr.symm
    obtain ⟨w, rfl⟩ := isUnit_iff_ne_zero.mpr hr0
    refine ⟨w, ?_⟩
    apply Units.ext
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val]
    exact hr
  · rintro ⟨v, rfl⟩
    exact ⟨↑v, by rw [powMonoidHom_apply, Units.val_pow_eq_pow_val]⟩

/-- **`k`-th power residue count.** For `k ∣ p − 1`, an odd prime `p` has
exactly `(p − 1)/k` nonzero `k`-th power residues in `ZMod p`. -/
theorem card_nonzero_kth_power_residues (hk : k ∣ p - 1) :
    Nat.card {a : ZMod p // a ≠ 0 ∧ ∃ x : ZMod p, x ^ k = a} = (p - 1) / k := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [Nat.zero_dvd] at hk
    have : 2 < p := Fact.out
    omega
  rw [← card_kHom_range p k hk]
  refine Nat.card_congr (Equiv.symm ?_)
  refine (Equiv.subtypeEquivRight
    (fun u => (isKthPower_coe_iff_mem_range p k hk0).symm)).trans ?_
  refine (@Equiv.subtypeEquiv (ZMod p)ˣ {a : ZMod p // a ≠ 0}
      (fun u => ∃ x : ZMod p, x ^ k = (↑u : ZMod p))
      (fun x => ∃ y : ZMod p, y ^ k = (x : ZMod p))
      unitsEquivNeZero (fun u => Iff.rfl)).trans ?_
  exact Equiv.subtypeSubtypeEquivSubtypeInter
    (· ≠ (0 : ZMod p)) (fun a => ∃ x : ZMod p, x ^ k = a)

/-- The quadratic count of `EulerCriterionSquaresOQ01OQ01` recovered as the
case `k = 2`: an odd prime has `(p − 1)/2` nonzero quadratic residues.  Here a
nonzero quadratic residue is presented as `∃ x, x² = a`. -/
theorem card_nonzero_quadratic_residues :
    Nat.card {a : ZMod p // a ≠ 0 ∧ ∃ x : ZMod p, x ^ 2 = a} = (p - 1) / 2 := by
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by have : 2 < p := Fact.out; omega)
  obtain ⟨m, hm⟩ := hodd
  have h2 : (2 : ℕ) ∣ p - 1 := ⟨m, by omega⟩
  exact card_nonzero_kth_power_residues p 2 h2

/-! ### Concrete check: cubic residues modulo 7 -/

/-- Mod `7` there are `(7−1)/3 = 2` nonzero cubic residues, namely `{1, 6}`
(the cubes `1³, 3³` modulo `7`). -/
theorem card_cubic_residues_mod_seven :
    Nat.card {a : ZMod 7 // a ≠ 0 ∧ ∃ x : ZMod 7, x ^ 3 = a} = 2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Fact (2 < 7) := ⟨by norm_num⟩
  exact card_nonzero_kth_power_residues 7 3 (by norm_num)

end EulerCriterionSquaresOQ01OQ01OQ01
