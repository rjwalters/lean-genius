import Mathlib.Tactic
import Proofs.CauchyGroupTheoremOQ01OQ01OQ01OQ01

/-
# Counting solutions of `xⁿ = g` for an arbitrary target `g`

## What this proves

The parent file `CauchyGroupTheoremOQ01OQ01OQ01OQ01` pins down the number of
solutions of `xⁿ = 1` in a finite **cyclic** group: it is exactly
`gcd(n, |G|)`. This file answers the natural follow-up question:

> For a *fixed* element `g` (not necessarily the identity), how many `x`
> satisfy `xⁿ = g`?

The answer splits cleanly into a **structural** part valid in every finite
**abelian** group, and an **explicit count** in the cyclic case.

* **Structural dichotomy (abelian).** In any finite abelian group the power map
  `x ↦ xⁿ` is a homomorphism, so the solution set of `xⁿ = g` is either empty
  (when `g` is not an `n`-th power) or a *coset* of the solution set of
  `xⁿ = 1`. Cosets have equal size, hence

  ```
  #{x | xⁿ = g} = #{x | xⁿ = 1}     if g is an n-th power
  #{x | xⁿ = g} = 0                 otherwise.
  ```

  (`card_pow_eq_eq_card_pow_one`, `card_pow_eq`.)

* **Explicit value (cyclic).** Feeding the parent's count `#{xⁿ = 1} =
  gcd(n, |G|)` into the dichotomy gives, in a finite cyclic group,

  ```
  #{x | xⁿ = g} = gcd(n, |G|)   if g is an n-th power, else 0.
  ```

  (`card_pow_eq_cyclic`.)

This is the sharp generalisation of the parent's `g = 1` count. It also makes
precise the abelian shadow of **Frobenius' theorem**: the number of solutions
of `xⁿ = g` is either `0` or a fixed value `gcd(n, |G|)` that does **not**
depend on which `n`-th power `g` is.

## Proof strategy

The whole content is one bijection. Fix a witness `a₀` with `a₀ⁿ = g`. In an
abelian group

```
x ↦ a₀⁻¹ · x
```

is a bijection from `{x | xⁿ = g}` to `{x | xⁿ = 1}` (with inverse
`y ↦ a₀ · y`), because `(a₀⁻¹·x)ⁿ = (a₀ⁿ)⁻¹·xⁿ = g⁻¹·g = 1` exactly when
`xⁿ = g`. Equal-size sets, so equal cardinalities. When `g` is not an `n`-th
power the solution set is empty by definition.
-/

namespace CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03

open Finset

variable {α : Type*} [CommGroup α]

/-- **Coset count.** In a finite abelian group, if `g` is an `n`-th power then
the equation `xⁿ = g` has exactly as many solutions as `xⁿ = 1`. The bijection
is left-translation by a fixed `n`-th root `a₀` of `g`. -/
theorem card_pow_eq_eq_card_pow_one [DecidableEq α] [Fintype α] {n : ℕ} {g : α}
    (hg : ∃ a, a ^ n = g) :
    (univ.filter (fun x => x ^ n = g)).card
      = (univ.filter (fun x : α => x ^ n = 1)).card := by
  obtain ⟨a₀, ha₀⟩ := hg
  -- The solution set of `xⁿ = g` is the left-translate by `a₀` of the solution
  -- set of `yⁿ = 1`; left translation is injective, so the cardinalities agree.
  have hset : (univ.filter (fun x => x ^ n = g))
      = (univ.filter (fun y : α => y ^ n = 1)).image (fun y => a₀ * y) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hx
      refine ⟨a₀⁻¹ * x, ?_, by rw [mul_inv_cancel_left]⟩
      rw [mul_pow, inv_pow, ha₀, hx, inv_mul_cancel]
    · rintro ⟨y, hy, rfl⟩
      rw [mul_pow, ha₀, hy, mul_one]
  rw [hset]
  exact Finset.card_image_of_injective _ (Equiv.mulLeft a₀).injective

/-- **Dichotomy.** In a finite abelian group the number of solutions of
`xⁿ = g` equals the number of solutions of `xⁿ = 1` when `g` is an `n`-th
power, and `0` otherwise. -/
theorem card_pow_eq [DecidableEq α] [Fintype α] (n : ℕ) (g : α) :
    (univ.filter (fun x => x ^ n = g)).card
      = if (∃ a, a ^ n = g) then (univ.filter (fun x : α => x ^ n = 1)).card else 0 := by
  by_cases h : ∃ a, a ^ n = g
  · rw [if_pos h, card_pow_eq_eq_card_pow_one h]
  · rw [if_neg h]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_false_of_mem
    intro x _ hx
    exact h ⟨x, hx⟩

/-- **Explicit count in a cyclic group.** Combining the dichotomy with the
parent's exact count `#{xⁿ = 1} = gcd(n, |G|)`, the number of solutions of
`xⁿ = g` in a finite cyclic group is `gcd(n, |G|)` when `g` is an `n`-th power
and `0` otherwise. In particular this value is independent of *which* `n`-th
power `g` is. -/
theorem card_pow_eq_cyclic [DecidableEq α] [Fintype α] [IsCyclic α] (n : ℕ) (g : α) :
    (univ.filter (fun x => x ^ n = g)).card
      = if (∃ a, a ^ n = g) then Nat.gcd n (Fintype.card α) else 0 := by
  rw [card_pow_eq]
  by_cases h : ∃ a, a ^ n = g
  · rw [if_pos h, if_pos h,
      CauchyGroupTheoremOQ01OQ01OQ01OQ01.card_pow_eq_one_eq_gcd]
  · rw [if_neg h, if_neg h]

/-- The identity `g = 1` is always an `n`-th power (`x = 1` works), so the
cyclic count specialises back to the parent's `gcd(n, |G|)`. This confirms the
new formula refines the old one. -/
theorem card_pow_eq_cyclic_one [DecidableEq α] [Fintype α] [IsCyclic α] (n : ℕ) :
    (univ.filter (fun x => x ^ n = (1 : α))).card = Nat.gcd n (Fintype.card α) := by
  rw [card_pow_eq_cyclic, if_pos ⟨1, one_pow n⟩]

/-- **Effective `n`-th power test (cyclic).** In a finite cyclic group of order
`m`, an element `g` is an `n`-th power **iff** `g ^ (m / gcd(n, m)) = 1`. The
`n`-th powers form the unique subgroup of order `m / gcd(n,m)`, namely the
`(m/gcd(n,m))`-torsion subgroup; membership in it is exactly this power test.
This turns the existential side condition of `card_pow_eq_cyclic` into a
decidable computation. -/
theorem isNthPower_iff [Fintype α] [IsCyclic α] {n : ℕ} {g : α} :
    (∃ a, a ^ n = g) ↔ g ^ (Fintype.card α / Nat.gcd n (Fintype.card α)) = 1 := by
  classical
  set m := Fintype.card α with hm
  set d := Nat.gcd n m with hd
  have hcardα : Nat.card α = m := by rw [hm, Nat.card_eq_fintype_card]
  have hmpos : 0 < m := Fintype.card_pos
  have hdm : d ∣ m := Nat.gcd_dvd_right n m
  have hdn : d ∣ n := Nat.gcd_dvd_left n m
  set k := m / d with hk
  have hkm : k ∣ m := Nat.div_dvd_of_dvd hdm
  -- The image of `x ↦ xⁿ` is contained in the `k`-torsion: every `n`-th power
  -- `aⁿ` satisfies `(aⁿ)ᵏ = a^(m·n') = 1`.
  have hle : (powMonoidHom n : α →* α).range ≤ (powMonoidHom k : α →* α).ker := by
    intro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    rw [MonoidHom.mem_ker]
    simp only [powMonoidHom_apply]
    rw [← pow_mul]
    obtain ⟨n', hn'⟩ := hdn
    have hnk : n * k = m * n' := by
      rw [hn', hk, mul_comm d n', mul_assoc, Nat.mul_div_cancel' hdm, mul_comm]
    exact orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_card.trans ⟨n', hnk⟩)
  -- Both subgroups have cardinality `k`, so the inclusion is an equality.
  have hcr : Nat.card (powMonoidHom n : α →* α).range = k := by
    rw [IsCyclic.card_powMonoidHom_range, hcardα, Nat.gcd_comm, ← hd, ← hk]
  have hck : Nat.card (powMonoidHom k : α →* α).ker = k := by
    rw [IsCyclic.card_powMonoidHom_ker, hcardα, Nat.gcd_eq_right hkm]
  have hrange_eq : (powMonoidHom n : α →* α).range = (powMonoidHom k : α →* α).ker :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq (by rw [hck, hcr]))
  -- Translate membership on both sides of the equality.
  constructor
  · rintro ⟨a, rfl⟩
    have hmem : a ^ n ∈ (powMonoidHom n : α →* α).range :=
      MonoidHom.mem_range.mpr ⟨a, powMonoidHom_apply n a⟩
    have := hle hmem
    rwa [MonoidHom.mem_ker, powMonoidHom_apply] at this
  · intro hgk
    have hmem : g ∈ (powMonoidHom k : α →* α).ker := by
      rw [MonoidHom.mem_ker, powMonoidHom_apply]; exact hgk
    rw [← hrange_eq] at hmem
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hmem
    exact ⟨a, by rw [← powMonoidHom_apply n a]; exact ha⟩

/-- **Fully effective count (cyclic).** Combining the explicit value with the
`n`-th power test: in a finite cyclic group of order `m`, the number of
solutions of `xⁿ = g` is `gcd(n, m)` when `g ^ (m / gcd(n,m)) = 1`, and `0`
otherwise — a condition that is directly checkable. -/
theorem card_pow_eq_cyclic_effective [DecidableEq α] [Fintype α] [IsCyclic α]
    (n : ℕ) (g : α) :
    (univ.filter (fun x => x ^ n = g)).card
      = if g ^ (Fintype.card α / Nat.gcd n (Fintype.card α)) = 1
        then Nat.gcd n (Fintype.card α) else 0 := by
  rw [card_pow_eq_cyclic]
  by_cases h : g ^ (Fintype.card α / Nat.gcd n (Fintype.card α)) = 1
  · rw [if_pos h, if_pos (isNthPower_iff.mpr h)]
  · rw [if_neg h, if_neg (fun hex => h (isNthPower_iff.mp hex))]

end CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03
