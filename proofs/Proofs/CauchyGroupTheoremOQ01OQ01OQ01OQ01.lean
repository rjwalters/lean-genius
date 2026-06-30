import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-
# Counting solutions to `xⁿ = 1` in a cyclic group: exactly `gcd(n, |G|)`

## What This Proves

For a finite **cyclic** group `G` and any exponent `n : ℕ`, the number of
solutions of the equation `xⁿ = 1` is **exactly** `gcd(n, |G|)`:

```
#{a : G | aⁿ = 1} = Nat.gcd n (Fintype.card G)
```

This is the sharp count. Mathlib only records the one-sided bound
`IsCyclic.card_pow_eq_one_le : #{a | aⁿ = 1} ≤ n` (for `0 < n`); the present
file pins down the value on the nose, for *every* `n` (including `n = 0`, where
both sides equal `|G|`).

## Why it matters: toward Frobenius' divisibility theorem

**Frobenius' theorem** states that in *any* finite group `G`, the number of
solutions of `xⁿ = 1` is divisible by `gcd(n, |G|)`. The cyclic case is the
base case and the extremal case: here the divisibility is an *equality*. The
corollary `frobenius_cyclic` records the divisibility statement that Frobenius
generalises to arbitrary groups, now established with the exact constant on the
cyclic fibre.

This also refines the parent file `CauchyGroupTheoremOQ01OQ01OQ01` (the
power-map dichotomy `x ↦ xⁿ` is a bijection iff `gcd(n,|G|) = 1`). That result
is the `gcd = 1` slice of the count: the power map is injective on a *cyclic*
group iff the only solution of `xⁿ = 1` is `1`, i.e. iff the count is `1`
(`pow_injective_iff_card_pow_eq_one_eq_one`).

## Proof strategy

Pick a generator `g` (so `orderOf g = |G| =: m`) and set `d := gcd(n, m)`,
`k := m / d`. The single subgroup `zpowers (g ^ k)` is exactly the solution
set:

* `orderOf (g ^ k) = m / gcd(m, k) = m / k = d`, using `k ∣ m`
  (`Nat.gcd_eq_right`, `Nat.div_div_self`).
* **`xⁿ = 1 ⟹ x ∈ zpowers (g ^ k)`.** Writing `x = gᵉ`, the relation
  `gᵉⁿ = 1` gives `m ∣ e·n`, and the elementary number theory lemma
  `div_gcd_dvd_of_dvd_mul` upgrades this to `k ∣ e` (the heart of the argument:
  `m = d·k`, `n = d·n'`, `gcd(k, n') = 1`, so `k ∣ e·n' ⟹ k ∣ e`). Hence
  `x = gᵉ ∈ zpowers (g ^ k)`.
* **`x ∈ zpowers (g ^ k) ⟹ xⁿ = 1`.** Then `orderOf x ∣ orderOf (g ^ k) = d ∣ n`
  (`orderOf_dvd_of_mem_zpowers`), so `xⁿ = 1`.

The cardinality of the solution set is therefore `|zpowers (g ^ k)| =
orderOf (g ^ k) = d = gcd(n, m)`.
-/

namespace CauchyGroupTheoremOQ01OQ01OQ01OQ01

open Finset Subgroup Submonoid Function

/-- **Number-theoretic core.** If `m ∣ e · n` then `m / gcd(n, m)` already
divides `e`. Equivalently: writing `d = gcd(n, m)`, `m = d·k` and `n = d·n'`
with `gcd(k, n') = 1`, the factor `k` of `m` that is coprime to `n` must come
entirely from `e`. This is the arithmetic engine behind the exact count. -/
theorem div_gcd_dvd_of_dvd_mul {n m e : ℕ} (hn : 0 < n) (h : m ∣ e * n) :
    m / Nat.gcd n m ∣ e := by
  set d := Nat.gcd n m with hd
  have hdpos : 0 < d :=
    Nat.pos_of_ne_zero fun h0 => hn.ne' (Nat.gcd_eq_zero_iff.mp h0).1
  have hdm : d ∣ m := Nat.gcd_dvd_right n m
  have hdn : d ∣ n := Nat.gcd_dvd_left n m
  -- `m = d * (m / d)` and `n = d * (n / d)`.
  have hmdk : d * (m / d) = m := Nat.mul_div_cancel' hdm
  have hndn : d * (n / d) = n := Nat.mul_div_cancel' hdn
  -- coprimality of the cofactors.
  have hcop : Nat.Coprime (m / d) (n / d) :=
    (Nat.coprime_div_gcd_div_gcd hdpos).symm
  -- From `m ∣ e * n`, cancel the common `d` to get `(m/d) ∣ e * (n/d)`.
  have key : d * (e * (n / d)) = e * n := by rw [mul_left_comm, hndn]
  have hmul : d * (m / d) ∣ d * (e * (n / d)) := by rw [hmdk, key]; exact h
  have hk_dvd : (m / d) ∣ e * (n / d) := Nat.dvd_of_mul_dvd_mul_left hdpos hmul
  -- `gcd(m/d, n/d) = 1` lets us drop the `n/d` factor.
  exact hcop.dvd_of_dvd_mul_right hk_dvd

variable {α : Type*} [Group α]

/-- **Main theorem.** In a finite cyclic group, the number of solutions of
`xⁿ = 1` is exactly `gcd(n, |G|)`. Holds for every `n`, including `n = 0`
(both sides are `|G|`). -/
theorem card_pow_eq_one_eq_gcd [DecidableEq α] [Fintype α] [IsCyclic α] (n : ℕ) :
    (univ.filter (fun a : α => a ^ n = 1)).card = Nat.gcd n (Fintype.card α) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: every element solves `x⁰ = 1`, and `gcd(0, m) = m`.
    subst hn
    have huniv : (univ.filter (fun a : α => a ^ 0 = 1)) = univ := by
      ext a; simp
    rw [huniv, card_univ, Nat.gcd_zero_left]
  -- Fix a generator and the relevant quantities.
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := α)
  set m := Fintype.card α with hm
  have hmpos : 0 < m := Fintype.card_pos
  have hgo : orderOf g = m := by
    rw [hm, ← Nat.card_eq_fintype_card]
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  set d := Nat.gcd n m with hd
  have hdpos : 0 < d :=
    Nat.pos_of_ne_zero fun h0 => hn.ne' (Nat.gcd_eq_zero_iff.mp h0).1
  have hdm : d ∣ m := Nat.gcd_dvd_right n m
  have hdn : d ∣ n := Nat.gcd_dvd_left n m
  set k := m / d with hk
  have hkm : k ∣ m := Nat.div_dvd_of_dvd hdm
  -- The order of `g ^ k` is exactly `d`.
  have hgk_order : orderOf (g ^ k) = d := by
    rw [orderOf_pow, hgo, Nat.gcd_eq_right hkm, hk, Nat.div_div_self hdm hmpos.ne']
  -- The solution set is exactly the subgroup `zpowers (g ^ k)`.
  have hset : (univ.filter (fun a : α => a ^ n = 1))
      = (zpowers (g ^ k) : Set α).toFinset := by
    ext a
    simp only [mem_filter, mem_univ, true_and, Set.mem_toFinset, SetLike.mem_coe]
    constructor
    · intro ha
      -- `a = g ^ e` for some `e`.
      obtain ⟨e, he⟩ := (mem_powers_iff a g).mp (mem_powers_iff_mem_zpowers.mpr (hg a))
      -- `m ∣ e * n`.
      have hpow : g ^ (e * n) = 1 := by rw [pow_mul, he]; exact ha
      have hmen : m ∣ e * n := by rw [← hgo]; exact orderOf_dvd_iff_pow_eq_one.mpr hpow
      -- hence `k = m / d ∣ e`.
      have hke : k ∣ e := by rw [hk, hd]; exact div_gcd_dvd_of_dvd_mul hn hmen
      obtain ⟨t, ht⟩ := hke
      exact mem_zpowers_iff.mpr ⟨(t : ℤ), by rw [zpow_natCast, ← pow_mul, ← ht, he]⟩
    · intro ha
      -- `orderOf a ∣ orderOf (g ^ k) = d ∣ n`, so `a ^ n = 1`.
      have h1 : orderOf a ∣ d := by
        have := orderOf_dvd_of_mem_zpowers ha
        rwa [hgk_order] at this
      exact orderOf_dvd_iff_pow_eq_one.mp (h1.trans hdn)
  -- Conclude by counting the subgroup.
  rw [hset]
  simp only [Set.toFinset_card, SetLike.coe_sort_coe]
  rw [Fintype.card_zpowers, hgk_order]

/-- **Frobenius' divisibility, cyclic case.** `gcd(n, |G|)` divides the number
of solutions of `xⁿ = 1` — here, with equality. This is the statement Frobenius'
theorem generalises to arbitrary finite groups. -/
theorem frobenius_cyclic [DecidableEq α] [Fintype α] [IsCyclic α] (n : ℕ) :
    Nat.gcd n (Fintype.card α) ∣ (univ.filter (fun a : α => a ^ n = 1)).card := by
  rw [card_pow_eq_one_eq_gcd]

/-- The solution set is a singleton (only the identity) iff `n` is coprime to
`|G|`. This is the cyclic incarnation of the power-map dichotomy of the parent
file: `x ↦ xⁿ` is injective iff the only `n`-th root of unity is `1`. -/
theorem card_pow_eq_one_eq_one_iff_coprime [DecidableEq α] [Fintype α] [IsCyclic α]
    (n : ℕ) :
    (univ.filter (fun a : α => a ^ n = 1)).card = 1 ↔ n.Coprime (Fintype.card α) := by
  rw [card_pow_eq_one_eq_gcd]

/-- When the exponent is a multiple of `|G|`, every element is a solution: the
count is the whole group. -/
theorem card_pow_eq_one_eq_card_of_card_dvd [DecidableEq α] [Fintype α] [IsCyclic α]
    {n : ℕ} (h : Fintype.card α ∣ n) :
    (univ.filter (fun a : α => a ^ n = 1)).card = Fintype.card α := by
  rw [card_pow_eq_one_eq_gcd, Nat.gcd_eq_right h]

end CauchyGroupTheoremOQ01OQ01OQ01OQ01
