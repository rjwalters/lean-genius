import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# Counting the solutions of `xⁿ = 1` in a finite cyclic group

## What this proves

For a finite cyclic group `G` of order `m = Nat.card G` and an exponent `n : ℕ`, the
number of solutions of the equation `xⁿ = 1` is *exactly* the greatest common divisor:

```
Nat.card {x : G // x ^ n = 1} = Nat.gcd n (Nat.card G).
```

This is the quantitative refinement of the parent file
`CauchyGroupTheoremOQ01OQ01OQ01`, which proves the qualitative *dichotomy* `x ↦ xⁿ` is a
bijection iff `gcd(n, |G|) = 1`.  Bijectivity is the special case where the solution set
of `xⁿ = 1` is the single point `{1}` (count `= 1`); here we pin down the count for every
`n`.

## Why it matters: the cyclic case of Frobenius's theorem

**Frobenius's theorem (1895)** states that for *any* finite group `G` and any `n`, the
number `#{x : xⁿ = 1}` is divisible by `gcd(n, |G|)`.  The proof for general groups is
deep.  The cyclic case proved here is the *sharp* base case: the divisibility is an
**equality**, `#{x : xⁿ = 1} = gcd(n, |G|)`.  Every step towards the general Frobenius
theorem has to reproduce this cyclic computation, so it is the natural first milestone.

## What is genuinely new here vs. Mathlib

Mathlib already proves `IsCyclic.card_powMonoidHom_ker`, which computes the cardinality of
the *kernel subgroup* of the `n`-th power map as `(Nat.card G).gcd n`.  We

* re-package that as the count of the solution **set** `{x // xⁿ = 1}`
  (`card_pow_eq_one_eq_gcd`), the form used in the statement of Frobenius's theorem;
* derive the structural consequences that are **not** in Mathlib:
  - the count always divides `|G|` (`card_pow_eq_one_dvd_card`);
  - `xⁿ = 1` holds for *all* `x` iff `|G| ∣ n` (`card_pow_eq_one_eq_card_iff`);
  - every divisor `d ∣ |G|` is realised exactly: `#{x : x^d = 1} = d`
    (`card_pow_eq_one_of_dvd_card`);
  - the solution counts are *monotone* under divisibility of exponents
    (`card_pow_eq_one_dvd_of_dvd`);
  - **the sharp characterisation** of the image: a number `v` arises as some solution
    count iff `v ∣ |G|` (`exists_card_pow_eq_one_iff_dvd`);
  - the Frobenius divisibility, here with equality (`gcd_dvd_card_pow_eq_one`).

All results are fully machine-checked with no `sorry` and no extra axioms (the concrete
examples use kernel `decide` on `Nat.gcd`, never `native_decide`).

Since every cyclic group is abelian we work over `[CommGroup G] [IsCyclic G]`; this is the
natural setting (and `powMonoidHom` requires commutativity) with no loss of generality.
-/

namespace CauchyGroupTheoremOQ01OQ01OQ01OQ01

open Function

variable {G : Type*}

/-! ### A general inclusion (any monoid)

If `a ∣ b`, every solution of `xᵃ = 1` is a solution of `xᵇ = 1`.  This holds in an
arbitrary monoid and underlies the monotonicity of the solution counts below. -/

/-- If `a ∣ b` then `xᵃ = 1` implies `xᵇ = 1`.  (True in any monoid.) -/
theorem pow_eq_one_of_dvd [Monoid G] {a b : ℕ} (h : a ∣ b) {x : G}
    (hx : x ^ a = 1) : x ^ b = 1 := by
  obtain ⟨c, rfl⟩ := h
  rw [pow_mul, hx, one_pow]

/-! ### The headline count -/

variable [CommGroup G] [IsCyclic G] [Finite G]

/-- **The solution count is the gcd.** In a finite cyclic group of order `|G|`, the
equation `xⁿ = 1` has exactly `gcd(n, |G|)` solutions.

This re-packages Mathlib's `IsCyclic.card_powMonoidHom_ker` (the cardinality of the kernel
of the `n`-th power homomorphism) as the count of the solution set, the shape in which the
statement of Frobenius's theorem is usually given. -/
theorem card_pow_eq_one_eq_gcd (n : ℕ) :
    Nat.card {x : G // x ^ n = 1} = Nat.gcd n (Nat.card G) := by
  have e : {x : G // x ^ n = 1} ≃ (powMonoidHom n : G →* G).ker :=
    Equiv.subtypeEquivRight fun x => by rw [MonoidHom.mem_ker, powMonoidHom_apply]
  rw [Nat.card_congr e, IsCyclic.card_powMonoidHom_ker, Nat.gcd_comm]

/-- The number of solutions of `xⁿ = 1` divides the order of the group: the solution set
is a subgroup (the kernel of the power map), so this is Lagrange's theorem made
quantitative. -/
theorem card_pow_eq_one_dvd_card (n : ℕ) :
    Nat.card {x : G // x ^ n = 1} ∣ Nat.card G := by
  rw [card_pow_eq_one_eq_gcd]
  exact Nat.gcd_dvd_right n (Nat.card G)

/-- **Frobenius divisibility, cyclic case.** `gcd(n, |G|)` divides the number of solutions
of `xⁿ = 1` — and, for cyclic groups, this divisibility is in fact an equality
(`card_pow_eq_one_eq_gcd`).  Frobenius's theorem extends the divisibility (not the
equality) to all finite groups. -/
theorem gcd_dvd_card_pow_eq_one (n : ℕ) :
    Nat.gcd n (Nat.card G) ∣ Nat.card {x : G // x ^ n = 1} := by
  rw [card_pow_eq_one_eq_gcd]

/-- Every `x` satisfies `xⁿ = 1` iff the order of the group divides `n`. Equivalently, the
solution count equals `|G|` exactly when `n` is a multiple of the group's exponent
(`= |G|` for cyclic groups). -/
theorem card_pow_eq_one_eq_card_iff (n : ℕ) :
    Nat.card {x : G // x ^ n = 1} = Nat.card G ↔ Nat.card G ∣ n := by
  rw [card_pow_eq_one_eq_gcd]
  constructor
  · intro h
    rw [← h]
    exact Nat.gcd_dvd_left n (Nat.card G)
  · intro h
    rw [Nat.gcd_comm]
    exact Nat.gcd_eq_left h

/-- **Every divisor is realised exactly.** If `d ∣ |G|`, then `xᵈ = 1` has exactly `d`
solutions.  In particular taking `d = |G|` recovers "every element is `|G|`-torsion", and
`d = 1` recovers "only `1` is a fixed point of `x ↦ x`". -/
theorem card_pow_eq_one_of_dvd_card {d : ℕ} (hd : d ∣ Nat.card G) :
    Nat.card {x : G // x ^ d = 1} = d := by
  rw [card_pow_eq_one_eq_gcd, Nat.gcd_eq_left hd]

/-- **Monotonicity under divisibility of exponents.** If `a ∣ b`, the count of solutions
of `xᵃ = 1` divides the count of solutions of `xᵇ = 1`.  (The solution *sets* nest by
`pow_eq_one_of_dvd`; on counts this becomes divisibility.) -/
theorem card_pow_eq_one_dvd_of_dvd {a b : ℕ} (h : a ∣ b) :
    Nat.card {x : G // x ^ a = 1} ∣ Nat.card {x : G // x ^ b = 1} := by
  rw [card_pow_eq_one_eq_gcd, card_pow_eq_one_eq_gcd]
  exact Nat.dvd_gcd ((Nat.gcd_dvd_left a _).trans h) (Nat.gcd_dvd_right a _)

/-- **Sharp characterisation of the possible solution counts.** A natural number `v` occurs
as the number of solutions of `xⁿ = 1` for some exponent `n` **iff** `v` divides `|G|`.
Thus the image of `n ↦ #{x : xⁿ = 1}` is exactly the set of divisors of `|G|`. -/
theorem exists_card_pow_eq_one_iff_dvd (v : ℕ) :
    (∃ n, Nat.card {x : G // x ^ n = 1} = v) ↔ v ∣ Nat.card G := by
  constructor
  · rintro ⟨n, rfl⟩
    exact card_pow_eq_one_dvd_card n
  · intro hv
    exact ⟨v, card_pow_eq_one_of_dvd_card hv⟩

/-! ### Concrete instances on `Multiplicative (ZMod 12)` (a cyclic group of order 12) -/

/-- The cyclic group `Multiplicative (ZMod 12)` has order `12`. -/
theorem card_mul_zmod12 : Nat.card (Multiplicative (ZMod 12)) = 12 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

/-- On the order-`12` cyclic group, `x⁸ = 1` has exactly `gcd(8, 12) = 4` solutions. -/
theorem card_pow8_mul_zmod12 :
    Nat.card {x : Multiplicative (ZMod 12) // x ^ 8 = 1} = 4 := by
  rw [card_pow_eq_one_eq_gcd, card_mul_zmod12]
  decide

/-- On the order-`12` cyclic group, `x⁵ = 1` has exactly `gcd(5, 12) = 1` solution (only
the identity): the fifth-power map is a bijection, recovering the parent dichotomy. -/
theorem card_pow5_mul_zmod12 :
    Nat.card {x : Multiplicative (ZMod 12) // x ^ 5 = 1} = 1 := by
  rw [card_pow_eq_one_eq_gcd, card_mul_zmod12]
  decide

/-- On the order-`12` cyclic group, `x⁶ = 1` has exactly `gcd(6, 12) = 6` solutions, since
`6 ∣ 12`: a divisor is realised exactly. -/
theorem card_pow6_mul_zmod12 :
    Nat.card {x : Multiplicative (ZMod 12) // x ^ 6 = 1} = 6 := by
  rw [card_pow_eq_one_eq_gcd, card_mul_zmod12]
  decide

end CauchyGroupTheoremOQ01OQ01OQ01OQ01
