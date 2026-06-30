import Mathlib.Tactic
import Proofs.CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03

/-
# `gcd(n, m)` recovers the power map: kernel, image, and fibre partition

## What this proves

Fix a finite group of order `m` and the power map `x ↦ xⁿ`. The parent file
`CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03` showed that, in the **cyclic** case,
each non-empty fibre of this map has exactly `gcd(n, m)` elements. This file
makes precise the slogan suggested by that count:

> Structurally, the `n`-th power map is the **same map** as the `gcd(n, m)`-th
> power map.

"Same map" is made precise in three independent senses, and the count is then
assembled into the full fibre partition of the group.

* **Same kernel (any finite group).** `xⁿ = 1 ↔ x^(gcd(n,m)) = 1`, because the
  order of `x` always divides `m`, so it divides `n` iff it divides `gcd(n,m)`.
  As subgroups, `ker (x ↦ xⁿ) = ker (x ↦ x^(gcd(n,m)))`.
  (`pow_eq_one_iff_pow_gcd`, `ker_pow_eq_ker_pow_gcd`.)

* **Same image (cyclic).** The set of `n`-th powers equals the set of
  `gcd(n,m)`-th powers: `range (x ↦ xⁿ) = range (x ↦ x^(gcd(n,m)))`. The
  inclusion `⊆` is elementary (`gcd ∣ n`); equality follows because both
  subgroups have order `m / gcd(n,m)`.
  (`range_pow_eq_range_pow_gcd`.)

* **Uniform fibres + partition (cyclic).** Every fibre over an actual `n`-th
  power has exactly `gcd(n,m)` elements (`card_fiber_pow`), so the map partitions
  the group of order `m` into `m / gcd(n,m)` fibres of equal size `gcd(n,m)`:

  ```
  #(n-th powers) · gcd(n, m) = m,      #(n-th powers) = m / gcd(n, m).
  ```

  (`card_image_pow_mul_gcd`, `card_image_pow`.)

The kernel statement needs no commutativity; the image and partition statements
use the unique-subgroup-per-divisor structure of a cyclic group via the parent's
count.

## Proof strategy

The kernel statement reduces, through `orderOf_dvd_iff_pow_eq_one`, to the
arithmetic fact `o ∣ m → (o ∣ n ↔ o ∣ gcd(n,m))`. The image statement combines
the divisibility inclusion with `IsCyclic.card_powMonoidHom_range`, which
evaluates each range cardinality to `m / gcd(m, ·)`. The partition identity is a
single application of `Finset.card_eq_sum_card_image`, with each summand
collapsed to `gcd(n, m)` by the parent's `card_pow_eq_cyclic`.
-/

namespace CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02

open Finset

/-! ### Same kernel — the `n`-torsion is the `gcd(n,m)`-torsion -/

/-- **Element-level kernel recovery (any finite group).** Since `orderOf x`
divides the group order `m`, it divides `n` exactly when it divides
`gcd(n, m)`. Hence `xⁿ = 1` is equivalent to `x^(gcd(n,m)) = 1`: passing from
the exponent `n` to `gcd(n, m)` does not change the solution set of `xⁱ = 1`. -/
theorem pow_eq_one_iff_pow_gcd {α : Type*} [Group α] [Fintype α] {n : ℕ} (x : α) :
    x ^ n = 1 ↔ x ^ Nat.gcd n (Fintype.card α) = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    exact Nat.dvd_gcd h orderOf_dvd_card
  · intro h
    exact h.trans (Nat.gcd_dvd_left _ _)

/-- **`n`-torsion solution set is the `gcd(n,m)`-torsion solution set.** The
Finset reformulation of `pow_eq_one_iff_pow_gcd`. -/
theorem solutions_pow_one_eq_gcd {α : Type*} [Group α] [Fintype α] [DecidableEq α]
    (n : ℕ) :
    univ.filter (fun x : α => x ^ n = 1)
      = univ.filter (fun x : α => x ^ Nat.gcd n (Fintype.card α) = 1) := by
  ext x
  simp only [mem_filter, mem_univ, true_and]
  exact pow_eq_one_iff_pow_gcd x

/-- **Kernel recovery as subgroups.** In a finite commutative group the kernels
of the power homomorphisms `x ↦ xⁿ` and `x ↦ x^(gcd(n,m))` coincide. -/
theorem ker_pow_eq_ker_pow_gcd {α : Type*} [CommGroup α] [Fintype α] (n : ℕ) :
    (powMonoidHom n : α →* α).ker
      = (powMonoidHom (Nat.gcd n (Fintype.card α)) : α →* α).ker := by
  ext x
  simp only [MonoidHom.mem_ker, powMonoidHom_apply]
  exact pow_eq_one_iff_pow_gcd x

/-! ### Same image — the `n`-th powers are the `gcd(n,m)`-th powers -/

/-- **Image recovery (cyclic).** In a finite cyclic group the subgroup of `n`-th
powers equals the subgroup of `gcd(n,m)`-th powers. The inclusion `⊆` holds in
any commutative group because `gcd(n,m) ∣ n` makes every `n`-th power a
`gcd(n,m)`-th power; equality follows since both subgroups have the same
cardinality `m / gcd(n, m)`. -/
theorem range_pow_eq_range_pow_gcd {α : Type*} [CommGroup α] [Fintype α] [IsCyclic α]
    (n : ℕ) :
    (powMonoidHom n : α →* α).range
      = (powMonoidHom (Nat.gcd n (Fintype.card α)) : α →* α).range := by
  obtain ⟨n', hn'⟩ := Nat.gcd_dvd_left n (Fintype.card α)
  -- Inclusion `range (·ⁿ) ≤ range (·^gcd)`: `aⁿ = (a^n')^gcd`.
  have hle : (powMonoidHom n : α →* α).range
      ≤ (powMonoidHom (Nat.gcd n (Fintype.card α)) : α →* α).range := by
    rintro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    refine MonoidHom.mem_range.mpr ⟨a ^ n', ?_⟩
    simp only [powMonoidHom_apply]
    rw [← pow_mul, mul_comm, ← hn']
  -- The cardinalities agree, so the inclusion is an equality.
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  rw [IsCyclic.card_powMonoidHom_range, IsCyclic.card_powMonoidHom_range,
    Nat.card_eq_fintype_card]
  congr 1
  rw [Nat.gcd_comm n (Fintype.card α)]
  exact Nat.gcd_eq_right (Nat.gcd_dvd_left _ _)

/-! ### Uniform fibres and the partition of the group -/

/-- **Uniform fibre size (cyclic).** Every fibre of `x ↦ xⁿ` lying over an actual
`n`-th power `b` has exactly `gcd(n, m)` elements — the value is independent of
`b`. This is the parent's count `card_pow_eq_cyclic` read on the image. -/
theorem card_fiber_pow {α : Type*} [CommGroup α] [Fintype α] [DecidableEq α] [IsCyclic α]
    {n : ℕ} {b : α} (hb : ∃ a, a ^ n = b) :
    (univ.filter (fun x : α => x ^ n = b)).card = Nat.gcd n (Fintype.card α) := by
  rw [CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03.card_pow_eq_cyclic n b, if_pos hb]

/-- **Partition identity (cyclic).** The power map `x ↦ xⁿ` partitions the group
of order `m` into its fibres; the non-empty ones all have size `gcd(n, m)`, and
there are exactly as many as there are `n`-th powers. Counting the group two
ways gives `#(n-th powers) · gcd(n, m) = m`. -/
theorem card_image_pow_mul_gcd {α : Type*} [CommGroup α] [Fintype α] [DecidableEq α]
    [IsCyclic α] (n : ℕ) :
    (univ.image (fun x : α => x ^ n)).card * Nat.gcd n (Fintype.card α)
      = Fintype.card α := by
  have key : ∀ b ∈ univ.image (fun x : α => x ^ n),
      (univ.filter (fun a : α => a ^ n = b)).card = Nat.gcd n (Fintype.card α) := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨a, _, ha⟩ := hb
    exact card_fiber_pow ⟨a, ha⟩
  have hsum : Fintype.card α
      = ∑ b ∈ univ.image (fun x : α => x ^ n),
          (univ.filter (fun a : α => a ^ n = b)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_image _ _
  conv_rhs => rw [hsum]
  rw [Finset.sum_congr rfl key, Finset.sum_const, smul_eq_mul]

/-- **Number of `n`-th powers (cyclic).** Dividing the partition identity by the
common fibre size: a finite cyclic group of order `m` has exactly
`m / gcd(n, m)` distinct `n`-th powers. -/
theorem card_image_pow {α : Type*} [CommGroup α] [Fintype α] [DecidableEq α] [IsCyclic α]
    (n : ℕ) :
    (univ.image (fun x : α => x ^ n)).card
      = Fintype.card α / Nat.gcd n (Fintype.card α) := by
  have h := card_image_pow_mul_gcd (α := α) n
  have hpos : 0 < Nat.gcd n (Fintype.card α) :=
    Nat.gcd_pos_of_pos_right _ Fintype.card_pos
  exact (Nat.div_eq_of_eq_mul_right hpos (by rw [mul_comm]; exact h.symm)).symm

end CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02
