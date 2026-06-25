import Mathlib.Tactic
import Proofs.CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02

/-
# The power map over an arbitrary finite abelian group: `gcd(n, exp G)` form

## What this proves

Fix a finite group and the power map `x ↦ xⁿ`.  The parent file
`CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02` analysed this map in a **cyclic**
group of order `m`, where the kernel, image and fibres are all governed by
`gcd(n, m)`.  This file removes the cyclicity assumption: over **any** finite
abelian group the same map is structurally the `gcd(n, exp G)`-th power map,
where `exp G = Monoid.exponent G` is the group exponent (the lcm of the element
orders).  The order `m` is replaced by the exponent because the exponent — not
the order — is the modulus that controls `xⁱ = 1` uniformly across all elements:
`orderOf x ∣ exp G` for every `x`.

* **Same kernel (any finite group).** `xⁿ = 1 ↔ x^(gcd(n, exp G)) = 1`, because
  `orderOf x ∣ exp G`, so it divides `n` iff it divides `gcd(n, exp G)`.  As
  subgroups, `ker (x ↦ xⁿ) = ker (x ↦ x^(gcd(n, exp G)))`.
  (`pow_eq_one_iff_pow_gcd_exponent`, `ker_pow_eq_ker_pow_gcd_exponent`.)

* **Same image (any finite abelian group).** `range (x ↦ xⁿ) =
  range (x ↦ x^(gcd(n, exp G)))`.  The inclusion `⊆` is elementary
  (`gcd ∣ n`); equality follows from the first isomorphism theorem, since equal
  kernels give equal-cardinality images.  No cyclicity is needed — this is the
  genuine generalisation of the parent's `range_pow_eq_range_pow_gcd`, which
  relied on the unique-subgroup-per-divisor structure of a cyclic group.
  (`range_pow_eq_range_pow_gcd_exponent`.)

* **Constant-fibre partition (any finite abelian group).** The power map is a
  group homomorphism, so its non-empty fibres are the cosets of the kernel and
  all have the same size `|ker(x ↦ xⁿ)|`.  Counting the group as a disjoint union
  of fibres gives `#(n-th powers) · |ker(x ↦ xⁿ)| = |G|`, hence
  `#(n-th powers) = |G| / |ker(x ↦ xⁿ)|`.
  (`card_range_pow_mul_card_ker`, `card_range_pow`.)

  In the cyclic case `|ker(x ↦ xⁿ)| = gcd(n, m)`, recovering the parent's count;
  in general the fibre size is the `n`-torsion count, which is `gcd(n, exp G)`
  only when the group is cyclic.

## Proof strategy

The kernel statement reduces, through `orderOf_dvd_iff_pow_eq_one`, to the
arithmetic fact `o ∣ exp G → (o ∣ n ↔ o ∣ gcd(n, exp G))`, using
`Monoid.order_dvd_exponent`.  The image statement combines the divisibility
inclusion with Noether's first isomorphism theorem
`QuotientGroup.quotientKerEquivRange`: equal kernels give equal quotients, hence
equal-cardinality ranges, and an inclusion of equal-cardinality subgroups is an
equality (`Subgroup.eq_of_le_of_card_ge`).  The partition identity is Lagrange's
theorem `Subgroup.card_eq_card_quotient_mul_card_subgroup` applied to the kernel,
with the quotient re-identified with the range by the same isomorphism.
-/

namespace CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02OQ01

open Finset

/-! ### Same kernel — the `n`-torsion is the `gcd(n, exp G)`-torsion -/

/-- **Element-level kernel recovery (any finite group).** Since `orderOf x`
divides the exponent `exp G`, it divides `n` exactly when it divides
`gcd(n, exp G)`.  Hence `xⁿ = 1` is equivalent to `x^(gcd(n, exp G)) = 1`. -/
theorem pow_eq_one_iff_pow_gcd_exponent {α : Type*} [Group α] {n : ℕ} (x : α) :
    x ^ n = 1 ↔ x ^ Nat.gcd n (Monoid.exponent α) = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    exact Nat.dvd_gcd h (Monoid.order_dvd_exponent x)
  · intro h
    exact h.trans (Nat.gcd_dvd_left _ _)

/-- **Kernel recovery as subgroups.** In a finite commutative group the kernels
of the power homomorphisms `x ↦ xⁿ` and `x ↦ x^(gcd(n, exp G))` coincide. -/
theorem ker_pow_eq_ker_pow_gcd_exponent {α : Type*} [CommGroup α] (n : ℕ) :
    (powMonoidHom n : α →* α).ker
      = (powMonoidHom (Nat.gcd n (Monoid.exponent α)) : α →* α).ker := by
  ext x
  simp only [MonoidHom.mem_ker, powMonoidHom_apply]
  exact pow_eq_one_iff_pow_gcd_exponent x

/-! ### Same image — the `n`-th powers are the `gcd(n, exp G)`-th powers -/

/-- **Image recovery (any finite abelian group).** The subgroup of `n`-th powers
equals the subgroup of `gcd(n, exp G)`-th powers.  The inclusion `⊆` holds
because `gcd(n, exp G) ∣ n` makes every `n`-th power a `gcd(n, exp G)`-th power;
equality follows from the first isomorphism theorem, as the equal kernels force
the two images to have the same cardinality.  Unlike the parent's cyclic proof,
this uses no special subgroup structure — only that the power map is a
homomorphism. -/
theorem range_pow_eq_range_pow_gcd_exponent {α : Type*} [CommGroup α] [Finite α]
    (n : ℕ) :
    (powMonoidHom n : α →* α).range
      = (powMonoidHom (Nat.gcd n (Monoid.exponent α)) : α →* α).range := by
  obtain ⟨n', hn'⟩ := Nat.gcd_dvd_left n (Monoid.exponent α)
  -- Inclusion `range (·ⁿ) ≤ range (·^gcd)`: `aⁿ = (a^n')^gcd`.
  have hle : (powMonoidHom n : α →* α).range
      ≤ (powMonoidHom (Nat.gcd n (Monoid.exponent α)) : α →* α).range := by
    rintro x hx
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hx
    refine MonoidHom.mem_range.mpr ⟨a ^ n', ?_⟩
    simp only [powMonoidHom_apply]
    rw [← pow_mul, mul_comm, ← hn']
  -- Equal kernels ⟹ equal-cardinality ranges (first isomorphism theorem).
  refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
  have hker : (powMonoidHom n : α →* α).ker
      = (powMonoidHom (Nat.gcd n (Monoid.exponent α)) : α →* α).ker :=
    ker_pow_eq_ker_pow_gcd_exponent n
  have e1 := QuotientGroup.quotientKerEquivRange (powMonoidHom n : α →* α)
  have e2 := QuotientGroup.quotientKerEquivRange
    (powMonoidHom (Nat.gcd n (Monoid.exponent α)) : α →* α)
  rw [← Nat.card_congr e1.toEquiv, ← Nat.card_congr e2.toEquiv, hker]

/-! ### Constant-fibre partition and the number of `n`-th powers -/

/-- **Partition identity (any finite abelian group).** The power map `x ↦ xⁿ` is a
homomorphism, so the group is partitioned into the cosets of its kernel: the
non-empty fibres all have size `|ker(x ↦ xⁿ)|`, and there are exactly
`#(n-th powers)` of them.  Counting two ways (Lagrange + the first isomorphism
theorem) gives `#(n-th powers) · |ker(x ↦ xⁿ)| = |G|`. -/
theorem card_range_pow_mul_card_ker {α : Type*} [CommGroup α] [Finite α] (n : ℕ) :
    Nat.card (powMonoidHom n : α →* α).range * Nat.card (powMonoidHom n : α →* α).ker
      = Nat.card α := by
  have e := QuotientGroup.quotientKerEquivRange (powMonoidHom n : α →* α)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (powMonoidHom n : α →* α).ker,
    Nat.card_congr e.toEquiv]

/-- **Number of `n`-th powers (any finite abelian group).** Dividing the partition
identity by the common fibre size: a finite abelian group has exactly
`|G| / |ker(x ↦ xⁿ)|` distinct `n`-th powers.  In the cyclic case
`|ker(x ↦ xⁿ)| = gcd(n, |G|)`, recovering the parent's `|G| / gcd(n, |G|)`. -/
theorem card_range_pow {α : Type*} [CommGroup α] [Finite α] (n : ℕ) :
    Nat.card (powMonoidHom n : α →* α).range
      = Nat.card α / Nat.card (powMonoidHom n : α →* α).ker := by
  have h := card_range_pow_mul_card_ker (α := α) n
  have hpos : 0 < Nat.card (powMonoidHom n : α →* α).ker := Nat.card_pos
  exact (Nat.div_eq_of_eq_mul_left hpos h.symm).symm

end CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02OQ01

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02OQ01.ker_pow_eq_ker_pow_gcd_exponent
#print axioms CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02OQ01.range_pow_eq_range_pow_gcd_exponent
#print axioms CauchyGroupTheoremOQ01OQ01OQ01OQ01OQ03OQ02OQ01.card_range_pow_mul_card_ker
