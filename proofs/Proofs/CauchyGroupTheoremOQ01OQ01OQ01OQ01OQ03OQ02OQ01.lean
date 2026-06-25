import Mathlib.Tactic

/-
# Power map over a general group: the exponent governs kernel *and* image

The parent entry (`gcd(n,m)` recovers the power map) established, for a finite
group of order `m`:

* **kernel**, in any finite group: `xⁿ = 1 ↔ x^(gcd(n,m)) = 1`;
* **image**, only in the *cyclic* case: the `n`-th powers are the
  `gcd(n,m)`-th powers.

It left open (parent open question 1) the image equality for a *general finite
abelian* group, noting that the cyclic proof used the group order `m` and the
counting identity `#range · #ker = m`, neither of which behaves the same once
the group is a nontrivial product of cyclic factors.

This file answers that question — and overshoots it. The right invariant is not
the order `m = |G|` but the **exponent** `e = exp G`. Against the exponent the
image equality

      range (x ↦ xⁿ)  =  range (x ↦ x^(gcd(n, e)))

holds **in every group** (no commutativity, no finiteness needed), because the
hard inclusion is a single Bézout identity: writing
`gcd(n, e) = n·A + e·B` over `ℤ` and using `x^e = 1`, every `gcd(n,e)`-th power
`x^(gcd(n,e)) = (x^A)ⁿ` is already an `n`-th power.

For a finite **abelian** group this recovers exactly the structural picture the
parent asked for:

* the power map `x ↦ xⁿ` is a homomorphism whose kernel is the
  `gcd(n, e)`-torsion subgroup (constant fibre size `#ker`), and
* the partition identity becomes `#range · #ker = |G|` — first-isomorphism
  bookkeeping that holds verbatim for every finite abelian group, with the
  cyclic identity `#(n-th powers) · gcd(n, m) = m` the special case where
  `#ker = gcd(n, m)`.

Everything is over `Mathlib.Tactic` only; `Monoid.exponent` is the sole new
ingredient relative to the parent.
-/

variable {α : Type*}

/-! ### A `ℤ`-power form of `x ^ exponent = 1` -/

/-- `x` raised to the (integer-cast) exponent is the identity, in any monoid.
This is the `zpow` companion of `Monoid.pow_exponent_eq_one`, packaged for the
Bézout computation below. -/
theorem zpow_exponent_eq_one [Group α] (x : α) :
    x ^ (Monoid.exponent α : ℤ) = 1 := by
  rw [zpow_natCast]
  exact Monoid.pow_exponent_eq_one x

/-! ### Kernel: the `n`-torsion is the `gcd(n, exp)`-torsion (any group) -/

/-- **Element-level kernel recovery against the exponent (any group).**
`orderOf x` divides the exponent, so `xⁿ = 1` (i.e. `orderOf x ∣ n`) is
unchanged by replacing `n` with `gcd(n, exp G)`. This is the parent's
`pow_eq_one_iff_pow_gcd` with the *exponent* in place of the order, and it no
longer needs finiteness. -/
theorem pow_eq_one_iff_pow_gcd_exponent [Group α] {n : ℕ} (x : α) :
    x ^ n = 1 ↔ x ^ Nat.gcd n (Monoid.exponent α) = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one,
    Nat.dvd_gcd_iff]
  exact (and_iff_left (Monoid.order_dvd_exponent x)).symm

/-! ### Image: the `n`-th powers are the `gcd(n, exp)`-th powers (any group) -/

/-- **Image recovery against the exponent (any group).** As *sets*, the `n`-th
powers coincide with the `gcd(n, exp G)`-th powers. Unlike the parent's cyclic
argument (which compared subgroup cardinalities), this holds with no
commutativity and no finiteness: the easy inclusion uses `gcd(n,e) ∣ n`, and the
hard inclusion is the Bézout identity `gcd(n,e) = n·A + e·B` together with
`x^e = 1`, which exhibits `x^(gcd(n,e)) = (x^A)ⁿ`. -/
theorem range_pow_eq_range_pow_gcd_exponent [Group α] (n : ℕ) :
    Set.range (fun x : α => x ^ n)
      = Set.range (fun x : α => x ^ Nat.gcd n (Monoid.exponent α)) := by
  set e := Monoid.exponent α with he
  set d := Nat.gcd n e with hd
  apply Set.Subset.antisymm
  · -- `range (·ⁿ) ⊆ range (·^d)`:  `d ∣ n`, so `xⁿ = (x^(n/d))^d`.
    rintro _ ⟨x, rfl⟩
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left n e
    exact ⟨x ^ k, by show (x ^ k) ^ d = x ^ n; rw [← pow_mul', ← hk]⟩
  · -- `range (·^d) ⊆ range (·ⁿ)`:  Bézout `d = n·A + e·B` gives `x^d = (x^A)ⁿ`.
    rintro _ ⟨x, rfl⟩
    refine ⟨x ^ (Nat.gcdA n e), ?_⟩
    show (x ^ Nat.gcdA n e) ^ n = x ^ d
    have hbez : (d : ℤ) = n * Nat.gcdA n e + e * Nat.gcdB n e := by
      rw [hd]; exact Nat.gcd_eq_gcd_ab n e
    have hx : x ^ (e : ℤ) = 1 := zpow_exponent_eq_one x
    have hxe : x ^ ((e : ℤ) * Nat.gcdB n e) = 1 := by rw [zpow_mul, hx, one_zpow]
    calc (x ^ Nat.gcdA n e) ^ n
          = (x ^ Nat.gcdA n e) ^ (n : ℤ) := (zpow_natCast _ n).symm
      _ = x ^ ((n : ℤ) * Nat.gcdA n e) := by rw [← zpow_mul, mul_comm]
      _ = x ^ ((n : ℤ) * Nat.gcdA n e) * x ^ ((e : ℤ) * Nat.gcdB n e) := by
            rw [hxe, mul_one]
      _ = x ^ ((n : ℤ) * Nat.gcdA n e + (e : ℤ) * Nat.gcdB n e) := (zpow_add x _ _).symm
      _ = x ^ (d : ℤ) := by rw [← hbez]
      _ = x ^ d := zpow_natCast x d

/-! ### Abelian packaging: kernel and image as subgroups, and the partition -/

/-- **Kernel subgroup recovery (abelian).** In a commutative group the kernel of
`x ↦ xⁿ` is the `gcd(n, exp G)`-torsion subgroup. -/
theorem ker_powMonoidHom_eq_gcd_exponent [CommGroup α] (n : ℕ) :
    (powMonoidHom n : α →* α).ker
      = (powMonoidHom (Nat.gcd n (Monoid.exponent α)) : α →* α).ker := by
  ext x
  simp only [MonoidHom.mem_ker, powMonoidHom_apply]
  exact pow_eq_one_iff_pow_gcd_exponent x

/-- **Image subgroup recovery (abelian).** In a commutative group the subgroup of
`n`-th powers equals the subgroup of `gcd(n, exp G)`-th powers — the open
question's image equality, now for *every* abelian group (finite or not), with
`exp G` the correct invariant in place of `|G|`. -/
theorem range_powMonoidHom_eq_gcd_exponent [CommGroup α] (n : ℕ) :
    (powMonoidHom n : α →* α).range
      = (powMonoidHom (Nat.gcd n (Monoid.exponent α)) : α →* α).range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    have : (powMonoidHom n x) ∈ Set.range (fun x : α => x ^ n) := ⟨x, rfl⟩
    rw [range_pow_eq_range_pow_gcd_exponent n] at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hz⟩
  · rintro ⟨x, rfl⟩
    have : (powMonoidHom (Nat.gcd n (Monoid.exponent α)) x)
        ∈ Set.range (fun x : α => x ^ Nat.gcd n (Monoid.exponent α)) := ⟨x, rfl⟩
    rw [← range_pow_eq_range_pow_gcd_exponent n] at this
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hz⟩

/-- **Partition identity (finite abelian).** For a finite abelian group the power
map `x ↦ xⁿ` is a homomorphism, so its image and kernel cardinalities multiply to
`|G|`. The non-empty fibres all have the constant size `#ker = #(gcd(n,exp)-th
roots of unity)`, and there are `#range` of them. This is the parent's partition
identity `#range · #ker = |G|` in the form that survives the passage to a
non-cyclic group: the constant fibre size is `#ker`, which equals `gcd(n, |G|)`
exactly when `G` is cyclic. -/
theorem card_range_mul_card_ker_powMonoidHom [CommGroup α] [Fintype α] (n : ℕ) :
    Nat.card (powMonoidHom n : α →* α).range
        * Nat.card (powMonoidHom n : α →* α).ker
      = Fintype.card α := by
  set f := (powMonoidHom n : α →* α) with hf
  have hidx : f.ker.index = Nat.card f.range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have key : Nat.card f.ker * f.ker.index = Nat.card α := Subgroup.card_mul_index f.ker
  rw [hidx] at key
  rw [← Nat.card_eq_fintype_card, mul_comm]
  exact key
