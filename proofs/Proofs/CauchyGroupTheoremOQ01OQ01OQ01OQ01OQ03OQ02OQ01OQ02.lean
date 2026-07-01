import Mathlib.Tactic

/-
# The exponent–gcd image equality on a finite commutative monoid

The parent entry proved, **in every group**, the image equality

      range (x ↦ xⁿ)  =  range (x ↦ x^(gcd(n, exp G)))

with the *exponent* `e = exp G` as the governing invariant, and left as an open
question (parent OQ #2) whether a *correct exponent–gcd statement* survives the
passage to a finite **commutative monoid**, "restricted to its group of units or
otherwise."

This file gives the precise answer. It has three parts.

## 1. The crux: the exponent detects group-likeness

For a monoid `M`, `exp M ≠ 0` forces **every** element to be a unit
(`isUnit_of_exponent_ne_zero`): if `x^e = 1` with `e ≥ 1` then `x^(e-1)` is a
two-sided inverse of `x`. Contrapositively, a **single** non-unit collapses the
exponent to `0` (`exponent_eq_zero_of_exists_not_isUnit`). For a finite
commutative monoid the converse holds too — a finite monoid all of whose elements
are units transfers its exponent from the finite group of units — giving the
clean characterization

      exp M ≠ 0  ↔  every element of M is a unit         (`exponent_ne_zero_iff_forall_isUnit`).

So on a finite commutative monoid the exponent is nonzero *exactly* when `M` is a
group; the moment `M` has a genuine non-unit, `exp M = 0`.

## 2. The positive answer — restricted to the group of units

Since `Mˣ` is always a group, the parent theorem applies verbatim to it
(`range_pow_units_eq_gcd_exponent`): the `n`-th powers among the units coincide,
as sets, with the `gcd(n, exp Mˣ)`-th powers. This is the "restricted to its
group of units" reading, and it is the right home for the equality. (The group
theorem it invokes, `range_pow_eq_range_pow_gcd_exponent`, is reproved inline here
so this file is self-contained.)

## 3. The full-monoid readings

* **Against the exponent, "otherwise" degenerates.** For a non-group finite
  monoid `exp M = 0`, so `gcd(n, exp M) = n` and the equality
  `range(·ⁿ) = range(·^gcd(n, exp M))` holds — but *vacuously*, as an identity of
  the map with itself (`range_pow_eq_range_pow_gcd_exponent_of_not_group`). There
  is no nontrivial exponent–gcd content on the non-unit part.
* **Against the order `|M|`, the naive surrogate is genuinely false.** In the
  multiplicative monoid `ZMod 4` (a finite commutative monoid, not a group: `2` is
  a non-unit, so `exp = 0`) the cube map has image `{0,1,3}`, whereas
  `gcd(3, |ZMod 4|) = gcd(3,4) = 1` would predict the full monoid — the two images
  differ (`order_surrogate_fails_zmod4`). This is the concrete obstruction: the
  cyclic-style `|M|`-based statement cannot extend past groups.

Everything is over `Mathlib.Tactic`; no axioms, no `native_decide`.
-/

variable {M : Type*}

/-! ### 0. The group image theorem (reproved inline from the parent) -/

/-- `x` raised to the integer-cast exponent is the identity, in any group. -/
private theorem zpow_exponent_eq_one' [Group M] (x : M) :
    x ^ (Monoid.exponent M : ℤ) = 1 := by
  rw [zpow_natCast]
  exact Monoid.pow_exponent_eq_one x

/-- **Image recovery against the exponent (any group).** As sets, the `n`-th
powers coincide with the `gcd(n, exp G)`-th powers. Easy inclusion: `gcd(n,e) ∣ n`.
Hard inclusion: Bézout `gcd(n,e) = n·A + e·B` with `x^e = 1` gives
`x^(gcd(n,e)) = (x^A)ⁿ`. Reproved here from the parent entry for self-containment. -/
theorem range_pow_eq_range_pow_gcd_exponent [Group M] (n : ℕ) :
    Set.range (fun x : M => x ^ n)
      = Set.range (fun x : M => x ^ Nat.gcd n (Monoid.exponent M)) := by
  set e := Monoid.exponent M with he
  set d := Nat.gcd n e with hd
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    obtain ⟨k, hk⟩ := Nat.gcd_dvd_left n e
    exact ⟨x ^ k, by show (x ^ k) ^ d = x ^ n; rw [← pow_mul', ← hk]⟩
  · rintro _ ⟨x, rfl⟩
    refine ⟨x ^ (Nat.gcdA n e), ?_⟩
    show (x ^ Nat.gcdA n e) ^ n = x ^ d
    have hbez : (d : ℤ) = n * Nat.gcdA n e + e * Nat.gcdB n e := by
      rw [hd]; exact Nat.gcd_eq_gcd_ab n e
    have hx : x ^ (e : ℤ) = 1 := zpow_exponent_eq_one' x
    have hxe : x ^ ((e : ℤ) * Nat.gcdB n e) = 1 := by rw [zpow_mul, hx, one_zpow]
    calc (x ^ Nat.gcdA n e) ^ n
          = (x ^ Nat.gcdA n e) ^ (n : ℤ) := (zpow_natCast _ n).symm
      _ = x ^ ((n : ℤ) * Nat.gcdA n e) := by rw [← zpow_mul, mul_comm]
      _ = x ^ ((n : ℤ) * Nat.gcdA n e) * x ^ ((e : ℤ) * Nat.gcdB n e) := by
            rw [hxe, mul_one]
      _ = x ^ ((n : ℤ) * Nat.gcdA n e + (e : ℤ) * Nat.gcdB n e) := (zpow_add x _ _).symm
      _ = x ^ (d : ℤ) := by rw [← hbez]
      _ = x ^ d := zpow_natCast x d

/-! ### 1. The crux: `exp M ≠ 0` iff every element is a unit -/

/-- **A nonzero exponent forces units.** If `Monoid.exponent M ≠ 0` then for every
`x`, the identity `x ^ e = 1` (with `e = exp M ≥ 1`) makes `x^(e-1)` a two-sided
inverse of `x`, so `x` is a unit. -/
theorem isUnit_of_exponent_ne_zero [Monoid M] (h : Monoid.exponent M ≠ 0) (x : M) :
    IsUnit x := by
  have he1 : 1 ≤ Monoid.exponent M := Nat.one_le_iff_ne_zero.mpr h
  have hx : x * x ^ (Monoid.exponent M - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel he1]; exact Monoid.pow_exponent_eq_one x
  have hx' : x ^ (Monoid.exponent M - 1) * x = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel he1]; exact Monoid.pow_exponent_eq_one x
  exact ⟨⟨x, x ^ (Monoid.exponent M - 1), hx, hx'⟩, rfl⟩

/-- **A single non-unit collapses the exponent.** The contrapositive of
`isUnit_of_exponent_ne_zero`: if some element of `M` fails to be a unit, then
`Monoid.exponent M = 0`. This is why no `|M|`- or `exp`-based image statement can
carry content on a monoid that is not a group. -/
theorem exponent_eq_zero_of_exists_not_isUnit [Monoid M]
    (h : ∃ x : M, ¬ IsUnit x) : Monoid.exponent M = 0 := by
  by_contra hne
  obtain ⟨x, hx⟩ := h
  exact hx (isUnit_of_exponent_ne_zero hne x)

/-- **Characterization (finite commutative case).** For a finite commutative
monoid, `Monoid.exponent M ≠ 0` holds *exactly* when every element is a unit —
i.e. exactly when `M` is a group. The forward direction is the crux above; the
converse transfers the (nonzero) exponent of the finite group of units `Mˣ`. -/
theorem exponent_ne_zero_iff_forall_isUnit
    [CommMonoid M] [Fintype M] [DecidableEq M] :
    Monoid.exponent M ≠ 0 ↔ ∀ x : M, IsUnit x := by
  constructor
  · intro h x
    exact isUnit_of_exponent_ne_zero h x
  · intro hall
    rw [Monoid.exponent_ne_zero]
    refine ⟨Monoid.exponent Mˣ, Nat.pos_of_ne_zero (Monoid.exponent_ne_zero_of_finite), ?_⟩
    intro x
    obtain ⟨u, rfl⟩ := hall x
    rw [← Units.val_pow_eq_pow_val, Monoid.pow_exponent_eq_one, Units.val_one]

/-! ### 2. The positive answer: image equality on the group of units -/

/-- **Exponent–gcd image equality on the units (the parent's home for monoids).**
`Mˣ` is a group, so the parent theorem applies unchanged: as *sets*, the `n`-th
powers among the units of `M` coincide with the `gcd(n, exp Mˣ)`-th powers. This
is the "restricted to its group of units" reading of parent OQ #2. -/
theorem range_pow_units_eq_gcd_exponent [Monoid M] (n : ℕ) :
    Set.range (fun u : Mˣ => u ^ n)
      = Set.range (fun u : Mˣ => u ^ Nat.gcd n (Monoid.exponent Mˣ)) :=
  range_pow_eq_range_pow_gcd_exponent n

/-! ### 3. The full-monoid readings: degeneracy against `exp`, failure against `|M|` -/

/-- **Against the exponent, the "otherwise" reading degenerates.** For a finite
monoid that is *not* a group (it has a non-unit), `exp M = 0`, hence
`gcd(n, exp M) = n` and the image equality `range(·ⁿ) = range(·^gcd(n, exp M))`
holds — but only as the identity of the power map with itself. No content beyond
the units survives. -/
theorem range_pow_eq_range_pow_gcd_exponent_of_not_group [Monoid M]
    (h : ∃ x : M, ¬ IsUnit x) (n : ℕ) :
    Set.range (fun x : M => x ^ n)
      = Set.range (fun x : M => x ^ Nat.gcd n (Monoid.exponent M)) := by
  rw [exponent_eq_zero_of_exists_not_isUnit h, Nat.gcd_zero_right]

/-- `ZMod 4` under multiplication is a finite commutative monoid that is **not** a
group: `2` is a non-unit (`2 · x ∈ {0,2}` never hits `1`). -/
theorem not_isUnit_two_zmod4 : ¬ IsUnit (2 : ZMod 4) := by decide

/-- Consequently its exponent is `0` — a witness of the crux above. -/
theorem exponent_zmod4_eq_zero : Monoid.exponent (ZMod 4) = 0 :=
  exponent_eq_zero_of_exists_not_isUnit ⟨2, not_isUnit_two_zmod4⟩

/-- **The exponent reading holds, trivially, on `ZMod 4`.** Since `exp = 0`,
`gcd(n, exp) = n` and both sides are the same map. -/
theorem exp_statement_trivial_zmod4 (n : ℕ) :
    Set.range (fun x : ZMod 4 => x ^ n)
      = Set.range (fun x : ZMod 4 => x ^ Nat.gcd n (Monoid.exponent (ZMod 4))) := by
  rw [exponent_zmod4_eq_zero, Nat.gcd_zero_right]

/-- **The `|M|`-order surrogate genuinely fails.** With `|ZMod 4| = 4` and
`gcd(3,4) = 1`, the cyclic-style prediction would equate the cube map with the
identity map. But the cube map has image `{0,1,3}` (missing `2`), while the
identity map has image all of `ZMod 4`. So the order-based statement — the direct
transcription of the parent's cyclic form — is false on this non-group monoid. -/
theorem order_surrogate_fails_zmod4 :
    Finset.univ.image (fun x : ZMod 4 => x ^ 3)
      ≠ Finset.univ.image (fun x : ZMod 4 => x ^ Nat.gcd 3 (Fintype.card (ZMod 4))) := by
  decide
