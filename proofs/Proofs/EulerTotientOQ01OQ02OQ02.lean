import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic

/-!
# Euler totient OQ-01 → OQ-02 → OQ-02: the Carmichael function on *even* prime powers

The parent (`euler-totient-oq-01-oq-02`, verified) packages the Carmichael function `λ` on
prime powers and records the headline value `λ(2ᵏ) = 2ᵏ⁻²` for `k ≥ 3` as a one-line
restatement of Mathlib's `carmichael_two_pow_of_ne_two`. The odd-prime sibling
(`euler-totient-oq-01-oq-02-oq-01`, verified) supplied the *mechanism* on the cyclic side:
`(ℤ/pᵏℤ)ˣ` is cyclic, so its exponent equals its order, `λ(pᵏ) = φ(pᵏ)`, and a **primitive
root** (a unit of order `φ`) exists.

This entry is the **exact dual** for the even prime `p = 2`, where the phenomenon is the
opposite. For `k ≥ 3` the unit group `(ℤ/2ᵏℤ)ˣ ≅ ℤ/2 × ℤ/2ᵏ⁻²` is **not cyclic**, so:

> there is **no primitive root** modulo `2ᵏ`,

and consequently the exponent drops strictly below the order:

> `λ(2ᵏ) = 2ᵏ⁻² < 2ᵏ⁻¹ = φ(2ᵏ)`  —  `λ` is *strictly* less than `φ`.

The contrast is genuinely two-sided and the boundary is **sharp**: `(ℤ/2ᵏℤ)ˣ` is cyclic for
`k ≤ 2` (so `λ(1) = λ(2) = 1`, `λ(4) = 2 = φ(4)`, and a primitive root *does* exist mod `4`),
and ceases to be cyclic at exactly `k = 3` (`λ(8) = 2 < 4 = φ(8)`).

The new content relative to the parent is the structural *reason* the value `2ᵏ⁻²` is forced —
non-cyclicity and the non-existence of a primitive root — together with the strict inequality
`λ(2ᵏ) < φ(2ᵏ)` and the sharp `k ≤ 2 / k ≥ 3` dichotomy, none of which the parent states.

## Main results

* `not_isCyclic_units_two_pow` : `(ℤ/2ᵏℤ)ˣ` is **not** cyclic for `k ≥ 3` (the mechanism).
* `no_primitiveRoot_two_pow` : **no** unit mod `2ᵏ` has order `φ(2ᵏ)` for `k ≥ 3` — i.e. there
  is no primitive root (the headline dual of the odd-prime sibling).
* `carmichael_two_pow` : `λ(2ᵏ) = 2ᵏ⁻²` for `k ≥ 3` (the OQ's target value).
* `exponent_units_two_pow` : exponent `(ℤ/2ᵏℤ)ˣ = 2ᵏ⁻²` (`λ` *is* the group exponent).
* `carmichael_lt_totient` : `λ(2ᵏ) < φ(2ᵏ)` for `k ≥ 3` — the **strict** divisor phenomenon.
* `carmichael_two`, `carmichael_four`, `isCyclic_units_four`,
  `exists_primitiveRoot_four` : the cyclic exceptions `k ≤ 2` (`λ(2)=1`, `λ(4)=2`, a primitive
  root mod `4`), pinning the sharp boundary.
* `carmichael_eight`, `carmichael_sixteen`, `carmichael_thirtytwo` : concrete `λ(8)=2`,
  `λ(16)=4`, `λ(32)=8`.
-/

namespace EulerTotientOQ01OQ02OQ02

open ArithmeticFunction Nat

/-! ### The mechanism: non-cyclicity of `(ℤ/2ᵏℤ)ˣ` for `k ≥ 3` -/

/-- **The unit group of `2ᵏ` is *not* cyclic for `k ≥ 3`.** This is the structural fact behind
    the even-prime exception, the exact opposite of the odd-prime-power case: `(ℤ/2ᵏℤ)ˣ` is
    `ℤ/2 × ℤ/2ᵏ⁻²`, a product of two nontrivial cyclic groups, hence not cyclic. Everything
    below — the strict drop `λ < φ` and the absence of a primitive root — flows from this.
    (Mathlib: `ZMod.isCyclic_units_two_pow_iff`, cyclic ⟺ `k ≤ 2`.) -/
theorem not_isCyclic_units_two_pow {k : ℕ} (hk : 3 ≤ k) :
    ¬ IsCyclic (ZMod (2 ^ k))ˣ :=
  (ZMod.isCyclic_units_two_pow_iff k).not.mpr (by omega)

/-! ### The headline dual: no primitive root modulo `2ᵏ` -/

/-- **No primitive root modulo `2ᵏ` for `k ≥ 3`.** A primitive root would be a unit `g` of
    order `φ(2ᵏ) = #(ℤ/2ᵏℤ)ˣ`, and a single element whose order equals the group order
    generates the whole group — forcing it to be cyclic. Since `(ℤ/2ᵏℤ)ˣ` is *not* cyclic for
    `k ≥ 3`, no such `g` exists. This is the precise dual of the odd-prime sibling's
    `exists_primitiveRoot_odd_prime_pow`: where odd prime powers always have a primitive root,
    high powers of two never do. -/
theorem no_primitiveRoot_two_pow {k : ℕ} (hk : 3 ≤ k) :
    ¬ ∃ g : (ZMod (2 ^ k))ˣ, orderOf g = (2 ^ k).totient := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rintro ⟨g, hg⟩
  refine not_isCyclic_units_two_pow hk ?_
  apply isCyclic_of_orderOf_eq_card g
  rw [hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

/-! ### The Carmichael value and its identification with the group exponent -/

/-- **`λ(2ᵏ) = 2ᵏ⁻²` for `k ≥ 3`** — the open question's target value. Because the unit group
    is not cyclic, its exponent `2ᵏ⁻²` is strictly smaller than its order `2ᵏ⁻¹`.
    (Mathlib: `carmichael_two_pow_of_ne_two`, valid for every `n ≠ 2`.) -/
theorem carmichael_two_pow {k : ℕ} (hk : 3 ≤ k) :
    Carmichael (2 ^ k) = 2 ^ (k - 2) :=
  carmichael_two_pow_of_ne_two (by omega)

/-- **`λ(2ᵏ)` *is* the exponent of `(ℤ/2ᵏℤ)ˣ`, equal to `2ᵏ⁻²` for `k ≥ 3`.** The Carmichael
    function is by definition the exponent of the unit group (the smallest `m` with `aᵐ = 1`
    for every unit `a`); here that exponent is `2ᵏ⁻²` — the universal exponent that no single
    element's order reaches. -/
theorem exponent_units_two_pow {k : ℕ} (hk : 3 ≤ k) :
    Monoid.exponent (ZMod (2 ^ k))ˣ = 2 ^ (k - 2) := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  rw [← carmichael_eq_exponent', carmichael_two_pow hk]

/-! ### The strict divisor phenomenon `λ(2ᵏ) < φ(2ᵏ)` -/

/-- **`φ(2ᵏ) = 2ᵏ⁻¹` for `k ≥ 1`.** The totient of a power of two: half of `2ᵏ` are odd, hence
    coprime to `2ᵏ`. Recorded here so the strict gap below reads off directly. -/
theorem totient_two_pow {k : ℕ} (hk : 1 ≤ k) :
    (2 ^ k).totient = 2 ^ (k - 1) := by
  simp [Nat.totient_prime_pow Nat.prime_two hk]

/-- **`λ(2ᵏ) < φ(2ᵏ)` for `k ≥ 3`** — the *strict* form of `λ ∣ φ`. The parent records only
    `2·λ(2ᵏ) = φ(2ᵏ)`; this states the sharp inequality `2ᵏ⁻² < 2ᵏ⁻¹` it conceals, the precise
    quantitative witness that Euler's exponent `φ(2ᵏ)` is *not* optimal — exactly because there
    is no primitive root. -/
theorem carmichael_lt_totient {k : ℕ} (hk : 3 ≤ k) :
    Carmichael (2 ^ k) < (2 ^ k).totient := by
  rw [carmichael_two_pow hk, totient_two_pow (by omega)]
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ### The sharp boundary: the cyclic exceptions `k ≤ 2` -/

/-- **`λ(2) = 1`.** `(ℤ/2ℤ)ˣ` is trivial, so its exponent is `1`. -/
theorem carmichael_two : Carmichael 2 = 1 := by
  have h := carmichael_two_pow_of_le_two (n := 1) (by norm_num)
  norm_num at h
  exact h

/-- **`λ(4) = 2 = φ(4)`.** Here `(ℤ/4ℤ)ˣ = {1, 3}` *is* cyclic, generated by `3`, so the
    Carmichael value still equals the totient — the last power of two before the exception. -/
theorem carmichael_four : Carmichael 4 = 2 := by
  have h := carmichael_two_pow_of_le_two (n := 2) (by norm_num)
  norm_num at h
  exact h

/-- **`(ℤ/4ℤ)ˣ` is cyclic** — the boundary case `k = 2`, the largest power of two whose unit
    group is cyclic. (Mathlib: `ZMod.isCyclic_units_four`.) -/
theorem isCyclic_units_four : IsCyclic (ZMod 4)ˣ :=
  ZMod.isCyclic_units_four

/-- **A primitive root *does* exist modulo `4`.** In sharp contrast with `k ≥ 3`, the cyclic
    group `(ℤ/4ℤ)ˣ` has a generator of order `φ(4) = 2` (namely `3 ≡ −1`). This pins the sharp
    boundary: primitive roots exist for `k ≤ 2` and vanish for `k ≥ 3`. -/
theorem exists_primitiveRoot_four :
    ∃ g : (ZMod 4)ˣ, orderOf g = (4 : ℕ).totient := by
  haveI := ZMod.isCyclic_units_four
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod 4)ˣ)
  exact ⟨g, by rw [hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]⟩

/-! ### Concrete values -/

/-- `λ(8) = 2` (the first non-cyclic case: `2 < 4 = φ(8)`). -/
theorem carmichael_eight : Carmichael 8 = 2 := by
  have h := carmichael_two_pow (k := 3) (by norm_num)
  norm_num at h
  exact h

/-- `λ(16) = 4` (`< 8 = φ(16)`). -/
theorem carmichael_sixteen : Carmichael 16 = 4 := by
  have h := carmichael_two_pow (k := 4) (by norm_num)
  norm_num at h
  exact h

/-- `λ(32) = 8` (`< 16 = φ(32)`). -/
theorem carmichael_thirtytwo : Carmichael 32 = 8 := by
  have h := carmichael_two_pow (k := 5) (by norm_num)
  norm_num at h
  exact h

end EulerTotientOQ01OQ02OQ02
