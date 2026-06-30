/-
  The 2-adic Unit Group as an Internal Direct Product:
    `(ℤ/2ᵏℤ)ˣ = ⟨-1⟩ × ⟨5⟩`   for `k ≥ 3`.

  Open Question: euler-totient-oq-01-oq-02-oq-03

  The parent file `EulerTotientOQ01OQ02.lean` records, from Mathlib, the *value*
  of the Carmichael function on powers of two,
    `λ(2ᵏ) = Carmichael (2 ^ k) = 2 ^ (k - 2)`   (`k ≥ 3`),
  i.e. the exponent of the unit group `(ℤ/2ᵏℤ)ˣ` is `2ᵏ⁻²`, strictly below the
  order `φ(2ᵏ) = 2ᵏ⁻¹`.  Mathlib also knows that this group is **not** cyclic
  (`ZMod.isCyclic_units_two_pow_iff`) and that `5` has order `2ᵏ⁻²`
  (`ZMod.orderOf_five`).  What Mathlib does *not* package -- and what actually
  *explains* the value `2ᵏ⁻²` -- is the **structure theorem**:

    `(ℤ/2ᵏℤ)ˣ` is the internal direct product of the order-2 subgroup `⟨-1⟩`
    and the cyclic subgroup `⟨5⟩` of order `2ᵏ⁻²`.

  Equivalently `(ℤ/2ᵏℤ)ˣ ≅ ℤ/2 × ℤ/2ᵏ⁻²`, from which `λ(2ᵏ) = lcm(2, 2ᵏ⁻²) = 2ᵏ⁻²`
  drops out as a one-line consequence.

  The mathematical crux -- the one step that is genuinely *not* in Mathlib -- is

    `(*)   -1 ∉ ⟨5⟩`,

  proved by reduction mod `4`: every power of `5` is `≡ 1 (mod 4)` (since
  `5 ≡ 1`), whereas `-1 ≡ 3 (mod 4)`.  Reducing modulo `4` is a group
  homomorphism `(ℤ/2ᵏℤ)ˣ → (ℤ/4ℤ)ˣ` killing `5` but not `-1`, so the two can
  never coincide.  Together with the order count
    `|⟨-1⟩| · |⟨5⟩| = 2 · 2ᵏ⁻² = 2ᵏ⁻¹ = |(ℤ/2ᵏℤ)ˣ|`
  this yields the internal direct-product decomposition `IsComplement'`.

  To keep every exponent free of truncated natural subtraction we parametrise the
  power as `k = n + 3` throughout (so `k ≥ 3 ⇔ n : ℕ`), with `2ᵏ⁻² = 2ⁿ⁺¹` and
  `φ(2ᵏ) = 2ⁿ⁺²`.

  ## Key Results
  1. `five`                          : the unit `5 ∈ (ℤ/2ⁿ⁺³ℤ)ˣ`
  2. `orderOf_five`                  : `orderOf 5 = 2ⁿ⁺¹`
  3. `orderOf_neg_one`               : `orderOf (-1) = 2`
  4. `neg_one_notMem_zpowers_five`   : `-1 ∉ ⟨5⟩`         (the crux `(*)`)
  5. `disjoint_neg_one_five`         : `Disjoint ⟨-1⟩ ⟨5⟩`
  6. `isComplement'_neg_one_five`    : `(ℤ/2ⁿ⁺³ℤ)ˣ = ⟨-1⟩ × ⟨5⟩`  (structure theorem)
  7. `carmichael_two_pow`            : `λ(2ⁿ⁺³) = 2ⁿ⁺¹`  (recovered from the structure)

  ## References
  - Ireland & Rosen, "A Classical Introduction to Modern Number Theory" (1990), Ch. 4
  - Mathlib: `Mathlib/RingTheory/ZMod/UnitsCyclic.lean`,
             `Mathlib/NumberTheory/ArithmeticFunction/Carmichael.lean`
-/

import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Tactic

namespace EulerTotientOQ01OQ02OQ03

-- This file uses `simp only [...]` followed by `decide`/`rw` closers; the
-- `unusedSimpArgs` linter reports false positives in that pattern.
set_option linter.unusedSimpArgs false

open ArithmeticFunction Subgroup

variable (n : ℕ)

/-- The unit `5` in `(ℤ/2ⁿ⁺³ℤ)ˣ`.  It generates the cyclic factor of the
    decomposition and has order `2ⁿ⁺¹`. -/
def five : (ZMod (2 ^ (n + 3)))ˣ :=
  ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right _ (by decide))

@[simp] theorem val_five : (five n : ZMod (2 ^ (n + 3))) = 5 := by
  simp [five, ZMod.coe_unitOfCoprime]

/-- **Order of the generator `5`.** `orderOf 5 = 2ⁿ⁺¹` in `(ℤ/2ⁿ⁺³ℤ)ˣ`.
    This is `ZMod.orderOf_five` transported from the ring to the unit group. -/
@[simp] theorem orderOf_five : orderOf (five n) = 2 ^ (n + 1) := by
  rw [← orderOf_units, val_five, show n + 3 = (n + 1) + 2 by ring, ZMod.orderOf_five]

/-- `4 ∣ 2ⁿ⁺³`, the divisibility underlying the reduction `ℤ/2ⁿ⁺³ℤ → ℤ/4ℤ`. -/
theorem dvd4 : (4 : ℕ) ∣ 2 ^ (n + 3) := by
  simpa using pow_dvd_pow 2 (show 2 ≤ n + 3 by omega)

/-- Reduction `(ℤ/2ⁿ⁺³ℤ)ˣ → (ℤ/4ℤ)ˣ` induced by the ring map `ℤ/2ⁿ⁺³ℤ → ℤ/4ℤ`. -/
private def red : (ZMod (2 ^ (n + 3)))ˣ →* (ZMod 4)ˣ :=
  Units.map (ZMod.castHom (dvd4 n) (ZMod 4)).toMonoidHom

@[simp] theorem red_five : red n (five n) = 1 := by
  apply Units.ext
  change ZMod.castHom (dvd4 n) (ZMod 4) (↑(five n)) = ↑(1 : (ZMod 4)ˣ)
  rw [val_five, map_ofNat, Units.val_one]
  decide

@[simp] theorem red_neg_one : red n (-1) = -1 := by
  apply Units.ext
  change ZMod.castHom (dvd4 n) (ZMod 4) (↑(-1 : (ZMod (2 ^ (n + 3)))ˣ)) = ↑(-1 : (ZMod 4)ˣ)
  rw [Units.val_neg, Units.val_one, map_neg, map_one, Units.val_neg, Units.val_one]

/-- **Order of `-1`.** In `(ℤ/2ⁿ⁺³ℤ)ˣ` the element `-1` has order exactly `2`. -/
@[simp] theorem orderOf_neg_one : orderOf (-1 : (ZMod (2 ^ (n + 3)))ˣ) = 2 := by
  apply orderOf_eq_prime
  · simp
  · intro h
    have key := congrArg (red n) h
    rw [red_neg_one, map_one] at key
    exact absurd (congrArg Units.val key) (by decide)

/-- **The crux `(*)`: `-1 ∉ ⟨5⟩`.**  Every power of `5` reduces to `1` modulo `4`,
    while `-1` reduces to `-1 ≠ 1`; hence `-1` is never a power of `5`.  This is
    precisely the obstruction to `(ℤ/2ᵏℤ)ˣ` being cyclic. -/
theorem neg_one_notMem_zpowers_five :
    (-1 : (ZMod (2 ^ (n + 3)))ˣ) ∉ zpowers (five n) := by
  intro hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  -- `hm : five n ^ m = -1`.  Apply the reduction `red`.
  have key := congrArg (red n) hm
  rw [map_zpow, red_five, one_zpow, red_neg_one] at key
  -- `key : (1 : (ZMod 4)ˣ) = -1`
  exact absurd (congrArg Units.val key) (by decide)

/-- The two cyclic subgroups `⟨-1⟩` and `⟨5⟩` are disjoint. -/
theorem disjoint_neg_one_five :
    Disjoint (zpowers (-1 : (ZMod (2 ^ (n + 3)))ˣ)) (zpowers (five n)) := by
  rw [disjoint_iff_inf_le]
  rintro x ⟨hxH, hxK⟩
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxH
  rw [Subgroup.mem_bot]
  rcases Int.even_or_odd m with he | ho
  · simpa using he.neg_zpow (1 : (ZMod (2 ^ (n + 3)))ˣ)
  · obtain ⟨k, rfl⟩ := ho
    have h2k : (-1 : (ZMod (2 ^ (n + 3)))ˣ) ^ (2 * k) = 1 := by
      simpa using (even_two_mul k).neg_zpow (1 : (ZMod (2 ^ (n + 3)))ˣ)
    have hval : (-1 : (ZMod (2 ^ (n + 3)))ˣ) ^ (2 * k + 1) = -1 := by
      rw [zpow_add, zpow_one, h2k, one_mul]
    rw [hval] at hxK
    exact absurd hxK (neg_one_notMem_zpowers_five n)

/-- `|(ℤ/2ⁿ⁺³ℤ)ˣ| = 2ⁿ⁺²`. -/
theorem card_units : Nat.card (ZMod (2 ^ (n + 3)))ˣ = 2 ^ (n + 2) := by
  rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    show n + 3 = (n + 2) + 1 from rfl, Nat.totient_prime_pow_succ Nat.prime_two]
  norm_num

/-- **Structure theorem.**  `(ℤ/2ⁿ⁺³ℤ)ˣ` is the internal direct product of the
    order-`2` subgroup `⟨-1⟩` and the order-`2ⁿ⁺¹` cyclic subgroup `⟨5⟩`:

      `(ℤ/2ᵏℤ)ˣ = ⟨-1⟩ × ⟨5⟩`   for `k = n + 3 ≥ 3`.

    Concretely, multiplication `⟨-1⟩ × ⟨5⟩ → (ℤ/2ᵏℤ)ˣ` is a bijection, so every
    unit is **uniquely** `(-1)ᵃ · 5ᵇ` with `a ∈ {0,1}`, `0 ≤ b < 2ᵏ⁻²`. -/
theorem isComplement'_neg_one_five :
    IsComplement' (zpowers (-1 : (ZMod (2 ^ (n + 3)))ˣ)) (zpowers (five n)) := by
  apply isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_neg_one, orderOf_five, card_units]
    ring
  · exact disjoint_neg_one_five n

/-- **Recovering `λ(2ᵏ) = 2ᵏ⁻²` from the structure.**  The exponent of a direct
    product is the lcm of the exponents, so
      `Carmichael (2ⁿ⁺³) = lcm(2, 2ⁿ⁺¹) = 2ⁿ⁺¹`,
    consistent with the decomposition `⟨-1⟩ × ⟨5⟩` above (the `⟨5⟩` factor is the
    larger of the two). -/
theorem carmichael_two_pow : Carmichael (2 ^ (n + 3)) = 2 ^ (n + 1) := by
  have h : n + 3 - 2 = n + 1 := by omega
  rw [carmichael_two_pow_of_ne_two (show n + 3 ≠ 2 by omega), h]

end EulerTotientOQ01OQ02OQ03
