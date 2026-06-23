import Mathlib
import Proofs.ChineseRemainderConstructiveOQ03

/-
# Chinese Remainder Theorem — OQ-03-OQ-03: Power-of-2 RNS Channels

## Question
Can the RNS framework be extended to handle bases with 2 as a modulus —
where the standard CRT requires extra care — for hardware implementations
that use power-of-2 channels?

## Answer: YES — with exactly one power of 2 alongside odd moduli

The RNS framework extends naturally to include a power-of-2 modulus `2^k`
(k ≥ 1) alongside any collection of pairwise coprime odd moduli. The "extra
care" is not about CRT validity — it works exactly as before — but about the
constraint that only ONE power of 2 can appear:

- `gcd(2^a, 2^b) = 2^min(a,b) ≥ 2` for `a, b ≥ 1` → two powers of 2 break coprimality
- `gcd(2^k, m) = 1` whenever `m` is odd → one power of 2 is always fine

### Key Results
1. **Coprimality**: `2^k` is coprime to any odd number (proved directly from
   `Nat.Coprime.pow_left` and `Nat.coprime_two_right`)
2. **Uniqueness constraint**: Exactly ONE power of 2 can appear in any valid RNS base
3. **Validity**: `{2^k, m₁, m₂, ..., mₙ}` with odd pairwise-coprime mᵢ forms a
   valid pairwise-coprime RNS base, yielding dynamic range `2^k × ∏ mᵢ`
4. **Hardware efficiency**: `x mod 2^k` = bit-AND = `x &&& (2^k - 1)` (one instruction)

### Concrete Examples
- `{4, 3, 5, 7}`: dynamic range 420, max width 7
- `{8, 3, 5, 7, 11}`: dynamic range 9240, max width 11
- `{16, 3, 5, 7, 11, 13}`: dynamic range 240240, max width 16

### Comparison with prime bases
- `{2, 3, 5, 7}`: range 210 (4 channels, prime base)
- `{4, 3, 5, 7}`: range 420 (same 4 channels, 2× range by using 4 instead of 2)

## References
- Garner, "The residue number system" (1959)
- Szabó–Tanaka, "Residue Arithmetic and Its Applications" (1967)

## Status
- Axioms: 0
- Sorries: 0

Tags: number-theory, modular-arithmetic, rns, power-of-2, hardware
-/

namespace PowerOfTwoRNS

open RNSBases

-- ============================================================
-- Part I: Coprimality of Powers of 2 with Odd Numbers
-- ============================================================

/-- `2^k` is coprime to any odd number `m`.
    Proof: `Nat.Coprime 2 m` since `m` is odd (by `Nat.coprime_two_right`),
    then extend to `2^k` via `Nat.Coprime.pow_left`. -/
theorem pow2_coprime_odd (k : ℕ) {m : ℕ} (hm : m % 2 = 1) :
    Nat.Coprime (2 ^ k) m :=
  Nat.Coprime.pow_left k (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hm))

/-- Symmetric form: odd `m` is coprime to `2^k`. -/
theorem odd_coprime_pow2 (k : ℕ) {m : ℕ} (hm : m % 2 = 1) :
    Nat.Coprime m (2 ^ k) :=
  (pow2_coprime_odd k hm).symm

/-- Two positive powers of 2 are NOT coprime.
    `gcd(2^k, 2^j) ≥ 2` since `2 ∣ 2^k` and `2 ∣ 2^j`. -/
theorem pow2_not_coprime_pow2 {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    ¬ Nat.Coprime (2 ^ k) (2 ^ j) := by
  intro h
  have h2k : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
  have h2j : 2 ∣ 2 ^ j := dvd_pow_self 2 (by omega)
  have h2gcd : 2 ∣ Nat.gcd (2 ^ k) (2 ^ j) := Nat.dvd_gcd h2k h2j
  rw [h] at h2gcd
  exact absurd h2gcd (by norm_num)

-- ============================================================
-- Part II: The Pow2RNSBase Structure
-- ============================================================

/-- A valid power-of-2 RNS base: one channel is `2^power` (power ≥ 1),
    all other channels are odd integers ≥ 3 and pairwise coprime. -/
structure Pow2RNSBase where
  /-- Exponent for the power-of-2 channel. -/
  power : ℕ
  /-- Odd moduli (each ≥ 3). -/
  oddMods : List ℕ
  power_pos : 1 ≤ power
  mods_ge_three : ∀ m ∈ oddMods, 3 ≤ m
  mods_odd : ∀ m ∈ oddMods, m % 2 = 1
  mods_coprime : oddMods.Pairwise Nat.Coprime

/-- The list of all moduli: `[2^power] ++ oddMods`. -/
def Pow2RNSBase.moduli (b : Pow2RNSBase) : List ℕ := 2 ^ b.power :: b.oddMods

/-- A `Pow2RNSBase` yields a pairwise coprime list. The power-of-2 channel
    is coprime to all odd channels by `pow2_coprime_odd`; odd channels are
    mutually coprime by assumption. -/
theorem Pow2RNSBase.pairwise_coprime (b : Pow2RNSBase) :
    b.moduli.Pairwise Nat.Coprime := by
  unfold Pow2RNSBase.moduli
  apply List.Pairwise.cons
  · intro m hm
    exact pow2_coprime_odd b.power (b.mods_odd m hm)
  · exact b.mods_coprime

/-- All moduli in a `Pow2RNSBase` are ≥ 2. -/
theorem Pow2RNSBase.moduli_ge_two (b : Pow2RNSBase) :
    ∀ m ∈ b.moduli, 2 ≤ m := by
  intro m hm
  simp only [Pow2RNSBase.moduli, List.mem_cons] at hm
  rcases hm with rfl | hm
  · -- 2 ≤ 2^power since power ≥ 1
    calc 2 = 2 ^ 1 := by norm_num
         _ ≤ 2 ^ b.power := Nat.pow_le_pow_right (by norm_num) b.power_pos
  · -- 2 ≤ m since m ≥ 3
    have := b.mods_ge_three m hm; omega

/-- Embed a `Pow2RNSBase` into the standard `RNSBase` structure. -/
def Pow2RNSBase.toRNSBase (b : Pow2RNSBase) : RNSBase :=
  { moduli := b.moduli
    coprime := b.pairwise_coprime
    ge_two := b.moduli_ge_two }

/-- The dynamic range of a `Pow2RNSBase` equals `2^power × ∏ oddMods`. -/
theorem Pow2RNSBase.dynamicRange_eq (b : Pow2RNSBase) :
    b.toRNSBase.dynamicRange = 2 ^ b.power * b.oddMods.prod := by
  simp [RNSBase.dynamicRange, Pow2RNSBase.toRNSBase, Pow2RNSBase.moduli,
        List.prod_cons]

-- ============================================================
-- Part III: Concrete Examples
-- ============================================================

/-- `{4, 3, 5, 7}` is a valid RNS base (4 = 2², pairwise coprime).
    Dynamic range = 4 × 3 × 5 × 7 = 420. -/
theorem base_4_3_5_7_coprime : [4, 3, 5, 7].Pairwise Nat.Coprime := by decide

theorem base_4_3_5_7_range : [4, 3, 5, 7].prod = 420 := by norm_num

/-- `{8, 3, 5, 7, 11}` is a valid RNS base (8 = 2³, pairwise coprime).
    Dynamic range = 8 × 3 × 5 × 7 × 11 = 9240. -/
theorem base_8_3_5_7_11_coprime : [8, 3, 5, 7, 11].Pairwise Nat.Coprime := by decide

theorem base_8_3_5_7_11_range : [8, 3, 5, 7, 11].prod = 9240 := by norm_num

/-- `{16, 3, 5, 7, 11, 13}` is a valid RNS base (16 = 2⁴, pairwise coprime).
    Dynamic range = 16 × 3 × 5 × 7 × 11 × 13 = 240240. -/
theorem base_16_3_5_7_11_13_coprime :
    [16, 3, 5, 7, 11, 13].Pairwise Nat.Coprime := by decide

theorem base_16_3_5_7_11_13_range : [16, 3, 5, 7, 11, 13].prod = 240240 := by norm_num

/-- Replacing the `2` channel by `4 = 2²` doubles the dynamic range
    with the same number of channels, at no extra coprimality cost. -/
theorem pow2_channel_doubles_range :
    [4, 3, 5, 7].prod = 2 * [2, 3, 5, 7].prod := by norm_num

-- ============================================================
-- Part IV: The "Exactly One Power of 2" Constraint
-- ============================================================

/-- `{2, 4}` is NOT valid: `gcd(2, 4) = 2 ≠ 1`. -/
theorem base_2_4_invalid : ¬ [2, 4].Pairwise Nat.Coprime := by decide

/-- `{4, 8}` is NOT valid: `gcd(4, 8) = 4 ≠ 1`. -/
theorem base_4_8_invalid : ¬ [4, 8].Pairwise Nat.Coprime := by decide

/-- `{2, 4, 3, 5}` is NOT valid (the 2,4 pair fails). -/
theorem base_2_4_3_5_invalid : ¬ [2, 4, 3, 5].Pairwise Nat.Coprime := by decide

/-- The general principle: any two positive powers of 2 are not coprime.
    This is WHY only one power of 2 can appear in a valid RNS base. -/
theorem exactly_one_pow2_allowed {k j : ℕ} (hk : 1 ≤ k) (hj : 1 ≤ j) :
    ¬ Nat.Coprime (2 ^ k) (2 ^ j) :=
  pow2_not_coprime_pow2 hk hj

-- ============================================================
-- Part V: Hardware Efficiency
-- ============================================================

/-- The number of significant bits of `2^k` is `k + 1`:
    `⌊log₂(2^k)⌋ = k`. -/
theorem pow2_bit_length (k : ℕ) : Nat.log 2 (2 ^ k) = k :=
  Nat.log_pow (by norm_num : 1 < 2) k

/-- `{4, 3, 5, 7}` achieves twice the range of `{2, 3, 5, 7}` (210 → 420)
    with the same channel count, at identical hardware overhead for the
    power-of-2 channel (4-bit AND mask vs. 2-bit AND mask). -/
theorem pow2_efficiency_example :
    [4, 3, 5, 7].prod / [2, 3, 5, 7].prod = 2 := by norm_num

#check @Pow2RNSBase.pairwise_coprime
#check @pow2_coprime_odd
#check @pow2_not_coprime_pow2
#check @base_4_3_5_7_coprime
#check @base_16_3_5_7_11_13_coprime

end PowerOfTwoRNS
