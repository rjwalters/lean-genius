/-
  Chinese Remainder Theorem — OQ-03-OQ-02:
  The classic three-moduli RNS set {2^n - 1, 2^n, 2^n + 1}

  ## Question
  What concrete RNS base is the canonical "most efficient" choice for computer
  arithmetic? The parent file `ChineseRemainderConstructiveOQ03` formalizes the
  general efficiency criteria for Residue Number System (RNS) bases (dynamic
  range, channel width, coprimality, Mersenne-friendly moduli). Sibling files
  cover prime-base optimality for all k (OQ-03-OQ-01) and a single power-of-2
  channel alongside odd moduli (OQ-03-OQ-03).

  None of them formalize the single most-cited efficient base in the hardware
  literature: the *balanced three-moduli set*

        { 2^n - 1, 2^n, 2^n + 1 }.

  This is THE textbook answer (Soderstrand et al., "Residue Number System
  Arithmetic", 1986) — three channels each of about n bits, giving a dynamic
  range of about 3n bits, with two of the three moduli admitting trivial
  hardware modular reduction (2^n is a bit-mask, 2^n - 1 is a Mersenne wrap).

  ## What this file delivers (0 axioms, 0 sorries; machine-checked)

  * Pairwise coprimality of {2^n - 1, 2^n, 2^n + 1} for n ≥ 1, broken into the
    three constituent facts:
      - `coprime_low_mid`  : gcd(2^n - 1, 2^n)     = 1  (consecutive integers)
      - `coprime_mid_high` : gcd(2^n, 2^n + 1)     = 1  (consecutive integers)
      - `coprime_low_high` : gcd(2^n - 1, 2^n + 1) = 1  (difference 2, odd ends)
  * The exact dynamic-range formula
        (2^n - 1) · 2^n · (2^n + 1) = 2^(3n) - 2^n          (`dynamicRange_formula`)
    i.e. the three-channel range is one short of a full 3n-bit word per low end.
  * A genuine `RNSBase` instance `threeModuliBase n` for n ≥ 2, with
    `channels = 3` and `dynamicRange = 2^(3n) - 2^n`.
  * A balance bound `2^n + 1 ≤ 2 · (2^n - 1)` (n ≥ 2): the largest and smallest
    channels differ by less than a factor of 2, so the critical path
    (= widest channel) is nearly minimal — the property that makes this base
    "efficient" for hardware.
  * The CRT-reconstruction step lemma `threeModuli_crt_step`:
        gcd( (2^n - 1)·2^n , 2^n + 1 ) = 1,
    which is exactly the coprimality needed to fold the first two channels and
    then reconstruct against the third (iterated two-modulus CRT).
  * Concrete cross-checks for n = 2,3,4: {3,4,5}, {7,8,9}, {15,16,17}.

  ## Four-moduli extension and the parity dichotomy (Section VI)

  Hardware designs frequently extend the three-moduli set to four channels by
  appending one more `(n+1)`-bit modulus. There are two natural candidates,
  `2^(n+1) + 1` and `2^(n+1) - 1`, and a clean *parity dichotomy* governs which
  one is admissible:

  * For ODD n, `{2^n-1, 2^n, 2^n+1, 2^(n+1)+1}` is pairwise coprime
    (`fourModuli_pairwise_coprime_odd`, packaged as `fourModuliBaseOdd`), but the
    other candidate `2^(n+1)-1` FAILS — it shares the factor 3 with `2^n+1`
    (`not_coprime_high_extMersenne_odd`).
  * For EVEN n, `{2^n-1, 2^n, 2^n+1, 2^(n+1)-1}` is pairwise coprime
    (`fourModuli_pairwise_coprime_even`, packaged as `fourModuliBaseEven`), but
    `2^(n+1)+1` FAILS — it shares the factor 3 with `2^n-1`
    (`not_coprime_lowMersenne_extHigh_even`).

  The obstruction is exactly divisibility by 3, controlled by `2^n mod 3`
  (= 2 for odd n, = 1 for even n; `two_pow_mod_three_of_odd/even`). The capstone
  `fourModuli_base_exists` shows every n ≥ 2 admits SOME valid four-channel
  extension — you just pick the modulus matching the parity of n.

  This is a constructive, fully machine-checked characterization of the
  three-moduli set; it does not claim global optimality over all bases (that
  remains the open parent question) — it formalizes why this specific, widely
  used base is valid and balanced.

  Status: VERIFIED (compiles clean against Mathlib 4.26.0 via `lake env lean`;
          `#print axioms` reports only [propext, Classical.choice, Quot.sound])
  Axioms: 0
  Sorries: 0

  References:
  [Sod86]  Soderstrand et al., "Residue Number System Arithmetic" (IEEE, 1986)
  [Gar59]  Garner, "The residue number system" (1959)
  [STK86]  Szabó-Tanaka, "Residue Arithmetic and Its Applications" (1967)

  Tags: number-theory, modular-arithmetic, algorithms, classical
-/

import Mathlib

namespace RNSThreeModuli

open Nat

-- ============================================================
-- SECTION I: Coprimality of the three moduli
-- ============================================================

/-- Consecutive integers are coprime: gcd divides their difference, which is 1. -/
theorem coprime_consecutive (a : ℕ) : Nat.Coprime a (a + 1) := by
  have hsub : Nat.gcd a (a + 1) ∣ (a + 1) - a :=
    Nat.dvd_sub (Nat.gcd_dvd_right a (a + 1)) (Nat.gcd_dvd_left a (a + 1))
  have he : (a + 1) - a = 1 := by omega
  rw [he] at hsub
  exact Nat.dvd_one.mp hsub

/-- Low–mid channel coprimality: `2^n - 1` and `2^n` are consecutive. -/
theorem coprime_low_mid (n : ℕ) : Nat.Coprime (2 ^ n - 1) (2 ^ n) := by
  have ha1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have h := coprime_consecutive (2 ^ n - 1)
  rwa [Nat.sub_add_cancel ha1] at h

/-- Mid–high channel coprimality: `2^n` and `2^n + 1` are consecutive. -/
theorem coprime_mid_high (n : ℕ) : Nat.Coprime (2 ^ n) (2 ^ n + 1) :=
  coprime_consecutive (2 ^ n)

/-- Low–high channel coprimality: `2^n - 1` and `2^n + 1` differ by 2 and both
    ends are odd (`2^n - 1` is odd for n ≥ 1), so any common divisor divides 2
    yet must be odd, hence 1. -/
theorem coprime_low_high (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (2 ^ n - 1) (2 ^ n + 1) := by
  have hpow : 2 ≤ 2 ^ n := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    simpa using this
  have hdl : Nat.gcd (2 ^ n - 1) (2 ^ n + 1) ∣ 2 ^ n - 1 := Nat.gcd_dvd_left _ _
  have hdr : Nat.gcd (2 ^ n - 1) (2 ^ n + 1) ∣ 2 ^ n + 1 := Nat.gcd_dvd_right _ _
  have hd2 : Nat.gcd (2 ^ n - 1) (2 ^ n + 1) ∣ 2 := by
    have hsub := Nat.dvd_sub hdr hdl
    have he : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by omega
    rwa [he] at hsub
  have hodd : ¬ (2 ∣ (2 ^ n - 1)) := by
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
    omega
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
  · exact h1
  · rw [h2] at hdl
    exact absurd hdl hodd

-- ============================================================
-- SECTION II: Dynamic range of the three-moduli set
-- ============================================================

/-- Exact dynamic-range formula for the three-moduli set:
    `(2^n - 1) · 2^n · (2^n + 1) = 2^(3n) - 2^n`.

    Algebraically `a(a-1)(a+1) = a^3 - a` with `a = 2^n`; the natural-number
    subtraction is handled by writing `2^n = k + 1`. -/
theorem dynamicRange_formula (n : ℕ) :
    (2 ^ n - 1) * 2 ^ n * (2 ^ n + 1) = 2 ^ (3 * n) - 2 ^ n := by
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 :=
    ⟨2 ^ n - 1, by have := Nat.one_le_pow n 2 (by norm_num); omega⟩
  have hpow : 2 ^ (3 * n) = (2 ^ n) ^ 3 := by
    rw [show 3 * n = n * 3 from by ring, pow_mul]
  rw [hpow, hk]
  simp only [Nat.add_sub_cancel]
  have key : k * (k + 1) * (k + 1 + 1) + (k + 1) = (k + 1) ^ 3 := by ring
  exact Nat.eq_sub_of_add_eq key

-- ============================================================
-- SECTION III: The three-moduli set as a genuine RNS base
-- ============================================================

/-- An RNS base: pairwise coprime moduli, all ≥ 2 (self-contained; the parent
    `ChineseRemainderConstructiveOQ03` has bit-rotted against current Mathlib). -/
structure RNSBase where
  moduli : List ℕ
  coprime : moduli.Pairwise Nat.Coprime
  ge_two : ∀ m ∈ moduli, 2 ≤ m

/-- Number of channels. -/
def RNSBase.channels (b : RNSBase) : ℕ := b.moduli.length

/-- Dynamic range = product of the moduli. -/
def RNSBase.dynamicRange (b : RNSBase) : ℕ := b.moduli.prod

/-- The three moduli `{2^n - 1, 2^n, 2^n + 1}` are pairwise coprime (n ≥ 1). -/
theorem threeModuli_pairwise_coprime (n : ℕ) (hn : 1 ≤ n) :
    [2 ^ n - 1, 2 ^ n, 2 ^ n + 1].Pairwise Nat.Coprime := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil))
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact coprime_low_mid n
    · rcases List.mem_singleton.mp ha' with rfl
      exact coprime_low_high n hn
  · intro a ha
    rcases List.mem_singleton.mp ha with rfl
    exact coprime_mid_high n
  · intro a ha
    simp at ha

/-- The three-moduli RNS base for n ≥ 2 (so that `2^n - 1 ≥ 3 ≥ 2`). -/
def threeModuliBase (n : ℕ) (hn : 2 ≤ n) : RNSBase where
  moduli := [2 ^ n - 1, 2 ^ n, 2 ^ n + 1]
  coprime := threeModuli_pairwise_coprime n (by omega)
  ge_two := by
    have hpow : 4 ≤ 2 ^ n := by
      have : (2 : ℕ) ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      simpa using this
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · omega
    · rcases List.mem_cons.mp hm' with rfl | hm''
      · omega
      · rcases List.mem_singleton.mp hm'' with rfl
        omega

/-- The three-moduli base has exactly 3 channels. -/
theorem threeModuliBase_channels (n : ℕ) (hn : 2 ≤ n) :
    (threeModuliBase n hn).channels = 3 := rfl

/-- The three-moduli base realizes the dynamic range `2^(3n) - 2^n`. -/
theorem threeModuliBase_dynamicRange (n : ℕ) (hn : 2 ≤ n) :
    (threeModuliBase n hn).dynamicRange = 2 ^ (3 * n) - 2 ^ n := by
  show ([2 ^ n - 1, 2 ^ n, 2 ^ n + 1] : List ℕ).prod = 2 ^ (3 * n) - 2 ^ n
  simp only [List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_assoc]
  exact dynamicRange_formula n

-- ============================================================
-- SECTION IV: Balance and reconstruction structure
-- ============================================================

/-- Balance property: the widest channel `2^n + 1` is less than twice the
    narrowest channel `2^n - 1` (for n ≥ 2). A balanced base minimizes the
    critical-path channel width for a given dynamic range — the reason the
    three-moduli set is favored in hardware. -/
theorem threeModuli_balanced (n : ℕ) (hn : 2 ≤ n) :
    2 ^ n + 1 ≤ 2 * (2 ^ n - 1) := by
  have hpow : 4 ≤ 2 ^ n := by
    have : (2 : ℕ) ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    simpa using this
  omega

/-- CRT reconstruction step: the product of the first two channels is coprime
    to the third. This is precisely the hypothesis that lets one combine the
    `2^n - 1` and `2^n` residues into a single residue mod `(2^n - 1)·2^n` and
    then apply two-modulus CRT against `2^n + 1`. -/
theorem threeModuli_crt_step (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime ((2 ^ n - 1) * 2 ^ n) (2 ^ n + 1) :=
  Nat.Coprime.mul_left (coprime_low_high n hn) (coprime_mid_high n)

-- ============================================================
-- SECTION V: Concrete cross-checks (n = 2, 3, 4)
-- ============================================================

/-- n = 2: the base is {3, 4, 5}. -/
theorem threeModuliBase_two_eq : (threeModuliBase 2 (by norm_num)).moduli = [3, 4, 5] := by
  decide

theorem example_n2_coprime : [3, 4, 5].Pairwise Nat.Coprime := by decide
theorem example_n2_range : ([3, 4, 5] : List ℕ).prod = 60 := by norm_num
theorem example_n2_range_formula : 2 ^ (3 * 2) - 2 ^ 2 = 60 := by norm_num

theorem example_n3_coprime : [7, 8, 9].Pairwise Nat.Coprime := by decide
theorem example_n3_range : ([7, 8, 9] : List ℕ).prod = 504 := by norm_num
theorem example_n3_range_formula : 2 ^ (3 * 3) - 2 ^ 3 = 504 := by norm_num

theorem example_n4_coprime : [15, 16, 17].Pairwise Nat.Coprime := by decide
theorem example_n4_range : ([15, 16, 17] : List ℕ).prod = 4080 := by norm_num
theorem example_n4_range_formula : 2 ^ (3 * 4) - 2 ^ 4 = 4080 := by norm_num

-- ============================================================
-- SECTION VI: Four-moduli extensions and the parity dichotomy
-- ============================================================

/-- `2^n mod 3 = 2` when n is odd: `2 ≡ -1 (mod 3)`, so odd powers are `≡ -1`. -/
theorem two_pow_mod_three_of_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨m, rfl⟩ := hn
  have hb : ((2 : ℕ) ^ 2) ≡ 1 [MOD 3] := by decide
  have h4 : ((2 : ℕ) ^ 2) ^ m % 3 = 1 := by
    have := hb.pow m; simpa [Nat.ModEq] using this
  calc 2 ^ (2 * m + 1) % 3
      = ((2 : ℕ) ^ 2) ^ m * 2 % 3 := by rw [pow_succ, pow_mul]
    _ = (((2 : ℕ) ^ 2) ^ m % 3) * (2 % 3) % 3 := by rw [Nat.mul_mod]
    _ = 2 := by rw [h4]

/-- `2^n mod 3 = 1` when n is even: `2 ≡ -1 (mod 3)`, so even powers are `≡ 1`. -/
theorem two_pow_mod_three_of_even {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have hb : ((2 : ℕ) ^ 2) ≡ 1 [MOD 3] := by decide
  have h4 : ((2 : ℕ) ^ 2) ^ m % 3 = 1 := by
    have := hb.pow m; simpa [Nat.ModEq] using this
  calc 2 ^ (m + m) % 3
      = ((2 : ℕ) ^ 2) ^ m % 3 := by rw [show m + m = 2 * m from by ring, pow_mul]
    _ = 1 := h4

/-- Any common divisor of `2^n - 1` and `2^(n+1) + 1` divides 3:
    `(2^(n+1)+1) - 2·(2^n-1) = 3`. -/
theorem gcd_lowMersenne_extHigh_dvd_three (n : ℕ) :
    Nat.gcd (2 ^ n - 1) (2 ^ (n + 1) + 1) ∣ 3 := by
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have ha1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hdl := Nat.gcd_dvd_left (2 ^ n - 1) (2 ^ (n + 1) + 1)
  have hdr := Nat.gcd_dvd_right (2 ^ n - 1) (2 ^ (n + 1) + 1)
  have h2 : Nat.gcd (2 ^ n - 1) (2 ^ (n + 1) + 1) ∣ 2 * (2 ^ n - 1) := hdl.mul_left 2
  have he : 2 ^ (n + 1) + 1 - 2 * (2 ^ n - 1) = 3 := by rw [hpow]; omega
  have hsub := Nat.dvd_sub hdr h2
  rwa [he] at hsub

/-- Any common divisor of `2^n + 1` and `2^(n+1) - 1` divides 3:
    `2·(2^n+1) - (2^(n+1)-1) = 3`. -/
theorem gcd_high_extMersenne_dvd_three (n : ℕ) :
    Nat.gcd (2 ^ n + 1) (2 ^ (n + 1) - 1) ∣ 3 := by
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have ha1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hdl := Nat.gcd_dvd_left (2 ^ n + 1) (2 ^ (n + 1) - 1)
  have hdr := Nat.gcd_dvd_right (2 ^ n + 1) (2 ^ (n + 1) - 1)
  have h2 : Nat.gcd (2 ^ n + 1) (2 ^ (n + 1) - 1) ∣ 2 * (2 ^ n + 1) := hdl.mul_left 2
  have he : 2 * (2 ^ n + 1) - (2 ^ (n + 1) - 1) = 3 := by rw [hpow]; omega
  have hsub := Nat.dvd_sub h2 hdr
  rwa [he] at hsub

/-- ODD n: the extended-high modulus `2^(n+1)+1` is coprime to `2^n - 1`.
    The gcd divides 3, but `3 ∤ 2^n-1` for odd n (`2^n ≡ 2 mod 3`). -/
theorem coprime_lowMersenne_extHigh_odd (n : ℕ) (hn : Odd n) :
    Nat.Coprime (2 ^ n - 1) (2 ^ (n + 1) + 1) := by
  have hd3 := gcd_lowMersenne_extHigh_dvd_three n
  have hmod : 2 ^ n % 3 = 2 := two_pow_mod_three_of_odd hn
  have hge : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hnot3 : ¬ Nat.gcd (2 ^ n - 1) (2 ^ (n + 1) + 1) = 3 := by
    intro hg
    have h3 : (3 : ℕ) ∣ 2 ^ n - 1 := by rw [← hg]; exact Nat.gcd_dvd_left _ _
    omega
  rcases (Nat.dvd_prime (by norm_num)).mp hd3 with h1 | h3
  · exact h1
  · exact absurd h3 hnot3

/-- `2^(n+1)+1` is coprime to the mid channel `2^n` (consecutive-to-double). -/
theorem coprime_mid_extHigh (n : ℕ) : Nat.Coprime (2 ^ n) (2 ^ (n + 1) + 1) := by
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hdl := Nat.gcd_dvd_left (2 ^ n) (2 ^ (n + 1) + 1)
  have hdr := Nat.gcd_dvd_right (2 ^ n) (2 ^ (n + 1) + 1)
  have h2 : Nat.gcd (2 ^ n) (2 ^ (n + 1) + 1) ∣ 2 ^ (n + 1) := by
    have := hdl.mul_left 2; rwa [← hpow] at this
  have he : 2 ^ (n + 1) + 1 - 2 ^ (n + 1) = 1 := by omega
  have hsub := Nat.dvd_sub hdr h2
  rw [he] at hsub
  exact Nat.dvd_one.mp hsub

/-- `2^(n+1)+1` is coprime to the high channel `2^n + 1`:
    `2·(2^n+1) - (2^(n+1)+1) = 1`. -/
theorem coprime_high_extHigh (n : ℕ) : Nat.Coprime (2 ^ n + 1) (2 ^ (n + 1) + 1) := by
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hdl := Nat.gcd_dvd_left (2 ^ n + 1) (2 ^ (n + 1) + 1)
  have hdr := Nat.gcd_dvd_right (2 ^ n + 1) (2 ^ (n + 1) + 1)
  have h2 : Nat.gcd (2 ^ n + 1) (2 ^ (n + 1) + 1) ∣ 2 * (2 ^ n + 1) := hdl.mul_left 2
  have he : 2 * (2 ^ n + 1) - (2 ^ (n + 1) + 1) = 1 := by rw [hpow]; omega
  have hsub := Nat.dvd_sub h2 hdr
  rw [he] at hsub
  exact Nat.dvd_one.mp hsub

/-- `2^(n+1)-1` is coprime to the low channel `2^n - 1` (for all n):
    `(2^(n+1)-1) - 2·(2^n-1) = 1`. -/
theorem coprime_lowMersenne_extMersenne (n : ℕ) :
    Nat.Coprime (2 ^ n - 1) (2 ^ (n + 1) - 1) := by
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have ha1 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have hdl := Nat.gcd_dvd_left (2 ^ n - 1) (2 ^ (n + 1) - 1)
  have hdr := Nat.gcd_dvd_right (2 ^ n - 1) (2 ^ (n + 1) - 1)
  have h2 : Nat.gcd (2 ^ n - 1) (2 ^ (n + 1) - 1) ∣ 2 * (2 ^ n - 1) := hdl.mul_left 2
  have he : 2 ^ (n + 1) - 1 - 2 * (2 ^ n - 1) = 1 := by rw [hpow]; omega
  have hsub := Nat.dvd_sub hdr h2
  rw [he] at hsub
  exact Nat.dvd_one.mp hsub

/-- `2^(n+1)-1` is coprime to the mid channel `2^n` (for all n):
    `2^(n+1) - (2^(n+1)-1) = 1`. -/
theorem coprime_mid_extMersenne (n : ℕ) : Nat.Coprime (2 ^ n) (2 ^ (n + 1) - 1) := by
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have ha1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
  have hdl := Nat.gcd_dvd_left (2 ^ n) (2 ^ (n + 1) - 1)
  have hdr := Nat.gcd_dvd_right (2 ^ n) (2 ^ (n + 1) - 1)
  have h2 : Nat.gcd (2 ^ n) (2 ^ (n + 1) - 1) ∣ 2 ^ (n + 1) := by
    have := hdl.mul_left 2; rwa [← hpow] at this
  have he : 2 ^ (n + 1) - (2 ^ (n + 1) - 1) = 1 := by omega
  have hsub := Nat.dvd_sub h2 hdr
  rw [he] at hsub
  exact Nat.dvd_one.mp hsub

/-- EVEN n: the extended-Mersenne modulus `2^(n+1)-1` is coprime to `2^n + 1`.
    The gcd divides 3, but `3 ∤ 2^n+1` for even n (`2^n ≡ 1 mod 3`). -/
theorem coprime_high_extMersenne_even (n : ℕ) (hn : Even n) :
    Nat.Coprime (2 ^ n + 1) (2 ^ (n + 1) - 1) := by
  have hd3 := gcd_high_extMersenne_dvd_three n
  have hmod : 2 ^ n % 3 = 1 := two_pow_mod_three_of_even hn
  have hnot3 : ¬ Nat.gcd (2 ^ n + 1) (2 ^ (n + 1) - 1) = 3 := by
    intro hg
    have h3 : (3 : ℕ) ∣ 2 ^ n + 1 := by rw [← hg]; exact Nat.gcd_dvd_left _ _
    omega
  rcases (Nat.dvd_prime (by norm_num)).mp hd3 with h1 | h3
  · exact h1
  · exact absurd h3 hnot3

/-- Sharp boundary (odd ↛ Mersenne): for ODD n, `2^(n+1)-1` is NOT coprime to
    `2^n+1` — both are divisible by 3 — so this extension fails at odd n. -/
theorem not_coprime_high_extMersenne_odd (n : ℕ) (hn : Odd n) :
    ¬ Nat.Coprime (2 ^ n + 1) (2 ^ (n + 1) - 1) := by
  have hmodO : 2 ^ n % 3 = 2 := two_pow_mod_three_of_odd hn
  have h1 : (3 : ℕ) ∣ 2 ^ n + 1 := by omega
  have hmodE : 2 ^ (n + 1) % 3 = 1 := two_pow_mod_three_of_even (Odd.add_one hn)
  have hge : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
  have h2 : (3 : ℕ) ∣ 2 ^ (n + 1) - 1 := by omega
  intro hco
  have hco' : Nat.gcd (2 ^ n + 1) (2 ^ (n + 1) - 1) = 1 := hco
  have hg : (3 : ℕ) ∣ Nat.gcd (2 ^ n + 1) (2 ^ (n + 1) - 1) := Nat.dvd_gcd h1 h2
  rw [hco'] at hg
  exact absurd hg (by norm_num)

/-- Sharp boundary (even ↛ extended-high): for EVEN n, `2^(n+1)+1` is NOT coprime
    to `2^n-1` — both are divisible by 3 — so this extension fails at even n. -/
theorem not_coprime_lowMersenne_extHigh_even (n : ℕ) (hn : Even n) :
    ¬ Nat.Coprime (2 ^ n - 1) (2 ^ (n + 1) + 1) := by
  have hmodE : 2 ^ n % 3 = 1 := two_pow_mod_three_of_even hn
  have hge : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
  have h1 : (3 : ℕ) ∣ 2 ^ n - 1 := by omega
  have hmodO : 2 ^ (n + 1) % 3 = 2 := two_pow_mod_three_of_odd (Even.add_one hn)
  have h2 : (3 : ℕ) ∣ 2 ^ (n + 1) + 1 := by omega
  intro hco
  have hco' : Nat.gcd (2 ^ n - 1) (2 ^ (n + 1) + 1) = 1 := hco
  have hg : (3 : ℕ) ∣ Nat.gcd (2 ^ n - 1) (2 ^ (n + 1) + 1) := Nat.dvd_gcd h1 h2
  rw [hco'] at hg
  exact absurd hg (by norm_num)

/-- ODD n: the four-moduli set `{2^n-1, 2^n, 2^n+1, 2^(n+1)+1}` is pairwise coprime. -/
theorem fourModuli_pairwise_coprime_odd (n : ℕ) (hn : Odd n) :
    [2 ^ n - 1, 2 ^ n, 2 ^ n + 1, 2 ^ (n + 1) + 1].Pairwise Nat.Coprime := by
  have hpos : 1 ≤ n := by obtain ⟨k, hk⟩ := hn; omega
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)))
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha1
    · exact coprime_low_mid n
    · rcases List.mem_cons.mp ha1 with rfl | ha2
      · exact coprime_low_high n hpos
      · rcases List.mem_singleton.mp ha2 with rfl
        exact coprime_lowMersenne_extHigh_odd n hn
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha1
    · exact coprime_mid_high n
    · rcases List.mem_singleton.mp ha1 with rfl
      exact coprime_mid_extHigh n
  · intro a ha
    rcases List.mem_singleton.mp ha with rfl
    exact coprime_high_extHigh n
  · intro a ha
    simp at ha

/-- EVEN n: the four-moduli set `{2^n-1, 2^n, 2^n+1, 2^(n+1)-1}` is pairwise coprime. -/
theorem fourModuli_pairwise_coprime_even (n : ℕ) (hn : Even n) (hpos : 1 ≤ n) :
    [2 ^ n - 1, 2 ^ n, 2 ^ n + 1, 2 ^ (n + 1) - 1].Pairwise Nat.Coprime := by
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_
    (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)))
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha1
    · exact coprime_low_mid n
    · rcases List.mem_cons.mp ha1 with rfl | ha2
      · exact coprime_low_high n hpos
      · rcases List.mem_singleton.mp ha2 with rfl
        exact coprime_lowMersenne_extMersenne n
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha1
    · exact coprime_mid_high n
    · rcases List.mem_singleton.mp ha1 with rfl
      exact coprime_mid_extMersenne n
  · intro a ha
    rcases List.mem_singleton.mp ha with rfl
    exact coprime_high_extMersenne_even n hn
  · intro a ha
    simp at ha

/-- The ODD-n four-moduli RNS base `{2^n-1, 2^n, 2^n+1, 2^(n+1)+1}` (n ≥ 2). -/
def fourModuliBaseOdd (n : ℕ) (hn : Odd n) (hn2 : 2 ≤ n) : RNSBase where
  moduli := [2 ^ n - 1, 2 ^ n, 2 ^ n + 1, 2 ^ (n + 1) + 1]
  coprime := fourModuli_pairwise_coprime_odd n hn
  ge_two := by
    have hpow : 4 ≤ 2 ^ n := by
      have : (2 : ℕ) ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      simpa using this
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · omega
    · rcases List.mem_cons.mp hm' with rfl | hm''
      · omega
      · rcases List.mem_cons.mp hm'' with rfl | hm'''
        · omega
        · rcases List.mem_singleton.mp hm''' with rfl
          have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_pow _ _ (by norm_num)
          omega

/-- The EVEN-n four-moduli RNS base `{2^n-1, 2^n, 2^n+1, 2^(n+1)-1}` (n ≥ 2). -/
def fourModuliBaseEven (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) : RNSBase where
  moduli := [2 ^ n - 1, 2 ^ n, 2 ^ n + 1, 2 ^ (n + 1) - 1]
  coprime := fourModuli_pairwise_coprime_even n hn (by omega)
  ge_two := by
    have hpow : 4 ≤ 2 ^ n := by
      have : (2 : ℕ) ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      simpa using this
    intro m hm
    rcases List.mem_cons.mp hm with rfl | hm'
    · omega
    · rcases List.mem_cons.mp hm' with rfl | hm''
      · omega
      · rcases List.mem_cons.mp hm'' with rfl | hm'''
        · omega
        · rcases List.mem_singleton.mp hm''' with rfl
          have h1 : 4 ≤ 2 ^ (n + 1) := by
            have : (2 : ℕ) ^ 2 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
            simpa using this
          omega

theorem fourModuliBaseOdd_channels (n : ℕ) (hn : Odd n) (hn2 : 2 ≤ n) :
    (fourModuliBaseOdd n hn hn2).channels = 4 := rfl

theorem fourModuliBaseEven_channels (n : ℕ) (hn : Even n) (hn2 : 2 ≤ n) :
    (fourModuliBaseEven n hn hn2).channels = 4 := rfl

/-- Parity dichotomy capstone: every n ≥ 2 admits SOME valid four-channel RNS
    extension of the three-moduli set — use `2^(n+1)+1` when n is odd and
    `2^(n+1)-1` when n is even. -/
theorem fourModuli_base_exists (n : ℕ) (hn2 : 2 ≤ n) :
    ∃ b : RNSBase, b.channels = 4 := by
  rcases Nat.even_or_odd n with he | ho
  · exact ⟨fourModuliBaseEven n he hn2, fourModuliBaseEven_channels n he hn2⟩
  · exact ⟨fourModuliBaseOdd n ho hn2, fourModuliBaseOdd_channels n ho hn2⟩

-- Concrete cross-checks for the parity dichotomy.
-- n = 3 (odd): {7,8,9,17} works; {7,8,9,15} fails (gcd(9,15) = 3).
theorem example_n3_four_odd : [7, 8, 9, 17].Pairwise Nat.Coprime := by decide
theorem example_n3_bad_mersenne_choice : ¬ [7, 8, 9, 15].Pairwise Nat.Coprime := by decide
-- n = 2 (even): {3,4,5,7} works; {3,4,5,9} fails (gcd(3,9) = 3).
theorem example_n2_four_even : [3, 4, 5, 7].Pairwise Nat.Coprime := by decide
theorem example_n2_bad_high_choice : ¬ [3, 4, 5, 9].Pairwise Nat.Coprime := by decide
-- n = 4 (even): {15,16,17,31} works.
theorem example_n4_four_even : [15, 16, 17, 31].Pairwise Nat.Coprime := by decide

#check @threeModuli_pairwise_coprime
#check @dynamicRange_formula
#check @threeModuliBase_dynamicRange
#check @threeModuli_crt_step
#check @fourModuli_pairwise_coprime_odd
#check @fourModuli_pairwise_coprime_even
#check @fourModuli_base_exists
#check @two_pow_mod_three_of_odd

end RNSThreeModuli
