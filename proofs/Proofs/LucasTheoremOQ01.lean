import Mathlib

/-!
# Lucas' Theorem and Glaisher's Count of Odd Binomial Coefficients

To reduce a binomial coefficient `C(m, n)` modulo a prime `p`, Lucas' theorem writes
both `m` and `n` in base `p` and multiplies the digit-wise binomial coefficients:
`C(m, n) ≡ ∏ᵢ C(mᵢ, nᵢ)  (mod p)`.  The bare statement is already in Mathlib
(`Mathlib.Data.Nat.Choose.Lucas`); we re-export it here as `lucas_theorem` and record
the single-step recursion `lucas_mod_two` for the prime `2`.

The substantive new content is the classical **mod-2 consequence**
(Glaisher, 1899): the number of *odd* entries in row `n` of Pascal's triangle is a
power of two, namely

> `oddCount n = 2 ^ s₂(n)`,

where `s₂(n)` is the number of `1`'s in the binary expansion of `n` (the binary
digit sum).  Concretely, row `5 = 101₂` has `s₂ = 2`, and indeed `1 5 10 10 5 1`
contains exactly `2² = 4` odd entries.

The engine is Lucas mod `2`, which over the digit `{0,1}` collapses to the doubling
recursion

* `oddCount_two_mul`         : `oddCount (2n)     = oddCount n`,
* `oddCount_two_mul_add_one` : `oddCount (2n + 1) = 2 · oddCount n`,

mirroring the binary-digit-sum recursion `s₂(2n) = s₂(n)`, `s₂(2n+1) = s₂(n) + 1`.
A strong induction then yields the closed form, and the corollary `oddCount_isPowerOfTwo`
records that every row contains a power-of-two number of odd entries.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

open Nat Finset

namespace LucasOddEntries

/-- `s₂ n` is the binary digit sum of `n` — the number of `1`'s in its base-2
expansion (since every base-2 digit is `0` or `1`). -/
def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

/-- The set of column indices `k ≤ n` for which `C(n, k)` is odd. -/
def oddRow (n : ℕ) : Finset ℕ := (range (n + 1)).filter (fun k => Odd (n.choose k))

/-- The number of odd entries in row `n` of Pascal's triangle. -/
def oddCount (n : ℕ) : ℕ := (oddRow n).card

/-! ## Lucas' theorem (re-export from Mathlib) -/

/-- **Lucas' theorem** (digit-product form), re-exported from Mathlib: for a prime `p`,
a binomial coefficient is the product over base-`p` digits of the digit-wise binomial
coefficients, modulo `p`. -/
theorem lucas_theorem {p : ℕ} [Fact p.Prime] {n k a : ℕ} (hn : n < p ^ a) (hk : k < p ^ a) :
    n.choose k ≡ ∏ i ∈ range a, (n / p ^ i % p).choose (k / p ^ i % p) [MOD p] :=
  Choose.lucas_theorem_nat hn hk

/-- The single base-`2` step of Lucas' theorem. -/
theorem lucas_mod_two (n k : ℕ) :
    n.choose k ≡ (n % 2).choose (k % 2) * (n / 2).choose (k / 2) [MOD 2] := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

/-! ## Pointwise parity of binomial coefficients via Lucas mod 2 -/

/-- `C(2n, k)` is odd iff `k` is even and `C(n, k/2)` is odd.  (Lucas mod 2 with the
top digit `0`: `C(0, 1) = 0` kills the odd-`k` case.) -/
theorem odd_choose_two_mul (n k : ℕ) :
    Odd ((2 * n).choose k) ↔ k % 2 = 0 ∧ Odd (n.choose (k / 2)) := by
  have h := lucas_mod_two (2 * n) k
  have e1 : (2 * n) % 2 = 0 := by omega
  have e2 : (2 * n) / 2 = n := by omega
  rw [e1, e2] at h
  have h' : (2 * n).choose k % 2 = (Nat.choose 0 (k % 2) * n.choose (k / 2)) % 2 := h
  rw [Nat.odd_iff, h']
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> rw [hk]
  · simp [Nat.odd_iff]
  · rw [Nat.choose_eq_zero_of_lt (by norm_num : (0 : ℕ) < 1)]; simp

/-- `C(2n+1, k)` is odd iff `C(n, k/2)` is odd, *regardless of the parity of `k`*.
(Lucas mod 2 with the top digit `1`: both `C(1,0)` and `C(1,1)` equal `1`.) -/
theorem odd_choose_two_mul_add_one (n k : ℕ) :
    Odd ((2 * n + 1).choose k) ↔ Odd (n.choose (k / 2)) := by
  have h := lucas_mod_two (2 * n + 1) k
  have e1 : (2 * n + 1) % 2 = 1 := by omega
  have e2 : (2 * n + 1) / 2 = n := by omega
  rw [e1, e2] at h
  have h' : (2 * n + 1).choose k % 2 = (Nat.choose 1 (k % 2) * n.choose (k / 2)) % 2 := h
  rw [Nat.odd_iff, h']
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> rw [hk]
  · simp [Nat.odd_iff]
  · simp [Nat.choose_self, Nat.odd_iff]

/-! ## The doubling recursion for `oddCount` -/

/-- Doubling the row index leaves the odd-entry count unchanged. -/
theorem oddCount_two_mul (n : ℕ) : oddCount (2 * n) = oddCount n := by
  have himg : oddRow (2 * n) = (oddRow n).image (fun j => 2 * j) := by
    ext k
    simp only [oddRow, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hk, hodd⟩
      rw [odd_choose_two_mul] at hodd
      obtain ⟨hk2, hoddk⟩ := hodd
      exact ⟨k / 2, ⟨by omega, hoddk⟩, by omega⟩
    · rintro ⟨j, ⟨hj, hoddj⟩, rfl⟩
      refine ⟨by omega, ?_⟩
      rw [odd_choose_two_mul]
      refine ⟨by omega, ?_⟩
      have : 2 * j / 2 = j := by omega
      rwa [this]
  unfold oddCount
  rw [himg]
  exact Finset.card_image_of_injective _ (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0))

/-- Doubling-plus-one doubles the odd-entry count. -/
theorem oddCount_two_mul_add_one (n : ℕ) : oddCount (2 * n + 1) = 2 * oddCount n := by
  have inj1 : Function.Injective (fun j : ℕ => 2 * j) :=
    mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)
  have inj2 : Function.Injective (fun j : ℕ => 2 * j + 1) := by
    intro a b hab
    have : 2 * a + 1 = 2 * b + 1 := hab
    omega
  have hdisj : Disjoint ((oddRow n).image (fun j => 2 * j))
      ((oddRow n).image (fun j => 2 * j + 1)) := by
    rw [Finset.disjoint_left]
    rintro a ha hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨j, _, rfl⟩ := ha
    obtain ⟨i, _, hi⟩ := hb
    omega
  have himg : oddRow (2 * n + 1)
      = (oddRow n).image (fun j => 2 * j) ∪ (oddRow n).image (fun j => 2 * j + 1) := by
    ext k
    simp only [oddRow, Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hk, hodd⟩
      rw [odd_choose_two_mul_add_one] at hodd
      rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
      · exact Or.inl ⟨k / 2, ⟨by omega, hodd⟩, by omega⟩
      · exact Or.inr ⟨k / 2, ⟨by omega, hodd⟩, by omega⟩
    · rintro (⟨j, ⟨hj, hoddj⟩, rfl⟩ | ⟨j, ⟨hj, hoddj⟩, rfl⟩)
      · refine ⟨by omega, ?_⟩
        rw [odd_choose_two_mul_add_one]
        have : 2 * j / 2 = j := by omega
        rwa [this]
      · refine ⟨by omega, ?_⟩
        rw [odd_choose_two_mul_add_one]
        have : (2 * j + 1) / 2 = j := by omega
        rwa [this]
  unfold oddCount
  rw [himg, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ inj1, Finset.card_image_of_injective _ inj2]
  ring

/-! ## The binary digit sum and its recursion -/

theorem s2_zero : s2 0 = 0 := by simp [s2]

/-- One step of the binary-digit-sum recursion. -/
theorem s2_pos (n : ℕ) (hn : 0 < n) : s2 n = n % 2 + s2 (n / 2) := by
  unfold s2
  rw [Nat.digits_def' (by norm_num : 1 < 2) hn, List.sum_cons]

/-! ## Glaisher's closed form -/

/-- **Glaisher's theorem.** The number of odd entries in row `n` of Pascal's triangle
equals `2 ^ s₂(n)`, where `s₂(n)` is the number of `1`'s in the binary expansion of `n`. -/
theorem oddCount_eq_two_pow_s2 (n : ℕ) : oddCount n = 2 ^ s2 n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [s2_zero]; decide
    · rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
      · -- n even
        have hn2 : n = 2 * (n / 2) := by omega
        have hlt : n / 2 < n := by omega
        calc oddCount n = oddCount (2 * (n / 2)) := by rw [← hn2]
          _ = oddCount (n / 2) := oddCount_two_mul _
          _ = 2 ^ s2 (n / 2) := ih _ hlt
          _ = 2 ^ s2 n := by rw [s2_pos n hn, h2, Nat.zero_add]
      · -- n odd
        have hn2 : n = 2 * (n / 2) + 1 := by omega
        have hlt : n / 2 < n := by omega
        calc oddCount n = oddCount (2 * (n / 2) + 1) := by rw [← hn2]
          _ = 2 * oddCount (n / 2) := oddCount_two_mul_add_one _
          _ = 2 * 2 ^ s2 (n / 2) := by rw [ih _ hlt]
          _ = 2 ^ (s2 (n / 2) + 1) := by rw [pow_succ]; ring
          _ = 2 ^ s2 n := by rw [s2_pos n hn, h2, Nat.add_comm 1 (s2 (n / 2))]

/-- Every row of Pascal's triangle contains a power-of-two number of odd entries. -/
theorem oddCount_isPowerOfTwo (n : ℕ) : ∃ m, oddCount n = 2 ^ m :=
  ⟨s2 n, oddCount_eq_two_pow_s2 n⟩

/-! ## Sanity checks -/

/-- Row `5 = 101₂` (`s₂ = 2`) has `2² = 4` odd entries: `1 5 10 10 5 1`. -/
example : oddCount 5 = 4 := by decide

/-- Row `4 = 100₂` (`s₂ = 1`) has `2¹ = 2` odd entries: `1 4 6 4 1`. -/
example : oddCount 4 = 2 := by decide

/-- Row `7 = 111₂` (`s₂ = 3`) is entirely odd: `2³ = 8` entries. -/
example : oddCount 7 = 8 := by decide

end LucasOddEntries
