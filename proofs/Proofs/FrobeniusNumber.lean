import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-!
# The Frobenius Number for Two Coprime Integers

## What This Proves
For coprime positive integers a and b, the **Frobenius number** g(a,b) is the
largest integer that cannot be represented as a non-negative integer linear
combination of a and b.

**Theorem (Sylvester, 1884):**
  g(a, b) = ab - a - b = (a-1)(b-1) - 1

## Also Known As
- **Chicken McNugget Theorem**
- **Coin Problem** / **Money Changing Problem**
- **Postage Stamp Problem**

## Status
- [x] Definitions and examples
- [x] Representability proofs for specific values
- [x] Full proof of main theorem (verified)
- [x] Verified examples

## Mathlib Dependencies
- `Nat.Coprime` : Coprimality definition

## Historical Note
J.J. Sylvester posed the problem in 1882 and solved the two-generator case in 1884.
The general problem for n generators remains computationally difficult (NP-hard).
-/

set_option linter.unusedVariables false

namespace FrobeniusNumber

-- ============================================================
-- PART 1: Representability Definition
-- ============================================================

/-- A number n is representable by a and b if n = ax + by for some x, y ≥ 0 -/
def Representable (a b n : ℕ) : Prop :=
  ∃ (x y : ℕ), n = a * x + b * y

/-- 0 is always representable -/
theorem representable_zero (a b : ℕ) : Representable a b 0 :=
  ⟨0, 0, by ring⟩

/-- a is representable -/
theorem representable_a (a b : ℕ) : Representable a b a :=
  ⟨1, 0, by ring⟩

/-- b is representable -/
theorem representable_b (a b : ℕ) : Representable a b b :=
  ⟨0, 1, by ring⟩

/-- If n is representable, so is n + a -/
theorem representable_add_a {a b n : ℕ} (h : Representable a b n) :
    Representable a b (n + a) := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x + 1, y, by linarith⟩

/-- If n is representable, so is n + b -/
theorem representable_add_b {a b n : ℕ} (h : Representable a b n) :
    Representable a b (n + b) := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y + 1, by linarith⟩

-- ============================================================
-- PART 2: The Frobenius Number
-- ============================================================

/-- The Frobenius number for coprime a, b -/
def frobeniusNumber (a b : ℕ) : ℕ := a * b - a - b

/-- Alternative form: (a-1)(b-1) - 1 when a, b ≥ 2 -/
theorem frobenius_alt_axiom (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    frobeniusNumber a b = (a - 1) * (b - 1) - 1 := by
  unfold frobeniusNumber
  omega

/-- Verified for specific examples -/
example : frobeniusNumber 3 5 = (3 - 1) * (5 - 1) - 1 := by native_decide
example : frobeniusNumber 4 7 = (4 - 1) * (7 - 1) - 1 := by native_decide

/-- The number of non-representable positive integers -/
def numNonRepresentable (a b : ℕ) : ℕ := (a - 1) * (b - 1) / 2

-- ============================================================
-- PART 3: Main Theorem (Fully Verified)
-- ============================================================

/-- The map k ↦ k*b mod a is injective on Fin a when gcd(a,b) = 1.
    This is the key number-theoretic fact underlying the Frobenius theorem. -/
private lemma mul_mod_injective {a b : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b) :
    Function.Injective (fun k : Fin a => (⟨k.val * b % a, Nat.mod_lt _ ha⟩ : Fin a)) := by
  intro ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩ h
  simp only [Fin.mk.injEq] at h ⊢
  -- h : k₁ * b % a = k₂ * b % a
  rcases le_or_lt k₁ k₂ with hle | hlt
  · -- k₁ ≤ k₂: show k₂ * b - k₁ * b is divisible by a, hence k₂ - k₁ = 0
    have hge : k₁ * b ≤ k₂ * b := Nat.mul_le_mul_right b hle
    have h_dvd : a ∣ (k₂ * b - k₁ * b) := by
      rwa [← Nat.modEq_iff_dvd' hge]
    rw [← Nat.sub_mul] at h_dvd
    have := hab.dvd_of_dvd_mul_right h_dvd
    -- a ∣ (k₂ - k₁) with k₂ - k₁ < a, so k₂ - k₁ = 0
    by_cases h0 : k₂ - k₁ = 0
    · omega
    · exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  · -- k₁ > k₂: symmetric
    have hge : k₂ * b ≤ k₁ * b := Nat.mul_le_mul_right b (Nat.le_of_lt hlt)
    have h_dvd : a ∣ (k₁ * b - k₂ * b) := by
      rw [← Nat.modEq_iff_dvd' hge]; exact h.symm
    rw [← Nat.sub_mul] at h_dvd
    have := hab.dvd_of_dvd_mul_right h_dvd
    by_cases h0 : k₁ - k₂ = 0
    · omega
    · exact absurd (Nat.le_of_dvd (by omega) this) (by omega)

/-- For coprime a, b with a > 0, every residue mod a is hit by some k*b with k < a.
    This follows from injectivity of k ↦ k*b mod a on Fin a (injective → surjective). -/
private lemma exists_mul_mod {a b : ℕ} (ha : 0 < a) (hab : Nat.Coprime a b)
    (r : ℕ) (hr : r < a) :
    ∃ k, k < a ∧ k * b % a = r := by
  let f : Fin a → Fin a := fun k => ⟨k.val * b % a, Nat.mod_lt _ ha⟩
  have h_surj : Function.Surjective f :=
    (Finite.injective_iff_surjective.mp (mul_mod_injective ha hab))
  obtain ⟨⟨k, hk⟩, hkr⟩ := h_surj ⟨r, hr⟩
  simp only [f, Fin.mk.injEq] at hkr
  exact ⟨k, hk, hkr⟩

/-- For coprime a, b ≥ 1: every n ≥ (a-1)(b-1) is representable.

    Proof: Since gcd(a,b) = 1, the map k ↦ kb mod a is a bijection on {0,...,a-1}.
    For given n, find k < a with kb ≡ n (mod a). Then a | (n - kb).
    The bound n ≥ (a-1)(b-1) ensures n ≥ kb, giving the representation. -/
theorem large_representable {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (n : ℕ) (hn : (a - 1) * (b - 1) ≤ n) :
    Representable a b n := by
  -- Trivial cases
  rcases ha.eq_or_lt with rfl | ha2
  · exact ⟨n, 0, by ring⟩
  rcases hb.eq_or_lt with rfl | hb2
  · exact ⟨0, n, by ring⟩
  -- Now a ≥ 2, b ≥ 2
  have ha_pos : 0 < a := by omega
  -- Find k < a with k*b ≡ n (mod a)
  obtain ⟨k, hk_lt, hk_mod⟩ := exists_mul_mod ha_pos hab (n % a) (Nat.mod_lt n ha_pos)
  -- Show n ≥ k*b (the crucial bound)
  have h_n_ge_kb : k * b ≤ n := by
    by_contra h_neg
    push_neg at h_neg
    -- k*b > n and k*b ≡ n (mod a), so a | (k*b - n) with k*b - n > 0
    have h_dvd : a ∣ (k * b - n) := by
      rw [← Nat.modEq_iff_dvd' (le_of_lt h_neg)]
      exact hk_mod.symm
    -- Since a divides a positive number, a ≤ k*b - n
    have h_gap : a ≤ k * b - n := Nat.le_of_dvd (by omega) h_dvd
    -- k ≤ a - 1, so k*b ≤ (a-1)*b
    have h_kb_bound : k * b ≤ (a - 1) * b := Nat.mul_le_mul_right b (by omega)
    -- (a-1)*b = (a-1)*(b-1) + (a-1)
    have hab_expand : (a - 1) * b = (a - 1) * (b - 1) + (a - 1) := by
      have : b = (b - 1) + 1 := by omega
      rw [this, mul_add, mul_one]
    -- k*b ≥ n + a ≥ (a-1)*(b-1) + a, but k*b ≤ (a-1)*(b-1) + (a-1)
    -- This gives a ≤ a - 1, contradiction
    rw [hab_expand] at h_kb_bound
    omega
  -- a divides n - k*b
  have h_div : a ∣ (n - k * b) :=
    (Nat.modEq_iff_dvd' h_n_ge_kb).mp hk_mod
  -- Write n = a*q + b*k
  obtain ⟨q, hq⟩ := h_div
  -- From n - k*b = a*q and k*b ≤ n, reconstruct n = a*q + b*k
  have h3 : n = n - k * b + k * b := (Nat.sub_add_cancel h_n_ge_kb).symm
  rw [hq] at h3
  -- h3 : n = a * q + k * b
  exact ⟨q, k, by linarith [mul_comm k b]⟩

/-- ab - a - b is NOT representable for coprime a, b with a, b ≥ 2.

    Proof: If ab - a - b = ax + by, then ab = a(x+1) + b(y+1).
    By coprimality a | (y+1) and b | (x+1), giving y+1 ≥ a and x+1 ≥ b.
    Then a(x+1) + b(y+1) ≥ 2ab > ab, contradiction. -/
theorem frobenius_not_representable {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ¬Representable a b (a * b - a - b) := by
  intro ⟨x, y, hxy⟩
  -- a*b ≥ a + b since (a-1)*(b-1) ≥ 1
  have hab_ge : a + b ≤ a * b := by nlinarith
  -- Rewrite: a*b = a*(x+1) + b*(y+1)
  have key : a * b = a * (x + 1) + b * (y + 1) := by nlinarith
  -- a | b*(y+1): factor as a*(b-(x+1)) using key
  have h_dvd_by : a ∣ b * (y + 1) := ⟨b - (x + 1), by nlinarith⟩
  -- By coprimality: a | (y + 1)
  have h_dvd_y1 : a ∣ (y + 1) := hab.dvd_of_dvd_mul_left h_dvd_by
  -- b | a*(x+1): factor as b*(a-(y+1)) using key
  have h_dvd_ax : b ∣ a * (x + 1) := ⟨a - (y + 1), by nlinarith⟩
  -- By coprimality: b | (x + 1)
  have h_dvd_x1 : b ∣ (x + 1) := hab.symm.dvd_of_dvd_mul_left h_dvd_ax
  -- y + 1 ≥ a and x + 1 ≥ b
  have h_y_ge : a ≤ y + 1 := Nat.le_of_dvd (by omega) h_dvd_y1
  have h_x_ge : b ≤ x + 1 := Nat.le_of_dvd (by omega) h_dvd_x1
  -- a*(x+1) ≥ a*b and b*(y+1) ≥ a*b, but their sum equals a*b. Contradiction.
  have hx1 : a * b ≤ a * (x + 1) := Nat.mul_le_mul_left a h_x_ge
  have hy1 : b * a ≤ b * (y + 1) := Nat.mul_le_mul_left b h_y_ge
  have hab_pos : 0 < a * b := Nat.mul_pos (by omega) (by omega)
  linarith [mul_comm a b]

/-- **Sylvester's Theorem (1884)**: For coprime a, b ≥ 2,
    the Frobenius number is exactly ab - a - b -/
theorem sylvester_frobenius {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    frobeniusNumber a b = a * b - a - b ∧
    ¬Representable a b (frobeniusNumber a b) ∧
    ∀ n > frobeniusNumber a b, Representable a b n := by
  constructor
  · rfl
  constructor
  · exact frobenius_not_representable hab ha hb
  · intro n hn
    have hbound : (a - 1) * (b - 1) ≤ n := by
      have h := frobenius_alt_axiom a b ha hb
      unfold frobeniusNumber at hn h
      omega
    exact large_representable hab (by omega) (by omega) n hbound

-- ============================================================
-- PART 4: Examples
-- ============================================================

-- Example: Frobenius number of (3, 5)
example : frobeniusNumber 3 5 = 7 := by native_decide

-- Example: Frobenius number of (3, 7)
example : frobeniusNumber 3 7 = 11 := by native_decide

-- Example: Frobenius number of (5, 8)
example : frobeniusNumber 5 8 = 27 := by native_decide

-- Verify specific representabilities
example : Representable 3 5 8 := ⟨1, 1, by norm_num⟩  -- 8 = 3 + 5
example : Representable 3 5 9 := ⟨3, 0, by norm_num⟩  -- 9 = 3*3
example : Representable 3 5 10 := ⟨0, 2, by norm_num⟩ -- 10 = 5*2
example : Representable 3 5 11 := ⟨2, 1, by norm_num⟩ -- 11 = 6 + 5
example : Representable 3 5 12 := ⟨4, 0, by norm_num⟩ -- 12 = 3*4

example : Representable 3 7 12 := ⟨4, 0, by norm_num⟩ -- 12 = 3*4
example : Representable 3 7 13 := ⟨2, 1, by norm_num⟩ -- 13 = 6 + 7
example : Representable 3 7 14 := ⟨0, 2, by norm_num⟩ -- 14 = 7*2

-- Example: (3, 5) has (2)(4)/2 = 4 non-representable numbers: 1, 2, 4, 7
example : numNonRepresentable 3 5 = 4 := by native_decide

-- Example: (3, 7) has (2)(6)/2 = 6 non-representable numbers
example : numNonRepresentable 3 7 = 6 := by native_decide

-- ============================================================
-- PART 5: Corollaries
-- ============================================================

/-- Every sufficiently large number is representable -/
theorem eventually_all_representable {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    ∃ N, ∀ n ≥ N, Representable a b n := by
  use (a - 1) * (b - 1)
  intro n hn
  exact large_representable hab ha hb n hn

/-- The set of representable numbers is closed under addition of a -/
theorem representable_closure_a {a b n : ℕ} (h : Representable a b n) :
    Representable a b (n + a) := representable_add_a h

/-- The set of representable numbers is closed under addition of b -/
theorem representable_closure_b {a b n : ℕ} (h : Representable a b n) :
    Representable a b (n + b) := representable_add_b h

-- ============================================================
-- PART 6: Special Cases
-- ============================================================

/-- For consecutive integers (a, a+1), the Frobenius number is a² - a - 1 = (a-1)a - 1 -/
theorem frobenius_consecutive (a : ℕ) (ha : 2 ≤ a) :
    frobeniusNumber a (a + 1) = a * a - a - 1 := by
  unfold frobeniusNumber
  ring_nf
  omega

-- Examples of consecutive integers
example : frobeniusNumber 2 3 = 1 := by native_decide  -- Only 1 is not representable
example : frobeniusNumber 3 4 = 5 := by native_decide
example : frobeniusNumber 4 5 = 11 := by native_decide
example : frobeniusNumber 5 6 = 19 := by native_decide

/-- The classic "Chicken McNugget" case with simplified coprime pair -/
-- Original McNugget problem used {6, 9, 20}, but 6 and 9 share factor 3
-- For coprime demonstration, we use {3, 5} or {5, 7}
example : frobeniusNumber 5 7 = 23 := by native_decide

-- ============================================================
-- Exports
-- ============================================================

#check Representable
#check frobeniusNumber
#check sylvester_frobenius
#check eventually_all_representable

end FrobeniusNumber
