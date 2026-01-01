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
- [ ] Full proof of main theorem (axiomatized)
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

/-- Alternative form: (a-1)(b-1) - 1 when a, b ≥ 2

    Proof: (a-1)(b-1) = ab - a - b + 1, so (a-1)(b-1) - 1 = ab - a - b -/
axiom frobenius_alt_axiom (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    frobeniusNumber a b = (a - 1) * (b - 1) - 1

/-- Verified for specific examples -/
example : frobeniusNumber 3 5 = (3 - 1) * (5 - 1) - 1 := by native_decide
example : frobeniusNumber 4 7 = (4 - 1) * (7 - 1) - 1 := by native_decide

/-- The number of non-representable positive integers -/
def numNonRepresentable (a b : ℕ) : ℕ := (a - 1) * (b - 1) / 2

-- ============================================================
-- PART 3: Main Theorem (Axiomatized)
-- ============================================================

/-- **Axiom:** For coprime a, b ≥ 2: every n ≥ (a-1)(b-1) is representable.

    **Proof sketch:** For each residue class r mod a, there exists a unique
    k ∈ {0, 1, ..., a-1} such that kb ≡ r (mod a). The smallest representable
    number in class r is kb. Adding multiples of a gives all representables.
    Since k < a, we have kb < ab, and kb + qa is representable for any q ≥ 0.
    Every n ≥ (a-1)(b-1) can be written in this form. -/
axiom large_representable {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (n : ℕ) (hn : (a - 1) * (b - 1) ≤ n) :
    Representable a b n

/-- **Axiom:** ab - a - b is NOT representable for coprime a, b with a, b ≥ 2.

    **Proof sketch:** Suppose ab - a - b = ax + by for some x, y ≥ 0.
    Then ab = a(x+1) + b(y+1). Since gcd(a,b) = 1:
    - a | b(y+1) implies a | (y+1), so y+1 ≥ a
    - b | a(x+1) implies b | (x+1), so x+1 ≥ b
    But then a(x+1) + b(y+1) ≥ ab + ab = 2ab > ab, contradiction. -/
axiom frobenius_not_representable {a b : ℕ} (hab : Nat.Coprime a b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) : ¬Representable a b (a * b - a - b)

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
    -- n > frobeniusNumber a b = ab - a - b
    -- We need (a-1)(b-1) ≤ n, i.e., ab - a - b + 1 ≤ n
    -- Since n > ab - a - b, we have n ≥ ab - a - b + 1
    have hbound : (a - 1) * (b - 1) ≤ n := by
      have h := frobenius_alt_axiom a b ha hb
      unfold frobeniusNumber at hn h
      -- frobenius_alt says ab - a - b = (a-1)(b-1) - 1
      -- So (a-1)(b-1) = ab - a - b + 1 ≤ n since n > ab - a - b
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
  -- a * (a + 1) - a - (a + 1) = a² + a - 2a - 1 = a² - a - 1
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
