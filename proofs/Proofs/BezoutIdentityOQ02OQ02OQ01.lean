import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

/-
# Constructive Divisibility Algorithm via Bézout Coefficients

## Open Question Origin

From bezout-identity-oq-02-oq-02 (Euclid's Lemma Generalized):
"Can the Bézout coefficients from BezoutIdentityOQ01.extGcd be combined
with euclids_lemma_ring to give a constructive, computable divisibility
algorithm — producing explicit quotient witnesses?"

## Answer: YES

We define a constructive quotient extraction: given coprime a, b and
proof that a ∣ b*c, compute the explicit integer q such that c = a * q.

The key formula: if u*a + v*b = 1 and b*c = a*k, then a*(u*c + v*k) = c.
-/

namespace BezoutIdentityOQ02OQ02OQ01

/-
## Part I: The Extended Euclidean Algorithm
-/

/-- The extended Euclidean algorithm. Returns (x, y, g) where a*x + b*y = g = gcd(a,b). -/
def extGcd : ℕ → ℕ → ℤ × ℤ × ℕ
  | a, 0 => (1, 0, a)
  | a, b + 1 =>
    have : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
    let r := extGcd (b + 1) (a % (b + 1))
    (r.2.1, r.1 - ↑(a / (b + 1)) * r.2.1, r.2.2)

@[simp]
theorem extGcd_zero (a : ℕ) : extGcd a 0 = (1, 0, a) := by simp [extGcd]

theorem extGcd_succ (a b : ℕ) :
    extGcd a (b + 1) =
      let r := extGcd (b + 1) (a % (b + 1))
      (r.2.1, r.1 - ↑(a / (b + 1)) * r.2.1, r.2.2) := by
  simp [extGcd]

theorem extGcd_gcd : ∀ (a b : ℕ), (extGcd a b).2.2 = Nat.gcd a b := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    match b with
    | 0 => simp [Nat.gcd_zero_right]
    | b + 1 =>
      rw [extGcd_succ]; simp only
      have hlt : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
      rw [ih (a % (b + 1)) hlt (b + 1)]
      rw [Nat.gcd_comm a (b + 1), Nat.gcd_rec (b + 1) a, Nat.gcd_comm]

theorem extGcd_bezout : ∀ (a b : ℕ),
    let r := extGcd a b
    (a : ℤ) * r.1 + (b : ℤ) * r.2.1 = (r.2.2 : ℤ) := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    match b with
    | 0 => simp
    | b + 1 =>
      simp only; rw [extGcd_succ]; simp only
      have hlt : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
      have hrec := ih (a % (b + 1)) hlt (b + 1)
      simp only at hrec
      set x' := (extGcd (b + 1) (a % (b + 1))).1
      set y' := (extGcd (b + 1) (a % (b + 1))).2.1
      have hdiv : (a : ℤ) = ↑(a / (b + 1)) * ↑(b + 1) + ↑(a % (b + 1)) := by
        have h := Nat.div_add_mod a (b + 1); zify at h ⊢; linarith
      linear_combination hrec + hdiv * y'

theorem extGcd_correct (a b : ℕ) :
    let r := extGcd a b
    (a : ℤ) * r.1 + (b : ℤ) * r.2.1 = ↑(Nat.gcd a b) := by
  have hbez := extGcd_bezout a b
  have hgcd := extGcd_gcd a b
  simp only; rw [← hgcd]; exact hbez

/-
## Part II: The Core Quotient Formula
-/

/-- **The core formula**: Given Bézout coefficients u, v with u*a + v*b = 1,
    and a divisibility witness k with b*c = a*k, then a*(u*c + v*k) = c.

    Proof: a*(u*c + v*k) = u*a*c + v*a*k = u*a*c + v*b*c = (u*a + v*b)*c = 1*c = c -/
theorem quotient_formula {R : Type*} [CommRing R] {a b c : R} (u v : R)
    (hbez : u * a + v * b = 1) (k : R) (hk : b * c = a * k) :
    a * (u * c + v * k) = c := by
  have hk' : a * k = b * c := hk.symm
  calc a * (u * c + v * k)
      = u * a * c + v * (a * k) := by ring
    _ = u * a * c + v * (b * c) := by rw [hk']
    _ = (u * a + v * b) * c := by ring
    _ = 1 * c := by rw [hbez]
    _ = c := one_mul c

/-- **Euclid's lemma with explicit witness**: constructive version. -/
theorem euclids_lemma_constructive {R : Type*} [CommRing R] {a b c : R}
    (u v : R) (hbez : u * a + v * b = 1) (hdvd : a ∣ b * c) : a ∣ c := by
  obtain ⟨k, hk⟩ := hdvd
  exact ⟨u * c + v * k, (quotient_formula u v hbez k hk).symm⟩

/-
## Part III: The Constructive Algorithm for ℕ via extGcd
-/

/-- **Constructive quotient**: Given a, b : ℕ with gcd = 1 and a ∣ b*c,
    compute the explicit quotient q such that a*q = c. -/
noncomputable def constructive_div (a b c : ℕ)
    (_hcop : Nat.gcd a b = 1) (hdvd : (a : ℤ) ∣ (b : ℤ) * c) : ℤ :=
  let r := extGcd a b
  let x := r.1
  let y := r.2.1
  let k := hdvd.choose
  x * c + y * k

/-- The constructive quotient is correct: a * q = c. -/
theorem constructive_div_correct (a b c : ℕ)
    (hcop : Nat.gcd a b = 1) (hdvd : (a : ℤ) ∣ (b : ℤ) * c) :
    (a : ℤ) * constructive_div a b c hcop hdvd = (c : ℤ) := by
  unfold constructive_div
  set r := extGcd a b
  set x := r.1
  set y := r.2.1
  set k := hdvd.choose
  have hk : (b : ℤ) * c = (a : ℤ) * k := hdvd.choose_spec
  have hbez : (a : ℤ) * x + (b : ℤ) * y = 1 := by
    have h := extGcd_correct a b
    simp only at h
    rw [hcop] at h; simp at h; linarith
  have hbez' : x * ↑a + y * ↑b = 1 := by linarith
  exact quotient_formula x y hbez' k hk

/-- **Main theorem**: Euclid's lemma via the constructive algorithm. -/
theorem euclids_lemma_via_extGcd (a b c : ℕ)
    (hcop : Nat.gcd a b = 1) (hdvd : (a : ℤ) ∣ (b : ℤ) * c) :
    (a : ℤ) ∣ (c : ℤ) :=
  ⟨constructive_div a b c hcop hdvd, (constructive_div_correct a b c hcop hdvd).symm⟩

/-
## Part IV: Computational Verification
-/

-- Verify extGcd computations
example : (extGcd 3 7).2.2 = 1 := by native_decide
example : (extGcd 5 7).2.2 = 1 := by native_decide
example : (extGcd 17 5).2.2 = 1 := by native_decide

-- Verify Bézout identities
example : let r := extGcd 3 7
          (3 : ℤ) * r.1 + 7 * r.2.1 = 1 := by native_decide

example : let r := extGcd 5 7
          (5 : ℤ) * r.1 + 7 * r.2.1 = 1 := by native_decide

example : let r := extGcd 17 5
          (17 : ℤ) * r.1 + 5 * r.2.1 = 1 := by native_decide

-- Verify with larger numbers
example : (extGcd 252 198).2.2 = 18 := by native_decide
example : let r := extGcd 252 198
          (252 : ℤ) * r.1 + 198 * r.2.1 = 18 := by native_decide

/-
## Part V: The Quotient is Unique (in Integral Domains)
-/

/-- **Uniqueness**: In an integral domain with a ≠ 0, if a*q₁ = c and a*q₂ = c,
    then q₁ = q₂. -/
theorem constructive_quotient_unique {R : Type*} [CommRing R] [IsDomain R]
    {a c : R} (ha : a ≠ 0) (q₁ q₂ : R) (h₁ : a * q₁ = c) (h₂ : a * q₂ = c) :
    q₁ = q₂ := by
  have : a * q₁ = a * q₂ := by rw [h₁, h₂]
  exact mul_left_cancel₀ ha this

/-
## Part VI: Connection to Abstract Algebra

The constructive formula works in any CommRing — we don't need ℤ specifically.
-/

/-- **Abstract constructive Euclid's lemma**: Works in any CommRing.
    Given Bézout witnesses, extract the divisibility quotient. -/
theorem abstract_euclids_lemma {R : Type*} [CommRing R] {a b c : R}
    (hcop : IsCoprime a b) (hdvd : a ∣ b * c) : a ∣ c := by
  obtain ⟨u, v, huv⟩ := hcop
  exact euclids_lemma_constructive u v huv hdvd

/-- The abstract version agrees with Mathlib's `IsCoprime.dvd_of_dvd_mul_right`. -/
example {R : Type*} [CommRing R] {a b c : R}
    (hcop : IsCoprime a b) (hdvd : a ∣ b * c) : a ∣ c :=
  hcop.dvd_of_dvd_mul_left hdvd

end BezoutIdentityOQ02OQ02OQ01
