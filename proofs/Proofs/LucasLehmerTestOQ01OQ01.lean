import Mathlib
import Proofs.LucasLehmerTestOQ01

/-
# Seed-independence of the Lucas–Lehmer recurrence

The Lucas–Lehmer test fixes the seed `s₀ = 4` and iterates `x ↦ x² − 2`
(Mathlib's `LucasLehmer.s`).  Why `4`?  This file isolates the algebraic
mechanism behind the choice of seed and makes the dependence on it explicit.

The recurrence `x ↦ x² − 2` is the *Chebyshev doubling map*: if `c = a + a⁻¹`
for a unit `a` of any commutative ring, then the iterate from seed `c` has the
closed form

    sₙ = a^(2ⁿ) + a^(−2ⁿ).

So the seed enters **only** through the unit `a` it represents.  The standard
seed `4 = (2 + √3) + (2 − √3)` is exactly `a + a⁻¹` for the fundamental unit
`a = 2 + √3` of `ℤ[√3]` (note `(2+√3)(2−√3) = 1`).  Specialising the closed
form to `ℤ[√3]` recovers the classical formula

    LucasLehmer.s n = ((2 + √3)^(2ⁿ) + (2 − √3)^(2ⁿ)).

## What this file proves

* `llSeq` — the generic `x ↦ x² − 2` recurrence over an arbitrary commutative
  ring from an arbitrary seed `c`;
* `llSeq_four_eq_s` — `llSeq 4 = LucasLehmer.s` over `ℤ` (anchoring the standard
  test inside the generic family);
* `map_llSeq` — the recurrence commutes with every ring homomorphism, so it is
  preserved under base change (this is what makes seed `4 ↦ 4` portable between
  `ℤ` and `ℤ[√3]`);
* `llSeq_closed` — the **doubling closed form** `llSeq (a + b) n = a^(2ⁿ) + b^(2ⁿ)`
  for any `a, b` with `a * b = 1`, in any commutative ring;
* `llSeq_shift` — seed-shift independence: running one extra step from seed `c`
  is the same as running from the advanced seed `c² − 2`;
* `s_closed_form` — the classical closed form for the integer Lucas–Lehmer
  sequence via `ℤ[√3]`.

Everything is proved from the commutative-ring axioms and Mathlib's `Zsqrtd`;
no `axiom`, no `sorry`, no `native_decide`.
-/

namespace LucasLehmerTestOQ01OQ01

open LucasLehmer

/-! ## The generic seeded recurrence -/

/-- The Lucas–Lehmer doubling recurrence `x ↦ x² − 2` over an arbitrary
commutative ring, started from an arbitrary seed `c`. -/
def llSeq {R : Type*} [CommRing R] (c : R) : ℕ → R
  | 0 => c
  | n + 1 => (llSeq c n) ^ 2 - 2

@[simp] theorem llSeq_zero {R : Type*} [CommRing R] (c : R) : llSeq c 0 = c := rfl

theorem llSeq_succ {R : Type*} [CommRing R] (c : R) (n : ℕ) :
    llSeq c (n + 1) = (llSeq c n) ^ 2 - 2 := rfl

/-! ## Anchoring Mathlib's seed-4 test -/

/-- Over `ℤ`, the generic recurrence from seed `4` is exactly Mathlib's
Lucas–Lehmer sequence `LucasLehmer.s`. -/
theorem llSeq_four_eq_s (n : ℕ) : llSeq (4 : ℤ) n = LucasLehmer.s n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [llSeq_succ, ih]; rfl

/-! ## Base change: the recurrence is a ring-hom-equivariant family -/

/-- The recurrence commutes with any ring homomorphism: `f (llSeq c n) = llSeq (f c) n`.
This is what lets us transport the seed-`4` sequence from `ℤ` into `ℤ[√3]`. -/
theorem map_llSeq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R) (n : ℕ) :
    f (llSeq c n) = llSeq (f c) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [llSeq_succ, map_sub, map_pow, map_ofNat, ih]

/-! ## The doubling closed form

The heart of seed-independence: the iterate depends on the seed `c = a + b`
(with `a b = 1`) only through `a`, via `sₙ = a^(2ⁿ) + b^(2ⁿ)`. -/

/-- **Doubling closed form.** For any `a, b` in a commutative ring with
`a * b = 1`, the recurrence from seed `a + b` satisfies
`llSeq (a + b) n = a^(2ⁿ) + b^(2ⁿ)`. -/
theorem llSeq_closed {R : Type*} [CommRing R] (a b : R) (hab : a * b = 1) (n : ℕ) :
    llSeq (a + b) n = a ^ (2 ^ n) + b ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [llSeq_succ, ih]
    have hpow : a ^ (2 ^ n) * b ^ (2 ^ n) = 1 := by rw [← mul_pow, hab, one_pow]
    have e1 : a ^ (2 ^ (n + 1)) = (a ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
    have e2 : b ^ (2 ^ (n + 1)) = (b ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
    rw [e1, e2]
    linear_combination 2 * hpow

/-! ## Seed-shift independence -/

/-- **Seed-shift independence.** Running one extra step from seed `c` equals
running from the advanced seed `c² − 2`. Hence the family of sequences is
closed under the recurrence map acting on seeds. -/
theorem llSeq_shift {R : Type*} [CommRing R] (c : R) :
    ∀ n, llSeq c (n + 1) = llSeq (c ^ 2 - 2) n
  | 0 => rfl
  | n + 1 => by rw [llSeq_succ, llSeq_shift c n, ← llSeq_succ]

/-! ## The classical closed form over `ℤ[√3]`

`4 = (2 + √3) + (2 − √3)` with `(2 + √3)(2 − √3) = 1`. Specialising the doubling
identity to the unit `a = 2 + √3 = ⟨2, 1⟩` of `ℤ[√3]` recovers the explicit
formula for the integer Lucas–Lehmer sequence. -/

/-- The fundamental unit `2 + √3` of `ℤ[√3]`. -/
def alpha : ℤ√3 := ⟨2, 1⟩

/-- Its conjugate `2 − √3 = (2 + √3)⁻¹`. -/
def beta : ℤ√3 := ⟨2, -1⟩

theorem alpha_mul_beta : alpha * beta = 1 := by
  apply Zsqrtd.ext <;>
    simp [alpha, beta, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_one, Zsqrtd.im_one]

theorem alpha_add_beta : alpha + beta = 4 := by
  apply Zsqrtd.ext <;> simp [alpha, beta, Zsqrtd.re_ofNat, Zsqrtd.im_ofNat]

/-- **Classical closed form.** The integer Lucas–Lehmer sequence is the real
part of `(2 + √3)^(2ⁿ) + (2 − √3)^(2ⁿ)` inside `ℤ[√3]`. -/
theorem s_closed_form (n : ℕ) :
    LucasLehmer.s n = (alpha ^ (2 ^ n) + beta ^ (2 ^ n)).re := by
  -- Transport the seed-4 sequence from ℤ into ℤ[√3].
  have hmap : ((LucasLehmer.s n : ℤ) : ℤ√3) = llSeq (4 : ℤ√3) n := by
    rw [← llSeq_four_eq_s n]
    have := map_llSeq (Int.castRingHom (ℤ√3)) (4 : ℤ) n
    simpa using this
  -- Evaluate the ℤ[√3] sequence by the doubling closed form.
  have hclosed : llSeq (4 : ℤ√3) n = alpha ^ (2 ^ n) + beta ^ (2 ^ n) := by
    rw [← alpha_add_beta, llSeq_closed alpha beta alpha_mul_beta]
  -- Combine and read off the real part.
  have : ((LucasLehmer.s n : ℤ) : ℤ√3) = alpha ^ (2 ^ n) + beta ^ (2 ^ n) := by
    rw [hmap, hclosed]
  have hre := congrArg Zsqrtd.re this
  rwa [Zsqrtd.re_intCast] at hre

/-! ## The alternative seed `s₀ = 10` is also of the form `ω + ω⁻¹`

The open question singles out the alternative starting value `s₀ = 10`.
It fits the same `ω + ω⁻¹` template, now in `ℤ[√6]`:
`10 = (5 + 2√6) + (5 − 2√6)` with `(5 + 2√6)(5 − 2√6) = 25 − 24 = 1`.
So the seed-`10` iterate has the analogous closed form, confirming `10` is an
admissible "unit-trace" seed exactly like `4`. -/

/-- The unit `5 + 2√6` of `ℤ[√6]`. -/
def gamma : ℤ√6 := ⟨5, 2⟩

/-- Its conjugate `5 − 2√6 = (5 + 2√6)⁻¹`. -/
def delta : ℤ√6 := ⟨5, -2⟩

theorem gamma_mul_delta : gamma * delta = 1 := by
  apply Zsqrtd.ext <;>
    simp [gamma, delta, Zsqrtd.re_mul, Zsqrtd.im_mul, Zsqrtd.re_one, Zsqrtd.im_one]

theorem gamma_add_delta : gamma + delta = 10 := by
  apply Zsqrtd.ext <;>
    simp [gamma, delta, Zsqrtd.re_ofNat, Zsqrtd.im_ofNat]

/-- **Seed-10 closed form.** The `x ↦ x² − 2` iterate from the alternative seed
`10` is the real part of `(5 + 2√6)^(2ⁿ) + (5 − 2√6)^(2ⁿ)` inside `ℤ[√6]` —
the same `ω^(2ⁿ) + ω⁻¹^(2ⁿ)` shape that governs the standard seed `4`. -/
theorem seed_ten_closed_form (n : ℕ) :
    llSeq (10 : ℤ) n = (gamma ^ (2 ^ n) + delta ^ (2 ^ n)).re := by
  have hmap : ((llSeq (10 : ℤ) n : ℤ) : ℤ√6) = llSeq (10 : ℤ√6) n := by
    have := map_llSeq (Int.castRingHom (ℤ√6)) (10 : ℤ) n
    simpa using this
  have hclosed : llSeq (10 : ℤ√6) n = gamma ^ (2 ^ n) + delta ^ (2 ^ n) := by
    rw [← gamma_add_delta, llSeq_closed gamma delta gamma_mul_delta]
  have : ((llSeq (10 : ℤ) n : ℤ) : ℤ√6) = gamma ^ (2 ^ n) + delta ^ (2 ^ n) := by
    rw [hmap, hclosed]
  have hre := congrArg Zsqrtd.re this
  rwa [Zsqrtd.re_intCast] at hre

end LucasLehmerTestOQ01OQ01
