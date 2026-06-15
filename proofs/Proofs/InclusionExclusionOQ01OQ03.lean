/-
  OQ-01-OQ-03: Classical (divisor-form) Möbius inversion
  (inclusion-exclusion-oq-01-oq-03)

  Open question of the parent gallery entry `inclusion-exclusion-oq-01`
  (which already proves the divisor–totient identity `Σ_{d|n} φ(d) = n` via the
  inclusion–exclusion sieve):

      Formalize Möbius inversion:
          f(n) = Σ_{d | n} g(d)   ⟺   g(n) = Σ_{d | n} μ(d) · f(n/d).

  This is the number-theoretic incarnation of inclusion–exclusion (the Möbius
  function `μ` of the divisor lattice is the IE sign).

  ── What Mathlib already has, and what this adds ──────────────────────────────

  Mathlib v4.26 proves Möbius inversion, but in **antidiagonal** form
  (`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`):

      (∀ n>0, Σ_{i ∈ n.divisors} f i = g n) ↔
        (∀ n>0, Σ_{x ∈ n.divisorsAntidiagonal} μ x.1 · g x.2 = f n).

  The textbook statement the gallery question asks for uses the **divisor** sum
  `Σ_{d | n} μ(d) · f(n/d)` instead of the antidiagonal sum.  The bridge is
  `Nat.sum_divisorsAntidiagonal`:
      Σ_{x ∈ n.divisorsAntidiagonal} F x.1 x.2 = Σ_{d ∈ n.divisors} F d (n/d).

  `moebius_inversion_divisors` below states and proves the textbook form by
  wiring these two lemmas (plus `eq_comm` to match the gallery's orientation).
  This is a thin but faithful bridge — the mathematical depth lives in Mathlib's
  `sum_eq_iff_sum_mul_moebius_eq`; the value here is exposing the classical
  `Σ_{d|n} μ(d) f(n/d)` shape that downstream gallery work expects.

  `totient_eq_sum_moebius_mul` then applies the bridge to the parent entry's
  `Σ_{d|n} φ(d) = n` (`Nat.sum_totient`), yielding the Möbius form of Euler's
  totient `φ(n) = Σ_{d|n} μ(d)·(n/d)` — the inclusion–exclusion read of `φ`.

  Numerically cross-checked (all n ≤ 400, random integer data, both directions,
  μ sanity, and the Euler-φ anchor) in
  `research/problems/inclusion-exclusion-oq-01-oq-03/verify_moebius_inversion.py`
  (ALL PASS).

  Status: 0 axioms, 0 sorries.  Registered in `Proofs/Proofs.lean` so the gallery
  build machine-checks it.  Lemma names verified against the pinned Mathlib v4.26.0
  (`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`, `Nat.sum_divisorsAntidiagonal`).
-/

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic

open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace InclusionExclusionOQ01OQ03

variable {R : Type*} [CommRing R]

/-- **Classical Möbius inversion (divisor form).**  For functions `f, g : ℕ → R`
    into a commutative ring,
        `f(n) = Σ_{d | n} g(d)   ↔   g(n) = Σ_{d | n} μ(d) · f(n/d)`
    (for all `n > 0`).  Bridges Mathlib's antidiagonal
    `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` to the textbook divisor
    sum via `Nat.sum_divisorsAntidiagonal`. -/
theorem moebius_inversion_divisors {f g : ℕ → R} :
    (∀ n > 0, f n = ∑ d ∈ n.divisors, g d) ↔
      (∀ n > 0, g n = ∑ d ∈ n.divisors, (μ d : R) * f (n / d)) := by
  constructor
  · intro h n hn
    have hM := (sum_eq_iff_sum_mul_moebius_eq (R := R) (f := g) (g := f)).mp
      (fun m hm => (h m hm).symm) n hn
    rw [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : R) * f b)] at hM
    exact hM.symm
  · intro h n hn
    have hM : ∀ m > 0, ∑ x ∈ m.divisorsAntidiagonal, (μ x.1 : R) * f x.2 = g m := by
      intro m hm
      rw [Nat.sum_divisorsAntidiagonal (fun a b => (μ a : R) * f b)]
      exact (h m hm).symm
    exact ((sum_eq_iff_sum_mul_moebius_eq (R := R) (f := g) (g := f)).mpr hM n hn).symm

/-- **Euler-φ corollary (Möbius form of the totient).**  Applying divisor-form
    Möbius inversion to the classical identity `n = Σ_{d | n} φ(d)` (`Nat.sum_totient`)
    gives the Möbius expression for the totient:
        `φ(n) = Σ_{d | n} μ(d) · (n / d)`   (for `n > 0`, over `ℤ`).
    This is the parent gallery entry's `Σ_{d|n} φ(d) = n` "inverted" — exactly the
    inclusion–exclusion read of Euler's function. -/
theorem totient_eq_sum_moebius_mul (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℤ) = ∑ d ∈ n.divisors, (μ d : ℤ) * ((n / d : ℕ) : ℤ) := by
  refine (moebius_inversion_divisors (R := ℤ)
      (f := fun m => (m : ℤ)) (g := fun d => (Nat.totient d : ℤ))).mp (fun m _ => ?_) n hn
  -- forward input: `(m : ℤ) = Σ_{d | m} φ(d)`, the cast of `Nat.sum_totient`.
  exact_mod_cast (Nat.sum_totient m).symm

/-- **Möbius convolution identity** `Σ_{d | n} μ(d) = [n = 1]` (for `n > 0`).
    This is the defining property of the Möbius function as the multiplicative
    inverse of the constant-one function (`μ ∗ 1 = δ`), and the cleanest face of
    inclusion–exclusion: the divisor-lattice IE signs cancel completely except at
    `n = 1`.  Derived purely from `moebius_inversion_divisors` (no extra Mathlib
    Möbius lemma): take `f ≡ 1`; the unique `g` with `f(n) = Σ_{d|n} g(d)` is the
    indicator `g = [· = 1]`, and inversion reads off `g(n) = Σ_{d|n} μ(d)`. -/
theorem moebius_sum_divisors_eq_ite (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, (μ d : R)) = if n = 1 then (1 : R) else 0 := by
  have hfwd : ∀ m > 0, (1 : R) = ∑ d ∈ m.divisors, (if d = 1 then (1 : R) else 0) := by
    intro m hm
    rw [Finset.sum_eq_single (1 : ℕ)]
    · simp
    · intro b _ hb1; simp [hb1]
    · intro h1; exact absurd (Nat.one_mem_divisors.mpr hm.ne') h1
  have key := (moebius_inversion_divisors (R := R)
      (f := fun _ => (1 : R)) (g := fun m => if m = 1 then (1 : R) else 0)).mp hfwd n hn
  simpa using key.symm

end InclusionExclusionOQ01OQ03
