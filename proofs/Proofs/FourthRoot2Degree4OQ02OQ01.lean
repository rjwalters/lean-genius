/-
  Fourth Root of 2, Degree 4 — OQ-02-OQ-01:
  From `Xⁿ − p` (prime `p`) to `Xⁿ − a` (general `a`): the full Kummer /
  Vahlen–Capelli criterion, and why it does NOT reduce to "not a perfect power".

  Open question (generalization) from `FourthRoot2Degree4OQ02`:

      Does the same packaging extend to `Xⁿ − a` for a general (non-prime) `a`,
      e.g. via the full Kummer criterion that `Xⁿ − a` is irreducible iff `a` is
      not a perfect `d`-th power for any prime `d ∣ n` (and `a ∉ −4·(fourth
      powers)` when `4 ∣ n`)?

  The parent file (`FourthRoot2Degree4OQ02`) packaged Eisenstein's criterion for
  `Xⁿ − p` with `p` **prime**.  A prime `p` is *never* a nontrivial power, so the
  irreducibility question there is answered by the single fact "`p` is prime".
  For a **general** `a` the answer is more delicate, and splits into a part that
  Mathlib already supplies and a part that it deliberately marks with `TODO`.

  ## What Mathlib supplies (general `a`, restated as packaged lemmas)

  Mathlib's `Mathlib/FieldTheory/KummerExtension.lean` proves the criterion for
  arbitrary `a` in exactly two regimes:

    * `X_pow_sub_C_irreducible_iff_of_odd`        — `n` odd:
        `Irreducible (Xⁿ − a) ↔ ∀ d ∣ n, d ≠ 1 → ∀ b, bᵈ ≠ a`.
    * `X_pow_sub_C_irreducible_iff_of_prime_pow`  — `n = pᵏ`, `p ≠ 2`:
        `Irreducible (X^{pᵏ} − a) ↔ ∀ b, bᵖ ≠ a`.

  In both regimes the criterion is *precisely* "`a` is not a perfect `d`-th power
  for the relevant primes `d`".  We restate these as our own general-`a` lemmas.

  ## Where the naive extension BREAKS (the mathematical heart)

  The naive statement "`Xⁿ − a` irreducible ⟺ `a` is not a perfect `d`-th power
  for any prime `d ∣ n`" is **false** once `4 ∣ n`.  The Vahlen–Capelli theorem
  adds an exceptional clause `a ∉ −4·(fourth powers)`, and Mathlib leaves the
  even case as a `TODO`.

  We formalise the sharp witness with Sophie Germain's identity

      X⁴ + 4c⁴ = (X² − 2cX + 2c²)(X² + 2cX + 2c²).

  Taking `a = −4c⁴` gives a reducible `X⁴ − C a` even though `a` is **not a
  perfect square** (indeed `a < 0`), so the only prime divisor `d = 2` of `4`
  passes the "not a `d`-th power" test.  The capstone
  `prime_divisor_criterion_insufficient` packages this as: there exists `a : ℚ`
  which is not a square yet with `X⁴ − C a` reducible — the naive criterion is
  provably insufficient for even exponents, which is exactly the phenomenon the
  open question points at.

  Results: 0 axioms, 0 sorries.
-/

import Mathlib

open Polynomial

namespace FourthRoot2Degree4OQ02OQ01

/-! ## Part 1: The general-`a` criterion in the regimes Mathlib covers

These two lemmas answer the "yes it extends" half of the open question: for a
general element `a` of any field, irreducibility of `Xⁿ − a` is governed purely
by whether `a` is a perfect power, provided `n` is odd or a `p ≠ 2` prime power.
-/

variable {K : Type*} [Field K]

/-- **General `a`, odd exponent.**  For any field `K`, any odd `n`, and any
`a : K`, `Xⁿ − a` is irreducible iff `a` is not a perfect `d`-th power for every
divisor `1 ≠ d ∣ n`.  This is Mathlib's `X_pow_sub_C_irreducible_iff_of_odd`,
repackaged as the general-`a` analogue of the parent's prime-only lemma. -/
theorem irreducible_X_pow_sub_C_odd_iff {n : ℕ} (hn : Odd n) (a : K) :
    Irreducible (X ^ n - C a) ↔ ∀ d, d ∣ n → d ≠ 1 → ∀ b : K, b ^ d ≠ a :=
  X_pow_sub_C_irreducible_iff_of_odd hn

/-- **General `a`, `p ≠ 2` prime-power exponent.**  For `n = pᵏ` with `p` an odd
prime and `k ≥ 1`, `X^{pᵏ} − a` is irreducible iff `a` is not a perfect `p`-th
power.  This is Mathlib's `X_pow_sub_C_irreducible_iff_of_prime_pow`. -/
theorem irreducible_X_pow_sub_C_primePow_iff {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {k : ℕ} (hk : k ≠ 0) (a : K) :
    Irreducible (X ^ p ^ k - C a) ↔ ∀ b : K, b ^ p ≠ a :=
  X_pow_sub_C_irreducible_iff_of_prime_pow hp hp2 hk

/-! ## Part 2: Sophie Germain factorisations (the `4 ∣ n`, `a = −4c⁴` family)

Pure ring identities.  Each exhibits a degree-4 polynomial `X⁴ − a` (with
`a = −4c⁴ < 0`, so `a` is not a square) as a product of two quadratics. -/

/-- Sophie Germain at `c = 1`: `X⁴ + 4 = (X² − 2X + 2)(X² + 2X + 2)`. -/
theorem sophie_germain_4 :
    (X ^ 2 - 2 * X + 2) * (X ^ 2 + 2 * X + 2) = (X ^ 4 + 4 : ℚ[X]) := by
  ring

/-- Sophie Germain at `c = 2`: `X⁴ + 64 = (X² − 4X + 8)(X² + 4X + 8)`,
so `a = −64 = −4·2⁴`. -/
theorem sophie_germain_64 :
    (X ^ 2 - 4 * X + 8) * (X ^ 2 + 4 * X + 8) = (X ^ 4 + 64 : ℚ[X]) := by
  ring

/-! ## Part 3: Reducibility of the witnesses

A quadratic factor has `natDegree = 2 ≠ 0`, hence is not a unit; a product of two
non-units cannot be irreducible. -/

/-- Helper: a rational polynomial of `natDegree 2` is not a unit. -/
private theorem not_isUnit_of_natDegree_two {q : ℚ[X]} (hq : q.natDegree = 2) :
    ¬ IsUnit q := by
  intro hu
  rw [natDegree_eq_zero_of_isUnit hu] at hq
  exact absurd hq (by norm_num)

/-- `X⁴ + 4` is reducible over `ℚ` (Sophie Germain), even though `−4` is not a
square in `ℚ`. -/
theorem X4_add_4_reducible : ¬ Irreducible (X ^ 4 + 4 : ℚ[X]) := by
  intro h
  rcases h.isUnit_or_isUnit sophie_germain_4.symm with hu | hu
  · exact absurd hu (not_isUnit_of_natDegree_two (by compute_degree!))
  · exact absurd hu (not_isUnit_of_natDegree_two (by compute_degree!))

/-- `X⁴ + 64` is reducible over `ℚ`, the `c = 2` member of the family. -/
theorem X4_add_64_reducible : ¬ Irreducible (X ^ 4 + 64 : ℚ[X]) := by
  intro h
  rcases h.isUnit_or_isUnit sophie_germain_64.symm with hu | hu
  · exact absurd hu (not_isUnit_of_natDegree_two (by compute_degree!))
  · exact absurd hu (not_isUnit_of_natDegree_two (by compute_degree!))

/-! ## Part 4: Recasting into `Xⁿ − C a` form and the sharp boundary -/

/-- `−4 : ℚ` is not a perfect square: the naive prime-divisor test for `n = 4`
(whose only prime divisor is `2`) is *satisfied* by `a = −4`. -/
theorem neg4_not_square : ∀ b : ℚ, b ^ 2 ≠ -4 := by
  intro b h
  nlinarith [sq_nonneg b]

/-- `−64 : ℚ` is not a perfect square either. -/
theorem neg64_not_square : ∀ b : ℚ, b ^ 2 ≠ -64 := by
  intro b h
  nlinarith [sq_nonneg b]

/-- `X⁴ − C(−4)` is reducible over `ℚ`.  Rewriting `C(−4) = −4` turns the
Kummer-form statement into the Sophie Germain witness. -/
theorem X_pow_sub_C_neg4_reducible : ¬ Irreducible (X ^ 4 - C (-4 : ℚ)) := by
  have hC : C (-4 : ℚ) = -4 := by simp
  rw [hC]
  have h : (X ^ 4 - (-4) : ℚ[X]) = X ^ 4 + 4 := by ring
  rw [h]; exact X4_add_4_reducible

/-- **The open question's crux, formalised.**  For the even exponent `n = 4`,
the naive criterion "`X⁴ − a` irreducible ⟺ `a` is not a perfect `d`-th power for
every prime `d ∣ 4`" is *insufficient*: there is a rational `a` (namely `−4`)
that is not a perfect square — so it passes the only relevant test `d = 2` — yet
`X⁴ − C a` is reducible.  This is exactly the `a ∈ −4·(fourth powers)` exceptional
clause of Vahlen–Capelli that Mathlib leaves as a `TODO`, and it shows the
parent's prime-`a` packaging does *not* naively extend to general `a` once
`4 ∣ n`. -/
theorem prime_divisor_criterion_insufficient :
    ∃ a : ℚ, (∀ b : ℚ, b ^ 2 ≠ a) ∧ ¬ Irreducible (X ^ 4 - C a) :=
  ⟨-4, neg4_not_square, X_pow_sub_C_neg4_reducible⟩

/-! ## Part 5: A concrete positive general-`a` instance in the covered regime

To confirm the "yes" half is usable, we instantiate the odd-exponent criterion.
Over `ℚ`, `X³ − a` is irreducible iff `a` is not a cube.  The identity
`(X − C b) ∣ (X³ − C (b³))` is the reducible boundary; here we simply record that
the packaged iff-lemma specialises to the exponent `3`. -/

/-- `X³ − a` (`a : K`) is irreducible iff `a` is not a perfect cube in `K`.
The divisors of the prime `3` are `1` and `3`, so the general odd criterion
collapses to a single cube test. -/
theorem irreducible_X3_sub_C_iff (a : K) :
    Irreducible (X ^ 3 - C a) ↔ ∀ b : K, b ^ 3 ≠ a := by
  rw [irreducible_X_pow_sub_C_odd_iff (by norm_num : Odd 3)]
  constructor
  · intro H b; exact H 3 (dvd_refl 3) (by norm_num) b
  · intro H d hd hd1 b
    -- divisors of the prime `3` are `1` and `3`; `d ≠ 1` forces `d = 3`
    obtain rfl : d = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h | h
      · exact absurd h hd1
      · exact h
    exact H b

end FourthRoot2Degree4OQ02OQ01

/-! ## Axiom audit

Confirms the headline results depend only on the foundational
`propext` / `Classical.choice` / `Quot.sound` — no `sorryAx`, no
`Lean.ofReduceBool` (i.e. no `native_decide`). -/

#print axioms FourthRoot2Degree4OQ02OQ01.irreducible_X_pow_sub_C_odd_iff
#print axioms FourthRoot2Degree4OQ02OQ01.irreducible_X_pow_sub_C_primePow_iff
#print axioms FourthRoot2Degree4OQ02OQ01.X4_add_4_reducible
#print axioms FourthRoot2Degree4OQ02OQ01.prime_divisor_criterion_insufficient
#print axioms FourthRoot2Degree4OQ02OQ01.irreducible_X3_sub_C_iff
