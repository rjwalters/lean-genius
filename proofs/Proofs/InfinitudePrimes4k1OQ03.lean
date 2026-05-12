import Proofs.InfinitudePrimes4k1
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Density 1/2 of Primes ≡ 1 (mod 4) — OQ-03

## What This File Aims to Establish

The parent file `Proofs/InfinitudePrimes4k1.lean` proves the *infinitude* of
primes `p ≡ 1 (mod 4)` by an elementary argument (Fermat sums-of-two-squares
+ Euler's criterion). This OQ asks for the strictly stronger statement:

$$
\lim_{N \to \infty} \frac{\#\{p \le N : p \text{ prime},\, p \equiv 1 \pmod 4\}}{\pi(N)}
  \;=\; \tfrac{1}{2}.
$$

This is the **natural-density** form of Dirichlet's theorem for `(q, a) = (4, 1)`
— a specialization of the prime number theorem for arithmetic progressions
(PNT-AP).

## Mathlib Status at v4.26.0 (S2, 2026-05-12)

A direct inspection of `Mathlib.NumberTheory.LSeries.PrimesInAP` at the pinned
revision `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) shows:

* **The infinitude form is available**, exported as `Nat.infinite_setOf_prime_and_eq_mod`.
* **The natural-density form is NOT available**. There is no
  `Mathlib.NumberTheory.LSeries.Wiener` or `Mathlib.NumberTheory.LSeries.IkeharaTauberian`
  module at this pin, and no theorem of the form
  `Nat.setOf_prime_and_eq_mod_div_smul_tendsto_inv_totient`.

The S1 OBSERVE plan (in `state.md`) assumed the density form was already in
Mathlib; this was over-optimistic. The closest quantitative lemma at this pin is
`ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`, which states
that the L-series of the von Mangoldt function restricted to a residue class
has a pole of strength `1/φ(q)` at `s = 1`. This is the **Dirichlet-density**
data, not the natural-density data.

## Scope of S2 (this iteration)

1. **Mathlib-bridge infinitude (verified).** Connect the parent file's
   elementary infinitude statement to Mathlib's general Dirichlet's theorem,
   specialized to `(q, a) = (4, 1)`. The result is identical in content but
   demonstrates the path from the gallery proof to Mathlib's analytic machinery.

2. **State the natural-density target (sorry).** Declare the OQ-03 deliverable
   as a Lean statement, marked `sorry`, so future iterations have a concrete
   syntactic target.

## Future Work (S3+)

* **S3a (Mathlib upgrade path).** When Mathlib gains an Ikehara-Tauberian
  module — e.g. `Mathlib.NumberTheory.LSeries.Wiener` — instantiate it for
  `(q, a) = (4, 1)` and discharge the `sorry`.
* **S3b (Dirichlet density side-step).** State and prove the *Dirichlet-density*
  form of the question via `LSeries_residueClass_lower_bound` + the matching
  upper bound; this is achievable at the current Mathlib pin and gives a
  formally weaker but pedagogically equivalent result.
* **S3c (Sum-of-two-squares corollary).** Combine the density form with
  Fermat's two-square theorem (`Mathlib.NumberTheory.SumTwoSquares`).

## Status
* Mathlib bridge to infinitude: **verified**.
* Natural-density theorem: **stated, with `sorry`** (OQ-03 target).
* No axiom declarations introduced.
-/

namespace InfinitudePrimes4k1OQ03

open Nat Filter Topology

/-! ## Auxiliary: `Nat.totient 4 = 2` and `1` is a unit mod 4 -/

/-- The reduced residues mod 4 are `{1, 3}`, so `φ(4) = 2`. -/
lemma totient_four : Nat.totient 4 = 2 := by decide

/-- `1` is a unit in `ZMod 4`. -/
lemma one_isUnit_zmodFour : IsUnit (1 : ZMod 4) := isUnit_one

/-! ## Translating between `p % 4 = 1` and `(p : ZMod 4) = 1` -/

/-- For natural-number `p`, the residue-class condition `p % 4 = 1` is
equivalent to `(p : ZMod 4) = 1`. -/
lemma mod_four_eq_one_iff_zmodFour_eq_one {p : ℕ} :
    p % 4 = 1 ↔ (p : ZMod 4) = 1 := by
  have h1 : (1 : ZMod 4) = ((1 : ℕ) : ZMod 4) := by norm_cast
  rw [h1, ZMod.natCast_eq_natCast_iff, Nat.ModEq]
  constructor
  · intro h; omega
  · intro h; omega

/-! ## Mathlib bridge: infinitude form -/

/-- **Mathlib bridge (infinitude form).** There are infinitely many primes
`p` with `(p : ZMod 4) = 1`, i.e. `p ≡ 1 (mod 4)`. This is
`Nat.infinite_setOf_prime_and_eq_mod` from
`Mathlib.NumberTheory.LSeries.PrimesInAP`, specialized to `(q, a) = (4, 1)`.

This is **strictly weaker** than the elementary parent statement
`InfinitudePrimes4k1.primes_1_mod_4_infinite` in the sense that the parent
uses no analytic input; but it is *the* statement that connects this file to
Mathlib's L-series machinery, which is the only known route to the density
form. -/
theorem primes_4k1_infinite_mathlib :
    {p : ℕ | p.Prime ∧ (p : ZMod 4) = 1}.Infinite :=
  Nat.infinite_setOf_prime_and_eq_mod one_isUnit_zmodFour

/-- The same statement in the `p % 4 = 1` formulation used by the parent file. -/
theorem primes_4k1_infinite_mod :
    {p : ℕ | p.Prime ∧ p % 4 = 1}.Infinite := by
  have key := primes_4k1_infinite_mathlib
  have hset : {p : ℕ | p.Prime ∧ (p : ZMod 4) = 1} =
      {p : ℕ | p.Prime ∧ p % 4 = 1} := by
    ext p
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro _
    exact (mod_four_eq_one_iff_zmodFour_eq_one).symm
  exact hset ▸ key

/-! ## OQ-03 target: natural-density form -/

/-- **OQ-03 deliverable (stated, not yet proved).**
The natural density of primes `≡ 1 (mod 4)` among all primes is `1/2`.

This is the natural-density form of Dirichlet's theorem for `(q, a) = (4, 1)`;
equivalently, the prime number theorem for arithmetic progressions specialized
to `(q, a) = (4, 1)`.

**Status (Mathlib v4.26.0):** The proof is currently blocked on the lack of
an Ikehara-Tauberian module in Mathlib at the pinned revision. The L-series
infrastructure needed for the proof is *present*
(`DirichletCharacter.LFunction`, `LSeries_residueClass_lower_bound`,
`LFunction_ne_zero_of_one_le_re`), but the Tauberian transfer from the
L-series pole strength to the prime-counting asymptotic is not yet exposed.

**Proof outline (when Mathlib supports it):**

1. By Dirichlet character orthogonality on `(ℤ/4ℤ)ˣ`, the indicator function
   of `{p : p ≡ 1 (mod 4)}` decomposes as `(1/2)(χ₀(p) + χ₁(p))` where
   `χ₀` is the trivial character mod 4 and `χ₁` is the unique nontrivial
   real character.
2. Apply PNT-AP (Ikehara-Tauberian on the L-series) to extract the
   asymptotic `π(N; 4, 1) ~ (1/2) · π(N)`.
3. Divide and take limits.

Using `Set.indicator (fun _ => (1 : ℝ))` keeps the statement purely in terms of
finset cardinality on `Finset.range`, matching common Mathlib conventions for
prime-counting asymptotics.
-/
theorem primes_4k1_natural_density :
    Tendsto
      (fun N : ℕ =>
        (((Finset.range (N + 1)).filter (fun p => p.Prime ∧ p % 4 = 1)).card : ℝ)
          / ((Finset.range (N + 1)).filter Nat.Prime).card)
      atTop (𝓝 (1 / 2)) := by
  sorry

/-! ## Sanity checks -/

#check primes_4k1_infinite_mathlib
#check primes_4k1_infinite_mod
#check primes_4k1_natural_density

end InfinitudePrimes4k1OQ03
