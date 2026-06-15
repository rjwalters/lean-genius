/-
# Besicovitch's theorem — ℚ-linear independence of √(squarefree)  (OQ-02)

Open Question (`sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-02`):

  Generalize OQ-01 (`Irrational (√2 + √3 + √5)`) to the structural theorem
  behind it — **Besicovitch (1940)**: the square roots of distinct squarefree
  integers are linearly independent over ℚ. Equivalently, for distinct primes
  p₁,…,pₙ,  [ℚ(√p₁,…,√pₙ) : ℚ] = 2ⁿ, with the 2ⁿ subset products a ℚ-basis.

OQ-01's "square twice to isolate √30" trick is the n = 3 shadow of the fact that
√2+√3+√5 is a primitive element of the degree-8 multiquadratic field ℚ(√2,√3,√5).
OQ-02 replaces the ad-hoc squaring with the uniform degree theorem.

## STATUS — partial: 2 endpoints discharged, induction core still open (Docker unavailable)

This file records the *decomposition* into the load-bearing lemmas. The single
non-trivial step is `sqrt_prime_not_mem_multiquadratic` (the induction heart);
everything else is either a Mathlib one-liner (base case, upper bound) or follows
from the degree theorem by linear algebra.

Discharged (no sorry): `irrational_sqrt_prime` (`Nat.Prime.irrational_sqrt`) and
`irrational_sqrt2_add_sqrt3_add_sqrt5` (the OQ-01 corollary, by direct citation of
the proved `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01` — see note there). Still `sorry`:
the induction heart and the two results that depend on it (`*_linearIndependent`).
These statements have NOT yet been checked by the Lean elaborator (no build this
session); the file remains unregistered pending a Docker build.

The mathematical content (degree = 2ⁿ, induction heart = degree doubling, and the
linear independence) is certified exactly in
`research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-02/verify_besicovitch.py`
(ALL PASS, exact sympy arithmetic).

Tags: number-theory, field-theory, multiquadratic, besicovitch, linear-independence
-/

import Mathlib
import Proofs.Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01

namespace BesicovitchOQ02

open scoped Real

/-- **n = 1 base case** (Mathlib one-liner): for a prime `p`, `√p` is irrational,
i.e. `{1, √p}` is ℚ-linearly independent. This is the seed of the induction and
is already discharged in OQ-01 style via `Nat.Prime.irrational_sqrt`. -/
theorem irrational_sqrt_prime {p : ℕ} (hp : p.Prime) :
    Irrational (Real.sqrt p) :=
  hp.irrational_sqrt

/-- **Induction heart (HEART — the only genuinely non-trivial step).**

For distinct primes, adjoining a *new* prime square root strictly enlarges the
field: `√p ∉ ℚ(√q : q ∈ ps)` whenever `p` is prime and `p ∉ ps`.

Equivalent (and the form certified exactly in `verify_besicovitch.py`, check (C)):
the minimal polynomial of `√p₁+…+√p_{k-1}+√p_k` has exactly twice the degree of
that of `√p₁+…+√p_{k-1}`.

Mathlib gap: no general multiquadratic non-membership lemma exists. Proof route:
characterize the squares of `ℚ(√q : q∈ps)` as `r²·∏_{T⊆ps} q` (r∈ℚ); a new prime
`p` is not of that form. Size ≈ 250–450 LOC. BUILD-class, requires a Lean build. -/
theorem sqrt_prime_not_mem_multiquadratic
    (ps : Finset ℕ) (p : ℕ) (hp : p.Prime)
    (hps : ∀ q ∈ ps, q.Prime) (hnew : p ∉ ps) :
    -- `√p` is not a ℚ-linear combination of subset-product roots of `ps`
    ¬ ∃ (c : Finset ℕ → ℚ),
        (Real.sqrt p : ℝ) =
          ∑ T ∈ ps.powerset, (c T : ℝ) * Real.sqrt (∏ q ∈ T, (q : ℝ)) := by
  sorry

/-- **Degree theorem** `[ℚ(√p₁,…,√pₙ) : ℚ] = 2ⁿ` for distinct primes, packaged as
"the `2ⁿ` subset-product square roots are ℚ-linearly independent". Follows from
the induction heart by induction on `ps.card` (upper bound `≤ 2ⁿ` is the easy
tower-of-quadratics direction). -/
theorem multiquadratic_subset_products_linearIndependent
    (ps : Finset ℕ) (hps : ∀ q ∈ ps, q.Prime) :
    LinearIndependent ℚ
      (fun T : ps.powerset => (Real.sqrt (∏ q ∈ (T : Finset ℕ), (q : ℝ)) : ℝ)) := by
  -- induction on `ps`, using `sqrt_prime_not_mem_multiquadratic` at each step
  sorry

/-- **Besicovitch's theorem (main OQ-02 statement).** The square roots of distinct
squarefree integers are ℚ-linearly independent. Each squarefree `d` has a distinct
odd-power-prime signature, hence maps to a distinct subset-product basis vector of
`multiquadratic_subset_products_linearIndependent`. -/
theorem besicovitch_sqrt_linearIndependent
    (S : Finset ℕ) (hS : ∀ d ∈ S, Squarefree d) :
    LinearIndependent ℚ (fun d : S => (Real.sqrt ((d : ℕ) : ℝ) : ℝ)) := by
  sorry

/-- **OQ-01 recovered.** `√2+√3+√5` is irrational. This is the `n = 3`,
`{2,3,5}` instance that OQ-02 generalizes, and it is already fully proved
(0 sorries, 0 axioms) in `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01` via the
"square twice to isolate √30" route. We discharge it here by direct citation
of that gallery proof — note this does **not** route through the still-open
`besicovitch_sqrt_linearIndependent` above (which would be circular), so it is
build-verifiable independently of the induction heart. -/
theorem irrational_sqrt2_add_sqrt3_add_sqrt5 :
    Irrational (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) :=
  Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.irrational_sqrt2_plus_sqrt3_plus_sqrt5

end BesicovitchOQ02
