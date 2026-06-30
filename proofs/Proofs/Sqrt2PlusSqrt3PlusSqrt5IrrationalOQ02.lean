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

## STATUS — partial: endpoints + Besicovitch reduction discharged, induction core open

This file records the *decomposition* into the load-bearing lemmas. The single
non-trivial step is `sqrt_prime_not_mem_multiquadratic` (the induction heart);
everything else is either a Mathlib one-liner (base case, upper bound) or follows
from the degree theorem by linear algebra.

Discharged (no sorry): `irrational_sqrt_prime` (`Nat.Prime.irrational_sqrt`),
`irrational_sqrt2_add_sqrt3_add_sqrt5` (the OQ-01 corollary, by direct citation of
the proved `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01` — see note there), and
`besicovitch_sqrt_linearIndependent` (the squarefree main statement) which is now a
genuine **derivation** from `multiquadratic_subset_products_linearIndependent` via the
`d ↦ primeFactors d` injection (`LinearIndependent.comp` +
`Nat.prod_primeFactors_of_squarefree`). Still `sorry`: the induction heart
`sqrt_prime_not_mem_multiquadratic` and the degree theorem
`multiquadratic_subset_products_linearIndependent` that consumes it. These statements
have NOT yet been checked by the Lean elaborator (no build this session); the file
remains unregistered pending a Docker build.

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
`multiquadratic_subset_products_linearIndependent`.

This is now a **genuine derivation** (no `sorry` of its own) from the degree theorem:
take `ps = ⋃_{d∈S} primeFactors d`; the map `d ↦ primeFactors d` injects `S` into
`ps.powerset` (squarefree ⇒ `∏ primeFactors d = d`, so distinct `d` give distinct factor
sets), and `√d = √(∏_{q | d} q)` identifies the family with a subfamily of the
multiquadratic basis. Linear independence is then inherited via `LinearIndependent.comp`.
Only the upstream `multiquadratic_subset_products_linearIndependent` (and through it the
induction heart) remains open. -/
theorem besicovitch_sqrt_linearIndependent
    (S : Finset ℕ) (hS : ∀ d ∈ S, Squarefree d) :
    LinearIndependent ℚ (fun d : S => (Real.sqrt ((d : ℕ) : ℝ) : ℝ)) := by
  classical
  -- All primes occurring among the radicands.
  set ps : Finset ℕ := S.biUnion (fun d => d.primeFactors) with hps_def
  have hps : ∀ q ∈ ps, q.Prime := by
    intro q hq
    rw [hps_def, Finset.mem_biUnion] at hq
    obtain ⟨d, _, hqd⟩ := hq
    exact Nat.prime_of_mem_primeFactors hqd
  -- The multiquadratic subset-product basis is ℚ-linearly independent (degree theorem).
  have hmq := multiquadratic_subset_products_linearIndependent ps hps
  -- `d ↦ primeFactors d` lands in `ps.powerset`.
  have hsub : ∀ d ∈ S, d.primeFactors ∈ ps.powerset := by
    intro d hd
    rw [Finset.mem_powerset, hps_def]
    exact Finset.subset_biUnion_of_mem (fun d => d.primeFactors) hd
  -- and is injective on `S` (squarefree numbers are recovered from their prime sets).
  let ι : {d // d ∈ S} → {T // T ∈ ps.powerset} :=
    fun d => ⟨(d : ℕ).primeFactors, hsub d.1 d.2⟩
  have hι : Function.Injective ι := by
    intro a b hab
    have hpf : (a : ℕ).primeFactors = (b : ℕ).primeFactors := by
      simpa [ι] using congrArg Subtype.val hab
    have hval : (a : ℕ) = (b : ℕ) := by
      rw [← Nat.prod_primeFactors_of_squarefree (hS a.1 a.2),
          ← Nat.prod_primeFactors_of_squarefree (hS b.1 b.2), hpf]
    exact Subtype.ext hval
  -- The target family is exactly the multiquadratic family restricted along `ι`.
  have hfun : (fun d : S => (Real.sqrt ((d : ℕ) : ℝ) : ℝ))
      = (fun T : ps.powerset => (Real.sqrt (∏ q ∈ (T : Finset ℕ), (q : ℝ)) : ℝ)) ∘ ι := by
    funext d
    have hcoe : ((ι d : {T // T ∈ ps.powerset}) : Finset ℕ) = (d : ℕ).primeFactors := rfl
    simp only [Function.comp_apply]
    rw [hcoe, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree (hS d.1 d.2)]
  rw [hfun]
  exact hmq.comp ι hι

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
