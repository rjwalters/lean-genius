/-
  ℚ-linear independence of the full family of consecutive even zeta values
  (basel-problem-oq-01-oq-02)

  The sibling `BaselProblemOQ01OQ02LinIndep.lean` establishes that a *pair* of distinct
  even zeta values `ζ(2m), ζ(2n)` is `ℚ`-linearly independent.  This file lifts that fact
  from pairs to the **entire finite family** of consecutive even zeta values:

      `LinearIndependent ℚ (fun k : Fin N => ζ(2(k+1)))`   for every `N`,

  i.e. `ζ(2), ζ(4), ζ(6), …, ζ(2N)` satisfy no nontrivial rational linear relation, all at
  once.  This is a genuine `N`-family generalization of the pair result, not a corollary of
  it (the pair theorem only excludes two-term relations).

  The mechanism is the transcendence-degree-`1` structure of `ℚ(π)`.  Concretely:

    * `pi_sq_pow_linearIndependent` — the powers `(π²)⁰, (π²)¹, (π²)², …` are `ℚ`-linearly
      independent.  This is exactly the transcendence of `π²` over `ℚ`, packaged through
      `Polynomial.linearIndependent_powers_iff_aeval` applied to the multiplication
      endomorphism `Algebra.lmul ℚ ℝ (π²)`.
    * `zeta_even_family_linearIndependent` — reindex those powers to the exponents `1, …, N`
      (an injective reindexing, `LinearIndependent.comp`) and rescale each by the nonzero
      rational `qₖ` from Euler's `ζ(2(k+1)) = qₖ·π^(2(k+1))` (`LinearIndependent.units_smul`).
      Rescaling a `ℚ`-independent family by nonzero *rationals* preserves independence, and
      `π^(2(k+1)) = (π²)^(k+1)`, so the rescaled powers are precisely the even zeta values.

  Axioms: uses `hermite_lindemann` only through the transcendence of `π` (via
  `pi_transcendental_over_rationals`); the Euler rational-multiple skeleton
  `zeta_even_eq_rat_mul_pi_pow` is itself axiom-free.
-/
import Mathlib
import Proofs.BaselProblemOQ01OQ02

open Real Polynomial

namespace BaselProblemOQ01OQ02FamilyLinIndep

open BaselProblemOQ01OQ02

/-- **Powers of `π²` are `ℚ`-linearly independent.**  The family `(π²)⁰, (π²)¹, (π²)², …`
    (equivalently `1, π², π⁴, …`) admits no nontrivial finite rational linear relation.

    This is a repackaging of the transcendence of `π²` over `ℚ`
    (`pi_transcendental_over_rationals.pow`): via
    `Polynomial.linearIndependent_powers_iff_aeval` for the multiplication endomorphism
    `f = Algebra.lmul ℚ ℝ (π²)` (which satisfies `(fⁿ) 1 = (π²)ⁿ`), linear independence of
    the powers is equivalent to injectivity of `aeval (π²)`, i.e. to transcendence. -/
theorem pi_sq_pow_linearIndependent :
    LinearIndependent ℚ (fun n : ℕ => (π ^ 2 : ℝ) ^ n) := by
  have hpisq : Transcendental ℚ (π ^ 2 : ℝ) :=
    pi_transcendental_over_rationals.pow (by norm_num)
  -- `(fⁿ) 1 = (π²)ⁿ` for the multiplication endomorphism `f = Algebra.lmul ℚ ℝ (π²)`.
  have hfn : ∀ n : ℕ, ((Algebra.lmul ℚ ℝ (π ^ 2)) ^ n) (1 : ℝ) = (π ^ 2) ^ n := by
    intro n
    rw [← map_pow]
    simp
  -- linear independence of the endomorphism powers applied to `1`
  have key : LinearIndependent ℚ
      (fun n : ℕ => ((Algebra.lmul ℚ ℝ (π ^ 2)) ^ n) (1 : ℝ)) := by
    rw [Polynomial.linearIndependent_powers_iff_aeval]
    intro p hp
    apply transcendental_iff.mp hpisq p
    rw [aeval_algHom_apply] at hp
    simpa using hp
  simpa only [hfn] using key

/-- **The consecutive even zeta values are jointly `ℚ`-linearly independent.**  For every `N`,

      `LinearIndependent ℚ (fun k : Fin N => ∑' j, 1 / j^(2(k+1)))`,

    i.e. `ζ(2), ζ(4), …, ζ(2N)` satisfy no nontrivial rational linear relation.

    Proof: reindex the `ℚ`-independent powers `(π²)ⁿ` (`pi_sq_pow_linearIndependent`) to the
    exponents `1, …, N` via the injective map `k ↦ k+1` (`LinearIndependent.comp`), then
    rescale the `k`-th vector by the nonzero rational `qₖ` from Euler's closed form
    `ζ(2(k+1)) = qₖ · π^(2(k+1))` (`LinearIndependent.units_smul`; rescaling by nonzero
    rationals preserves `ℚ`-independence).  Since `π^(2(k+1)) = (π²)^(k+1)`, the rescaled
    powers are exactly the even zeta values. -/
theorem zeta_even_family_linearIndependent (N : ℕ) :
    LinearIndependent ℚ
      (fun k : Fin N => ∑' j : ℕ, 1 / (j : ℝ) ^ (2 * ((k : ℕ) + 1))) := by
  -- reindex the powers of π² to the exponents 1, …, N
  have hinj : Function.Injective (fun k : Fin N => (k : ℕ) + 1) := by
    intro a b hab
    simp only at hab
    exact Fin.ext (by omega)
  have hpiFam : LinearIndependent ℚ (fun k : Fin N => (π ^ 2 : ℝ) ^ ((k : ℕ) + 1)) :=
    pi_sq_pow_linearIndependent.comp (fun k : Fin N => (k : ℕ) + 1) hinj
  -- Euler: choose the nonzero rational scalars qₖ with ζ(2(k+1)) = qₖ·π^(2(k+1))
  choose q hq hzeta using
    fun k : Fin N => zeta_even_eq_rat_mul_pi_pow ((k : ℕ) + 1) (Nat.succ_pos _)
  -- rescale each π²-power by the nonzero unit qₖ
  have hscaled := hpiFam.units_smul (fun k : Fin N => Units.mk0 (q k) (hq k))
  -- the rescaled family is exactly the zeta family
  have hEq : (fun k : Fin N => ∑' j : ℕ, 1 / (j : ℝ) ^ (2 * ((k : ℕ) + 1)))
      = (fun k : Fin N => Units.mk0 (q k) (hq k)) •
          (fun k : Fin N => (π ^ 2 : ℝ) ^ ((k : ℕ) + 1)) := by
    funext k
    rw [hzeta k, pow_mul]
    simp [Pi.smul_apply', Units.smul_def, Rat.smul_def]
  rw [hEq]
  exact hscaled

/-- **The Basel initial segment `ζ(2), ζ(4), ζ(6)` is `ℚ`-linearly independent.**  The
    concrete `N = 3` instance of `zeta_even_family_linearIndependent`. -/
theorem zeta_two_four_six_linearIndependent :
    LinearIndependent ℚ
      (fun k : Fin 3 => ∑' j : ℕ, 1 / (j : ℝ) ^ (2 * ((k : ℕ) + 1))) :=
  zeta_even_family_linearIndependent 3

end BaselProblemOQ01OQ02FamilyLinIndep
