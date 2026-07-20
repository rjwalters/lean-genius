/-
  ℚ-linear independence of distinct even zeta values
  (basel-problem-oq-01-oq-02)

  The node `BaselProblemOQ01OQ02.lean` develops the full `ℚ·π^(even)` closure algebra of
  the even zeta values `ζ(2n) = ∑' k, 1/k^(2n)`: single values, ratios, products, powers,
  finite/weighted products, polynomial evaluations, and pairwise sums/differences are all
  shown transcendental.  What that development never records is the **linear-algebra**
  structure over `ℚ`: distinct even zeta values are not merely individually transcendental,
  they are jointly `ℚ`-linearly independent.  This file supplies that fact for a pair.

    * `zeta_even_no_rational_relation` — for `0 < m < n`, the only rational solution of
      `a·ζ(2m) + b·ζ(2n) = 0` is `a = b = 0`.  (Strictly stronger than
      `zeta_even_add_transcendental` / `zeta_even_sub_transcendental`, which only exclude
      the special coefficients `(1, 1)` and `(1, -1)`.)
    * `zeta_even_linearIndependent_pair` — the packaged statement
      `LinearIndependent ℚ ![ζ(2m), ζ(2n)]`.
    * `zeta_two_zeta_four_linearIndependent` — the concrete Basel instance
      `LinearIndependent ℚ ![ζ(2), ζ(4)]`.
    * `pi_sq_pow_linearIndependent` — the powers `{(π²)ⁱ}ᵢ` are `ℚ`-linearly independent
      (transcendence of `π²` ⟹ `aeval (π²)` injective ⟹ the monomial basis maps to an
      independent family).
    * `zeta_even_family_linearIndependent` — the `N`-family generalization
      `LinearIndependent ℚ (fun k : Fin N => ζ(2(k+1)))`: *all* the even zeta values
      `ζ(2), ζ(4), …, ζ(2N)` are jointly `ℚ`-linearly independent, not merely pairwise.
    * `zeta_two_four_six_linearIndependent` — the concrete triple `ζ(2), ζ(4), ζ(6)`.

  Mathematically: `ζ(2m) = qₘ·π^(2m)` and `ζ(2n) = qₙ·π^(2n)` with `qₘ, qₙ ∈ ℚ∖{0}`;
  a rational relation forces `a·qₘ + b·qₙ·π^(2(n-m)) = 0` after dividing by `π^(2m)`, and
  the irrationality of `π^(2(n-m))` then kills the `b`-term, hence the `a`-term.  So the even
  zeta values lie on distinct `ℚ`-lines through the origin of the transcendence-degree-`1`
  field `ℚ(π)`.

  Uses `hermite_lindemann` only through `π^m` irrationality (`pi_pow_irrational`, from the
  parent node); the rational-multiple skeleton is axiom-free.
-/
import Mathlib
import Proofs.BaselProblemOQ01OQ02

open Real Polynomial

namespace BaselProblemOQ01OQ02LinIndep

/-- **No nontrivial rational relation between two distinct even zeta values.**  For
    `0 < m < n`, the only rational pair `(a, b)` with

      `a · ζ(2m) + b · ζ(2n) = 0`

    is `(0, 0)`.  Equivalently, `ζ(2m)` and `ζ(2n)` are `ℚ`-linearly independent.

    Writing `ζ(2m) = qₘ π^(2m)`, `ζ(2n) = qₙ π^(2n)` (`qₘ, qₙ ≠ 0`, Euler), the relation
    becomes `π^(2m)·(a qₘ + b qₙ π^(2(n-m))) = 0`; since `π^(2m) ≠ 0` the bracket vanishes,
    and `b qₙ ≠ 0` would make `π^(2(n-m)) = -(a qₘ)/(b qₙ)` rational, contradicting
    `pi_pow_irrational`.  Hence `b = 0`, then `a = 0`. -/
theorem zeta_even_no_rational_relation (n m : ℕ) (hm : 0 < m) (hmn : m < n) (a b : ℚ)
    (h : (a : ℝ) * (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m))
        + (b : ℝ) * (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) = 0) :
    a = 0 ∧ b = 0 := by
  obtain ⟨qm, hqm, hm_eq⟩ := BaselProblemOQ01OQ02.zeta_even_eq_rat_mul_pi_pow m hm
  obtain ⟨qn, hqn, hn_eq⟩ := BaselProblemOQ01OQ02.zeta_even_eq_rat_mul_pi_pow n (by omega)
  rw [hm_eq, hn_eq] at h
  -- split off the shared factor π^(2m)
  have hsplit : (π : ℝ) ^ (2 * n) = π ^ (2 * m) * π ^ (2 * (n - m)) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit] at h
  have hpine : (π : ℝ) ^ (2 * m) ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  -- the bracket after factoring out π^(2m)
  have hbr : (a : ℝ) * (qm : ℝ) + (b : ℝ) * (qn : ℝ) * π ^ (2 * (n - m)) = 0 := by
    have factored :
        (π : ℝ) ^ (2 * m)
          * ((a : ℝ) * (qm : ℝ) + (b : ℝ) * (qn : ℝ) * π ^ (2 * (n - m))) = 0 := by
      rw [← h]; ring
    rcases mul_eq_zero.mp factored with h1 | h2
    · exact absurd h1 hpine
    · exact h2
  -- π^(2(n-m)) is irrational
  have hirr : Irrational (π ^ (2 * (n - m))) := BaselProblemOQ01OQ02.pi_pow_irrational _ (by omega)
  -- b·qn = 0, else π^(2(n-m)) would be rational
  have hbqn : (b * qn : ℚ) = 0 := by
    by_contra hne
    have hirrmul : Irrational (((b * qn : ℚ) : ℝ) * π ^ (2 * (n - m))) := hirr.ratCast_mul hne
    have heq : ((b * qn : ℚ) : ℝ) * π ^ (2 * (n - m)) = ((-(a * qm) : ℚ) : ℝ) := by
      push_cast; linarith [hbr]
    rw [heq] at hirrmul
    exact (Rat.not_irrational _) hirrmul
  -- hence b = 0
  have hb : b = 0 := by
    rcases mul_eq_zero.mp hbqn with h1 | h1
    · exact h1
    · exact absurd h1 hqn
  -- and then a = 0
  have ha : a = 0 := by
    rw [hb] at hbr
    simp only [Rat.cast_zero, zero_mul, zero_mul, add_zero] at hbr
    rcases mul_eq_zero.mp hbr with h1 | h1
    · exact_mod_cast h1
    · exact absurd (by exact_mod_cast h1 : qm = 0) hqm
  exact ⟨ha, hb⟩

/-- **Two distinct even zeta values are `ℚ`-linearly independent.**  For `0 < m < n`,

      `LinearIndependent ℚ ![ζ(2m), ζ(2n)]`.

    The packaged form of `zeta_even_no_rational_relation` via `LinearIndependent.pair_iff`.
    (Over `ℝ` as a `ℚ`-vector space, `s • x = (s : ℝ) * x`.) -/
theorem zeta_even_linearIndependent_pair (n m : ℕ) (hm : 0 < m) (hmn : m < n) :
    LinearIndependent ℚ
      ![(∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m)), (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n))] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  refine zeta_even_no_rational_relation n m hm hmn s t ?_
  rw [Rat.smul_def, Rat.smul_def] at hst
  exact hst

/-- **The Basel pair `ζ(2), ζ(4)` is `ℚ`-linearly independent.**  Concretely, no rational
    `a, b` (other than `0, 0`) satisfy `a·(π²/6) + b·(π⁴/90) = 0`. -/
theorem zeta_two_zeta_four_linearIndependent :
    LinearIndependent ℚ
      ![(∑' k : ℕ, 1 / (k : ℝ) ^ 2), (∑' k : ℕ, 1 / (k : ℝ) ^ 4)] := by
  exact zeta_even_linearIndependent_pair 2 1 one_pos (by norm_num)

/-! ### The `N`-family generalization

    The pair result above shows any two distinct even zeta values are `ℚ`-independent.  The
    real structural statement is that *all* of them are jointly independent: `{ζ(2k)}_{k≥1}`
    is a `ℚ`-linearly independent family.  The mechanism is the transcendence of `π²`.  Since
    `ζ(2(k+1)) = q_{k+1} · (π²)^(k+1)` with `q_{k+1} ∈ ℚ∖{0}` (Euler), the family is a nonzero
    rational rescaling of the powers `{(π²)^(k+1)}`, and powers of a transcendental element are
    linearly independent (the polynomial-evaluation map `ℚ[X] → ℝ` at `π²` is injective, so it
    carries the monomial basis to an independent family).  -/

/-- **Powers of `π²` are `ℚ`-linearly independent.**  `π²` is transcendental over `ℚ` (from
    transcendence of `π`), so `aeval (π²) : ℚ[X] → ℝ` is injective; it sends the monomial basis
    `{Xⁱ}` of `ℚ[X]` to the family `{(π²)ⁱ}`, which is therefore `ℚ`-linearly independent. -/
theorem pi_sq_pow_linearIndependent :
    LinearIndependent ℚ (fun i : ℕ => ((π : ℝ) ^ 2) ^ i) := by
  have htr : Transcendental ℚ ((π : ℝ) ^ 2) :=
    pi_transcendental_over_rationals.pow (by norm_num)
  have hinj : Function.Injective (Polynomial.aeval ((π : ℝ) ^ 2) : ℚ[X] →ₐ[ℚ] ℝ) :=
    transcendental_iff_injective.1 htr
  have hker :
      LinearMap.ker (Polynomial.aeval ((π : ℝ) ^ 2) : ℚ[X] →ₐ[ℚ] ℝ).toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.2 hinj
  have hb := (Polynomial.basisMonomials ℚ).linearIndependent.map'
      (Polynomial.aeval ((π : ℝ) ^ 2) : ℚ[X] →ₐ[ℚ] ℝ).toLinearMap hker
  have hfun :
      (Polynomial.aeval ((π : ℝ) ^ 2) : ℚ[X] →ₐ[ℚ] ℝ).toLinearMap ∘ ⇑(Polynomial.basisMonomials ℚ)
        = fun i : ℕ => ((π : ℝ) ^ 2) ^ i := by
    funext i
    simp [Polynomial.coe_basisMonomials, Polynomial.aeval_monomial]
  rwa [hfun] at hb

/-- **The `N`-family `ζ(2), ζ(4), …, ζ(2N)` is `ℚ`-linearly independent.**  For every `N`,

      `LinearIndependent ℚ (fun k : Fin N => ζ(2(k+1)))`.

    Strictly generalizes `zeta_even_linearIndependent_pair` (the `N = 2` slice with a
    reindexing).  Each `ζ(2(k+1)) = q_{k+1}·(π²)^(k+1)` with `q_{k+1} ∈ ℚ∖{0}` (Euler,
    `zeta_even_eq_rat_mul_pi_pow`), so the family is a nonzero-rational (unit) rescaling of the
    linearly independent powers `{(π²)^(k+1)}` (`pi_sq_pow_linearIndependent`, restricted to the
    shifted index `k ↦ k+1`, then `LinearIndependent.units_smul`).

    Uses `hermite_lindemann` only through the transcendence of `π` — no new assumption beyond the
    parent node. -/
theorem zeta_even_family_linearIndependent (N : ℕ) :
    LinearIndependent ℚ
      (fun k : Fin N => (∑' j : ℕ, 1 / (j : ℝ) ^ (2 * (k.val + 1)))) := by
  -- Shifted powers of π² are linearly independent (restrict the full ℕ-indexed family).
  have hshift : Function.Injective (fun k : Fin N => k.val + 1) :=
    Nat.succ_injective.comp Fin.val_injective
  have hbase : LinearIndependent ℚ (fun k : Fin N => ((π : ℝ) ^ 2) ^ (k.val + 1)) :=
    pi_sq_pow_linearIndependent.comp _ hshift
  -- Euler's closed form supplies, for each k, a nonzero rational qₖ with ζ(2(k+1)) = qₖ·π^(2(k+1)).
  choose q hqne hqeq using fun k : Fin N =>
    BaselProblemOQ01OQ02.zeta_even_eq_rat_mul_pi_pow (k.val + 1) (Nat.succ_pos _)
  -- Rescale the base family by the units qₖ; linear independence is preserved.
  have hscaled := hbase.units_smul (fun k : Fin N => Units.mk0 (q k) (hqne k))
  -- Identify the rescaled family with the zeta family.
  have hfun :
      (fun k : Fin N => (∑' j : ℕ, 1 / (j : ℝ) ^ (2 * (k.val + 1))))
        = (fun k : Fin N => Units.mk0 (q k) (hqne k))
            • (fun k : Fin N => ((π : ℝ) ^ 2) ^ (k.val + 1)) := by
    funext k
    simp only [Pi.smul_apply', Units.smul_def, Units.val_mk0, Rat.smul_def]
    rw [hqeq k, pow_mul]
  rw [hfun]
  exact hscaled

/-- **The concrete Basel triple `ζ(2), ζ(4), ζ(6)` is `ℚ`-linearly independent.**  The `N = 3`
    instance of `zeta_even_family_linearIndependent`. -/
theorem zeta_two_four_six_linearIndependent :
    LinearIndependent ℚ
      ![(∑' k : ℕ, 1 / (k : ℝ) ^ 2), (∑' k : ℕ, 1 / (k : ℝ) ^ 4),
        (∑' k : ℕ, 1 / (k : ℝ) ^ 6)] := by
  have h := zeta_even_family_linearIndependent 3
  have heq :
      (fun k : Fin 3 => (∑' j : ℕ, 1 / (j : ℝ) ^ (2 * (k.val + 1))))
        = ![(∑' k : ℕ, 1 / (k : ℝ) ^ 2), (∑' k : ℕ, 1 / (k : ℝ) ^ 4),
            (∑' k : ℕ, 1 / (k : ℝ) ^ 6)] := by
    funext k
    fin_cases k <;> rfl
  rwa [heq] at h

end BaselProblemOQ01OQ02LinIndep
