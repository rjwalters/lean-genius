/-
  ℚ-linear independence of distinct even zeta values
  (basel-problem-oq-01-oq-02)

  The node `BaselProblemOQ01OQ02.lean` develops the full `ℚ·π^(even)` closure algebra of
  the even zeta values `ζ(2n) = ∑' k, 1/k^(2n)`: single values, ratios, products, powers,
  finite/weighted products, polynomial evaluations, and pairwise sums/differences are all
  shown transcendental.  What that development never records is the **linear-algebra**
  structure over `ℚ`: distinct even zeta values are not merely individually transcendental,
  they are jointly `ℚ`-linearly independent.  This file supplies that fact — first for a
  pair, then for the whole family `ζ(2), ζ(4), …, ζ(2N)`.

    * `zeta_even_no_rational_relation` — for `0 < m < n`, the only rational solution of
      `a·ζ(2m) + b·ζ(2n) = 0` is `a = b = 0`.  (Strictly stronger than
      `zeta_even_add_transcendental` / `zeta_even_sub_transcendental`, which only exclude
      the special coefficients `(1, 1)` and `(1, -1)`.)
    * `zeta_even_linearIndependent_pair` — the packaged statement
      `LinearIndependent ℚ ![ζ(2m), ζ(2n)]`.
    * `zeta_two_zeta_four_linearIndependent` — the concrete Basel instance
      `LinearIndependent ℚ ![ζ(2), ζ(4)]`.
    * `zeta_even_linearIndependent_family` — the `N`-family generalization
      `LinearIndependent ℚ (fun i : Fin N ↦ ζ(2(i+1)))`, via a single polynomial identity
      at `π` and transcendence of `π` (strictly stronger than any collection of pairs).
    * `zeta_two_four_six_linearIndependent` — the concrete instance for `ζ(2), ζ(4), ζ(6)`.

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

open Real

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

/-- **The full family of even zeta values is `ℚ`-linearly independent.**  For every `N`,

      `LinearIndependent ℚ (fun i : Fin N ↦ ζ(2(i+1)))`,

    i.e. `ζ(2), ζ(4), …, ζ(2N)` are jointly `ℚ`-linearly independent.  This is the
    `N`-family generalization of `zeta_even_linearIndependent_pair` (strictly stronger than
    any finite collection of pairwise statements): the *only* rational vanishing relation
    `∑ᵢ gᵢ · ζ(2(i+1)) = 0` is the trivial one.

    **Proof.**  Euler gives `ζ(2(i+1)) = qᵢ · π^(2(i+1))` with `qᵢ ∈ ℚ∖{0}`, so a rational
    relation `∑ᵢ gᵢ ζ(2(i+1)) = 0` becomes `∑ᵢ (gᵢ qᵢ) π^(2(i+1)) = 0 = aeval π P` for the
    polynomial `P = ∑ᵢ C(gᵢ qᵢ) · X^(2(i+1)) ∈ ℚ[X]`.  Transcendence of `π` over `ℚ`
    (`transcendental_iff`, from `pi_transcendental_over_rationals`) forces `P = 0`; since the
    exponents `2(i+1)` are distinct, the coefficient of `X^(2(j+1))` is exactly `gⱼ qⱼ`, so
    `gⱼ qⱼ = 0`, and `qⱼ ≠ 0` gives `gⱼ = 0`.

    **Assumption:** `hermite_lindemann` (transcendence of `π`), via `pi_transcendental_over_rationals`.
    The reduction of linear independence to a single polynomial identity is axiom-free; the
    axiom enters only through the transcendence of `π`. -/
theorem zeta_even_linearIndependent_family (N : ℕ) :
    LinearIndependent ℚ
      (fun i : Fin N => (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * (i.val + 1)))) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  -- Euler closed form for each component, as a choice of nonzero rationals `qm`.
  have hq : ∀ i : Fin N, ∃ q : ℚ, q ≠ 0 ∧
      (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * (i.val + 1))) = (q : ℝ) * π ^ (2 * (i.val + 1)) :=
    fun i => BaselProblemOQ01OQ02.zeta_even_eq_rat_mul_pi_pow (i.val + 1) (Nat.succ_pos _)
  choose qm hqm0 hqmeq using hq
  -- Substitute Euler and convert the `ℚ`-scalar action to `ratCast` multiplication.
  have hsum' :
      (∑ i : Fin N, ((g i * qm i : ℚ) : ℝ) * π ^ (2 * (i.val + 1))) = 0 := by
    rw [← hsum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Rat.smul_def, hqmeq i]
    push_cast; ring
  -- The vanishing polynomial `P = ∑ C(g i · qm i) · X^(2(i+1))`.
  set P : Polynomial ℚ :=
    ∑ i : Fin N, Polynomial.C (g i * qm i) * Polynomial.X ^ (2 * (i.val + 1)) with hP
  have haeval : (Polynomial.aeval (π : ℝ)) P = 0 := by
    rw [hP, map_sum, ← hsum']
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, eq_ratCast]
  -- Transcendence of π over ℚ forces P = 0.
  have hPzero : P = 0 :=
    (transcendental_iff.mp pi_transcendental_over_rationals) P haeval
  -- Read off the coefficient of X^(2(j+1)): it is exactly g j · qm j.
  intro j
  have hcoeff : P.coeff (2 * (j.val + 1)) = g j * qm j := by
    rw [hP, Polynomial.finsetSum_coeff,
      Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro i _ hij
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      intro hcontra
      exact hij (Fin.ext (by omega : (i : ℕ) = j))
  rw [hPzero, Polynomial.coeff_zero] at hcoeff
  rcases mul_eq_zero.mp hcoeff.symm with h1 | h1
  · exact h1
  · exact absurd h1 (hqm0 j)

/-- **Concrete instance:** `ζ(2), ζ(4), ζ(6)` are `ℚ`-linearly independent. -/
theorem zeta_two_four_six_linearIndependent :
    LinearIndependent ℚ
      (fun i : Fin 3 => (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * (i.val + 1)))) :=
  zeta_even_linearIndependent_family 3

end BaselProblemOQ01OQ02LinIndep
