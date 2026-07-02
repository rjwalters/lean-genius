import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Tactic

/-
# Factorial Moments of the Fixed-Point Count Are All 1 (Poisson(1) Hallmark)

Let `X_n = #{fixed points of a uniformly random σ ∈ S_n}`. This file proves that
every falling-factorial ("factorial") moment of `X_n` equals `1`:

  E[(X_n)_r] = E[ X_n (X_n - 1) ⋯ (X_n - r + 1) ] = 1        for all 0 ≤ r ≤ n.

This is the signature of the Poisson(1) distribution: a Poisson(λ) variable has
`r`-th factorial moment `λ^r`, so `λ = 1` gives all factorial moments equal to `1`.
It is the exact, finite-`n` analogue of the parent's asymptotic statement
`D_k(n)/n! → e⁻¹/k!` (`derangements-convergence-oq-05`).

## Proof

Working with counts rather than measures, the expectation of a function `g` of
`σ` is `(1/n!) ∑_{σ ∈ S_n} g(σ)`, so the claim `E[(X_n)_r] = 1` is the sum identity

  `∑_{σ ∈ S_n} (X_n(σ))_r = n!`.                                     (★)

The falling factorial counts ordered `r`-tuples of distinct fixed points, and
`(X)_r = r! · C(X, r)`, where `C(X, r)` counts the `r`-element *subsets* of the
fixed-point set. Summing over `σ` and swapping the order of summation,

  `∑_σ (X_σ)_r = r! · ∑_{|S| = r} #{ σ : S ⊆ Fix σ }`,

and a permutation fixes a given `r`-set `S` pointwise iff it restricts to an
arbitrary permutation of the complement, of which there are `(n - r)!`
(`card_perm_fixesPointwise`). Hence

  `∑_σ (X_σ)_r = r! · C(n, r) · (n - r)! = n!`

by `Nat.choose_mul_factorial_mul_factorial`.

## Main results

* `card_perm_fixesPointwise` : for a set `S`, `#{ σ ∈ S_n : σ fixes S pointwise } = (n - |S|)!`.
* `sum_descFactorial_fixedPoints` : the sum identity (★), `∑_σ (X_σ)_r = n!` for `r ≤ n`.
* `factorial_moment_eq_one` : the `r`-th factorial moment `E[(X_n)_r] = 1` (as a real).

The `card_perm_fixesPointwise` counting lemma reuses Mathlib's
`Equiv.Perm.subtypeEquivSubtypePerm` (permutations of a subtype ≃ permutations of
the whole type fixing the rest pointwise); the factorial-moment identity is not in
Mathlib.
-/

open Equiv Function Finset
open scoped BigOperators

namespace DerangementsFactorialMoments

variable {n : ℕ}

/-- The fixed-point set of `σ`, as a `Finset`. -/
private abbrev fixedSet (σ : Perm (Fin n)) : Finset (Fin n) :=
  univ.filter (fun i => σ i = i)

/-- **Counting permutations that fix a set pointwise.** For any `S ⊆ Fin n`, the
permutations of `Fin n` that fix every element of `S` are in bijection with the
permutations of the complement `Sᶜ`; hence there are `(n - |S|)!` of them.

A permutation fixing `S` pointwise necessarily permutes the complement, and
conversely any permutation of the complement extends by the identity on `S`. -/
theorem card_perm_fixesPointwise (S : Finset (Fin n)) :
    (univ.filter (fun σ : Perm (Fin n) => ∀ i ∈ S, σ i = i)).card
      = (n - S.card).factorial := by
  classical
  rw [← Fintype.card_subtype]
  -- `Perm ↥Sᶜ ≃ {σ // σ fixes S pointwise}` via `subtypeEquivSubtypePerm (· ∉ S)`.
  let e : Perm {a : Fin n // a ∉ S} ≃ {σ : Perm (Fin n) // ∀ i ∈ S, σ i = i} :=
    (Equiv.Perm.subtypeEquivSubtypePerm (fun a : Fin n => a ∉ S)).trans
      (Equiv.subtypeEquivRight (by intro σ; simp only [not_not]))
  rw [← Fintype.card_congr e, Fintype.card_perm]
  -- `card {a // a ∉ S} = n - |S|`.
  have h1 : Fintype.card {a : Fin n // a ∈ S} = S.card := by simp
  have hcard : Fintype.card {a : Fin n // a ∉ S} = n - S.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, h1]
  rw [hcard]

/-- **The factorial-moment sum identity (★).** Summing the `r`-th falling factorial
of the fixed-point count over all permutations of `Fin n` gives exactly `n!`, for
every `r ≤ n`. Dividing by `n!` yields `E[(X_n)_r] = 1`. -/
theorem sum_descFactorial_fixedPoints (n r : ℕ) (hr : r ≤ n) :
    ∑ σ : Perm (Fin n), ((fixedSet σ).card).descFactorial r = n.factorial := by
  classical
  -- Rewrite each falling factorial as `r! · #{r-subsets of the fixed set}`, expressed
  -- as a sum of indicators over the `r`-subsets `S` of `Fin n`.
  have hterm : ∀ σ : Perm (Fin n),
      ((fixedSet σ).card).descFactorial r
        = r.factorial * ∑ S ∈ powersetCard r (univ : Finset (Fin n)),
            (if S ⊆ fixedSet σ then 1 else 0) := by
    intro σ
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    congr 1
    -- `C(|F|, r) = |powersetCard r F| = ∑_{|S|=r} [S ⊆ F]`.
    rw [← Finset.card_powersetCard]
    have hsub : powersetCard r (fixedSet σ)
        = (powersetCard r (univ : Finset (Fin n))).filter (· ⊆ fixedSet σ) := by
      ext T
      simp only [mem_powersetCard, mem_filter, Finset.subset_univ, true_and]
      tauto
    rw [hsub, Finset.card_filter]
  rw [Finset.sum_congr rfl (fun σ _ => hterm σ)]
  -- Pull `r!` out and swap the order of summation.
  rw [← Finset.mul_sum, Finset.sum_comm]
  -- The inner sum over `σ` counts permutations fixing `S` pointwise: `(n - |S|)!`.
  have hinner : ∀ S ∈ powersetCard r (univ : Finset (Fin n)),
      ∑ σ : Perm (Fin n), (if S ⊆ fixedSet σ then 1 else 0) = (n - r).factorial := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    have hcard : (univ.filter (fun σ : Perm (Fin n) => S ⊆ fixedSet σ)).card
        = (n - S.card).factorial := by
      have : (univ.filter (fun σ : Perm (Fin n) => S ⊆ fixedSet σ))
          = univ.filter (fun σ : Perm (Fin n) => ∀ i ∈ S, σ i = i) := by
        apply Finset.filter_congr
        intro σ _
        constructor
        · intro h i hi
          have := h hi
          simp only [fixedSet, mem_filter, mem_univ, true_and] at this
          exact this
        · intro h x hx
          simp only [fixedSet, mem_filter, mem_univ, true_and]
          exact h x hx
      rw [this, card_perm_fixesPointwise]
    rw [← Finset.card_filter]
    rw [hcard, hS.2]
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_powersetCard,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- `r! · C(n,r) · (n-r)! = n!`.
  rw [← Nat.choose_mul_factorial_mul_factorial hr]
  ring

/-- **The factorial moments are all `1`.** For `r ≤ n`, the `r`-th factorial moment
of the fixed-point count `X_n` of a uniform random permutation equals `1`:

  `E[(X_n)_r] = (1/n!) ∑_{σ} (X_n(σ))_r = 1`.

This is the defining property of a Poisson(1) variable (`λ^r` with `λ = 1`). -/
theorem factorial_moment_eq_one (n r : ℕ) (hr : r ≤ n) :
    (∑ σ : Perm (Fin n), ((fixedSet σ).card).descFactorial r : ℝ)
        / (Fintype.card (Perm (Fin n)) : ℝ) = 1 := by
  rw [Fintype.card_perm, Fintype.card_fin]
  have h : (∑ σ : Perm (Fin n), ((fixedSet σ).card).descFactorial r : ℝ)
      = (n.factorial : ℝ) := by
    exact_mod_cast sum_descFactorial_fixedPoints n r hr
  rw [h]
  have hne : (n.factorial : ℝ) ≠ 0 := by
    exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **`r = 1`: the expected number of fixed points is `1`.** A specialization of the
general identity (the mean of the Poisson(1) limit). -/
theorem sum_card_fixedPoints (n : ℕ) (hn : 1 ≤ n) :
    ∑ σ : Perm (Fin n), (fixedSet σ).card = n.factorial := by
  have := sum_descFactorial_fixedPoints n 1 hn
  simpa using this

end DerangementsFactorialMoments
