/-
  Chebyshev Bounds OQ-04-OQ-01: Toward an Elementary PNT (Selberg-Erdős)

  ## Open Question

  Prove ψ(n)/n → 1 (the Prime Number Theorem for the second Chebyshev
  function) elementarily, removing the axiom `chebyshevPsi_asymptotic`
  from `ChebyshevBoundsOQ04.lean`.

  ## Status: Iteration 1 / OBSERVE

  This file scaffolds the Selberg-Erdős 1949 elementary proof strategy.
  Concretely, it:

  - Defines the Selberg auxiliary function
        Λ₂(n) = Λ(n)·log n + (Λ ∗ Λ)(n),
    where Λ ∗ Λ denotes Dirichlet convolution.
  - Defines the Selberg partial sum S₂(N) = Σ_{n ≤ N} Λ₂(n).
  - Proves routine non-negativity, base-value, and monotonicity lemmas.
  - Documents the elementary-PNT roadmap and identifies Mathlib gaps.

  No new axioms are added; the parent file's `chebyshevPsi_asymptotic`
  axiom remains the open target.

  ## Roadmap

  1. **Selberg's symmetry formula**: S₂(N) = 2N·log N + O(N).

     This is the central identity of the elementary proof. It is
     provable from the Möbius–log identity
        Σ_{d ∣ n} μ(d)·log²(n/d) = Λ₂(n)   (n ≥ 1)
     combined with
        Σ_{n ≤ N} log²n = N·log²N − 2N·log N + O(log²N).

  2. **Reduction to oscillation control**: define
        R(x) := ψ(x) − x,    V(x) := |R(x)| / x.
     Selberg's symmetry formula yields the Tauberian inequality
        V(x)·log x ≤ (2/x)·Σ_{n ≤ x} V(x/n)·Λ(n) + O(1),
     which expresses oscillations of ψ(x)/x in terms of an averaged
     self-reference.

  3. **Erdős's combinatorial lemma**: if V(x) ≤ V for all x ≥ x₀ and
     V(x) attains a value close to V along a subsequence, then for some
     c > 0 the values V(x) cannot stay arbitrarily close to V on a long
     enough interval — forcing lim sup V(x) = 0.

  4. **Conclusion**: lim ψ(x)/x = 1, i.e. `chebyshevPsi_asymptotic`.

  ## Mathlib gaps observed (Mathlib v4.26.0)

  - No formalization of Selberg's symmetry formula.
  - No analogue of the Möbius–log identity Σ_{d ∣ n} μ(d)·log²(n/d).
  - No partial-summation framework specialized to Λ₂-type sums.

  ## References

  - Selberg, "An elementary proof of the prime-number theorem",
    Annals of Math. 50 (1949), 305–313.
  - Erdős, "On a new method in elementary number theory which leads to
    an elementary proof of the prime number theorem",
    PNAS 35 (1949), 374–384.
  - Tenenbaum, "Introduction to analytic and probabilistic number
    theory" (3rd ed., 2015), §I.6.
  - Iwaniec–Kowalski, "Analytic Number Theory", AMS Colloquium 53
    (2004), §2.3.
-/

import Mathlib
import Proofs.ChebyshevBoundsOQ04

namespace ChebyshevBoundsOQ04OQ01

open Nat Finset ArithmeticFunction
open scoped BigOperators

/-! ## Dirichlet convolution Λ ∗ Λ

We use the explicit divisor-sum form so that subsequent algebraic
manipulations (which the elementary proof requires) avoid the
`divisorsAntidiagonal` abstraction. -/

/-- The Dirichlet convolution `(Λ ∗ Λ)` at `n`, defined explicitly:
    `(Λ ∗ Λ)(n) = Σ_{d ∣ n} Λ(d) · Λ(n/d)`.
    For `n = 0`, the empty divisor set yields `0`. -/
noncomputable def vonMangoldtConv (n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors, vonMangoldt d * vonMangoldt (n / d)

/-! ## Selberg's auxiliary function Λ₂

Λ₂(n) := Λ(n)·log n + (Λ ∗ Λ)(n). The basic identity used by Selberg is

   Σ_{d ∣ n} μ(d)·log²(n/d) = Λ₂(n)   (n ≥ 1),

from which Selberg's symmetry formula

   Σ_{n ≤ N} Λ₂(n) = 2N·log N + O(N)

follows by standard Dirichlet hyperbola summation. -/

/-- Selberg's auxiliary function:
    `Λ₂(n) = Λ(n) · log n + (Λ ∗ Λ)(n)`. -/
noncomputable def selbergLambda2 (n : ℕ) : ℝ :=
  vonMangoldt n * Real.log n + vonMangoldtConv n

/-- The partial Selberg sum: `S₂(N) = Σ_{n ≤ N} Λ₂(n)`. -/
noncomputable def selbergSum2 (N : ℕ) : ℝ :=
  ∑ n ∈ range (N + 1), selbergLambda2 n

/-! ### Base values and non-negativity -/

/-- `(Λ ∗ Λ)(0) = 0` since `divisors 0 = ∅`. -/
theorem vonMangoldtConv_zero : vonMangoldtConv 0 = 0 := by
  unfold vonMangoldtConv
  simp

/-- `(Λ ∗ Λ)(1) = 0` since the only divisor is `1` and `Λ(1) = 0`. -/
theorem vonMangoldtConv_one : vonMangoldtConv 1 = 0 := by
  unfold vonMangoldtConv
  simp [vonMangoldt_apply_one]

/-- `(Λ ∗ Λ)(n) ≥ 0` for all `n`, since `Λ ≥ 0` everywhere. -/
theorem vonMangoldtConv_nonneg (n : ℕ) : 0 ≤ vonMangoldtConv n := by
  unfold vonMangoldtConv
  exact Finset.sum_nonneg (fun _ _ =>
    mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)

/-- `Λ₂(0) = 0`. -/
theorem selbergLambda2_zero : selbergLambda2 0 = 0 := by
  unfold selbergLambda2
  rw [vonMangoldtConv_zero]
  simp [ArithmeticFunction.map_zero]

/-- `Λ₂(1) = 0`: both summands vanish (Λ(1) = 0 and (Λ ∗ Λ)(1) = 0). -/
theorem selbergLambda2_one : selbergLambda2 1 = 0 := by
  unfold selbergLambda2
  rw [vonMangoldtConv_one, vonMangoldt_apply_one]
  ring

/-- `Λ₂(n) ≥ 0` for all `n`. The first summand is non-negative because
    `Λ(n) ≥ 0` and `log n ≥ 0` (with the convention `log 0 = 0`). -/
theorem selbergLambda2_nonneg (n : ℕ) : 0 ≤ selbergLambda2 n := by
  unfold selbergLambda2
  refine add_nonneg ?_ (vonMangoldtConv_nonneg n)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    simp [ArithmeticFunction.map_zero]
  · exact mul_nonneg vonMangoldt_nonneg
      (Real.log_nonneg (by exact_mod_cast h))

/-! ### Partial sum properties -/

/-- `S₂(0) = 0`: the only term is `Λ₂(0) = 0`. -/
theorem selbergSum2_zero : selbergSum2 0 = 0 := by
  unfold selbergSum2
  rw [Finset.sum_range_one, selbergLambda2_zero]

/-- `S₂(N+1) = S₂(N) + Λ₂(N+1)`: the partial-sum recurrence. -/
theorem selbergSum2_succ (N : ℕ) :
    selbergSum2 (N + 1) = selbergSum2 N + selbergLambda2 (N + 1) := by
  unfold selbergSum2
  rw [Finset.sum_range_succ]

/-- The partial Selberg sum is non-negative. -/
theorem selbergSum2_nonneg (N : ℕ) : 0 ≤ selbergSum2 N := by
  unfold selbergSum2
  exact Finset.sum_nonneg (fun n _ => selbergLambda2_nonneg n)

/-- The partial Selberg sum is monotone in the truncation parameter. -/
theorem selbergSum2_mono : Monotone selbergSum2 := by
  intro M N hMN
  unfold selbergSum2
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  · intro k _ _
    exact selbergLambda2_nonneg k

/-! ### Prime values

For prime `p`, `(Λ ∗ Λ)(p) = 0` (the only divisors of `p` are `1` and
`p`, and each summand contains a factor `Λ(1) = 0`). Combined with
`Λ(p) = log p`, this gives the clean closed form `Λ₂(p) = (log p)²`,
the simplest non-trivial value of the auxiliary function. -/

/-- `(Λ ∗ Λ)(p) = 0` for every prime `p`. The sum over `p.divisors =
    {1, p}` is `Λ(1)·Λ(p) + Λ(p)·Λ(1) = 0`. -/
theorem vonMangoldtConv_prime (p : ℕ) (hp : Nat.Prime p) :
    vonMangoldtConv p = 0 := by
  unfold vonMangoldtConv
  rw [Nat.Prime.divisors hp]
  have hne : (1 : ℕ) ≠ p := hp.one_lt.ne
  rw [Finset.sum_pair hne]
  rw [Nat.div_one, Nat.div_self hp.pos, vonMangoldt_apply_one]
  ring

/-- `Λ₂(p) = (log p)²` for every prime `p`. The first summand contributes
    `Λ(p)·log p = (log p)²` (by `vonMangoldt_apply_prime`) and the
    convolution summand vanishes (by `vonMangoldtConv_prime`). -/
theorem selbergLambda2_prime (p : ℕ) (hp : Nat.Prime p) :
    selbergLambda2 p = (Real.log p) ^ 2 := by
  unfold selbergLambda2
  rw [vonMangoldtConv_prime p hp, vonMangoldt_apply_prime hp]
  ring

/-! ### Selberg's dual identity (Iter 3)

The central algebraic identity at the heart of the elementary PNT proof is

    Λ₂(n) = Σ_{d ∣ n} μ(d) · (log (n/d))²    (n ≥ 1).

By Möbius inversion this is equivalent to its **dual form**

    Σ_{d ∣ n} Λ₂(d) = (log n)²    (n ≥ 1),

which is the natural target of direct algebra. The dual unfolds as

    Σ_{d ∣ n} Λ₂(d)
      = Σ_{d ∣ n} Λ(d)·log d + Σ_{d ∣ n} (Λ ∗ Λ)(d)
      = Σ_{d ∣ n} Λ(d)·log d + Σ_{d ∣ n} Λ(d)·log(n/d)
      = Σ_{d ∣ n} Λ(d)·(log d + log(n/d))
      = log n · Σ_{d ∣ n} Λ(d)
      = (log n)²

using the standard Dirichlet identity Λ ∗ ζ = log (Mathlib's
`vonMangoldt_mul_zeta`) twice, `Real.log_mul`, and the fundamental sum
`Σ_{d ∣ n} Λ(d) = log n` (`vonMangoldt_sum`). The "original" identity
follows by `sum_eq_iff_sum_mul_moebius_eq` (deferred to Iter 4). -/

/-- Bridge: the local `vonMangoldtConv` (defined as a sum over `divisors`)
    coincides with the Mathlib Dirichlet convolution `Λ ∗ Λ` of `vonMangoldt`
    with itself (which unfolds over `divisorsAntidiagonal`). -/
theorem vonMangoldtConv_eq_mul (n : ℕ) :
    vonMangoldtConv n = ((vonMangoldt : ArithmeticFunction ℝ) * vonMangoldt) n := by
  unfold vonMangoldtConv
  rw [ArithmeticFunction.mul_apply, ← Nat.map_div_right_divisors, Finset.sum_map]
  rfl

/-- Convolution identity in summed form: `Σ_{d ∣ n} (Λ ∗ Λ)(d) = Σ_{d ∣ n} Λ(d) · log(n/d)`.
    The proof uses `(Λ ∗ Λ) ∗ ζ = Λ ∗ (Λ ∗ ζ) = Λ ∗ log`. -/
theorem sum_divisors_vonMangoldtConv (n : ℕ) :
    ∑ d ∈ n.divisors, vonMangoldtConv d =
      ∑ d ∈ n.divisors, vonMangoldt d * Real.log ((n / d : ℕ) : ℝ) := by
  simp_rw [vonMangoldtConv_eq_mul]
  rw [← ArithmeticFunction.coe_mul_zeta_apply, mul_assoc,
      ArithmeticFunction.vonMangoldt_mul_zeta, ArithmeticFunction.mul_apply,
      ← Nat.map_div_right_divisors, Finset.sum_map]
  simp [ArithmeticFunction.log_apply]

/-- **Selberg's dual identity** (Iter 3, central deliverable): for every `n > 0`,

      Σ_{d ∣ n} Λ₂(d) = (log n)².

    This is the Möbius-dual form of `Λ₂(n) = Σ_{d ∣ n} μ(d) · log²(n/d)`. The
    proof is fully elementary: it combines Λ ∗ ζ = log (twice) with the
    pointwise additivity of `Real.log` on divisor pairs. -/
theorem sum_divisors_selbergLambda2_eq_log_sq {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, selbergLambda2 d = (Real.log n) ^ 2 := by
  unfold selbergLambda2
  rw [Finset.sum_add_distrib, sum_divisors_vonMangoldtConv,
      ← Finset.sum_add_distrib]
  have key : ∀ d ∈ n.divisors,
      vonMangoldt d * Real.log d + vonMangoldt d * Real.log ((n / d : ℕ) : ℝ) =
        vonMangoldt d * Real.log n := by
    intro d hd
    rw [← mul_add]
    rw [Nat.mem_divisors] at hd
    obtain ⟨hdvd, _⟩ := hd
    have hd_pos : (0 : ℕ) < d := Nat.pos_of_dvd_of_pos hdvd hn
    have hnd_pos : (0 : ℕ) < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd_pos
    have hd_ne : ((d : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    have hnd_ne : (((n / d : ℕ)) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hnd_pos.ne'
    rw [← Real.log_mul hd_ne hnd_ne, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  rw [Finset.sum_congr rfl key, ← Finset.sum_mul,
      ArithmeticFunction.vonMangoldt_sum]
  ring

/-- **Möbius–log identity (literal form, Iter 4)**: for `n > 0`,

      Λ₂(n) = Σ_{d ∣ n} μ(d) · log²(n/d).

    This is the Möbius-inverse of Iter 3's dual identity
    `sum_divisors_selbergLambda2_eq_log_sq`. The proof applies
    `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` to the dual
    identity, then re-indexes `divisorsAntidiagonal → divisors` via
    `Nat.sum_divisorsAntidiagonal`. -/
theorem selbergLambda2_eq_moebius_log_sq {n : ℕ} (hn : 0 < n) :
    selbergLambda2 n =
      ∑ d ∈ n.divisors,
        ((ArithmeticFunction.moebius d : ℝ) * (Real.log (n / d : ℕ)) ^ 2) := by
  have hiter3 : ∀ m : ℕ, 0 < m → ∑ i ∈ m.divisors, selbergLambda2 i = (Real.log m) ^ 2 :=
    fun m hm => sum_divisors_selbergLambda2_eq_log_sq hm
  have hinv :=
    (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)).mp hiter3 n hn
  have hbridge :
      ∑ x ∈ n.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius x.fst : ℝ) * (Real.log x.snd) ^ 2)
        = ∑ d ∈ n.divisors,
          ((ArithmeticFunction.moebius d : ℝ) * (Real.log (n / d : ℕ)) ^ 2) :=
    Nat.sum_divisorsAntidiagonal
      (fun a b => (ArithmeticFunction.moebius a : ℝ) * (Real.log b) ^ 2)
  exact hinv.symm.trans hbridge

/-! ## Mertens partial sum M(N) and its trivial linear bound (Iter 5a-β-1)

Toward the weak Mertens M1 estimate

    |Σ_{d ∈ Icc 1 N} (μ(d) : ℝ) / d| ≤ 1 + Real.log N    (Iter 5a-β target),

the foundational ingredient is the trivial triangle bound

    |M(N)| ≤ N,    M(N) := Σ_{d ∈ Icc 1 N} (μ(d) : ℝ).

This follows from `|μ(d)| ≤ 1` (Mathlib `ArithmeticFunction.abs_moebius_le_one`,
in ℤ) and the triangle inequality `|Σ| ≤ Σ |·|`. The linear bound is
far from optimal — the Riemann hypothesis is equivalent to
`|M(N)| = O(N^{1/2+ε})` — but the trivial form is exactly what
summation-by-parts will need in 5a-β. -/

/-- The Mertens partial sum `M(N) := Σ_{1 ≤ d ≤ N} μ(d)`, cast to `ℝ`. -/
noncomputable def mertensM (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ)

/-- `M(0) = 0` since `Icc 1 0 = ∅`. -/
theorem mertensM_zero : mertensM 0 = 0 := by
  unfold mertensM
  rw [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1)]
  simp

/-- **Trivial linear bound** for the Mertens partial sum: `|M(N)| ≤ N`.
    Proof: triangle inequality `|Σ| ≤ Σ |·|`, then
    `|(μ d : ℝ)| = ((|μ d| : ℤ) : ℝ) ≤ 1` via
    `ArithmeticFunction.abs_moebius_le_one`, then count
    `(Finset.Icc 1 N).card = N`. -/
theorem mertensM_abs_le (N : ℕ) : |mertensM N| ≤ (N : ℝ) := by
  unfold mertensM
  calc |∑ d ∈ Finset.Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ)|
      ≤ ∑ d ∈ Finset.Icc 1 N, |((ArithmeticFunction.moebius d : ℤ) : ℝ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d _
        rw [← Int.cast_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = ((Finset.Icc 1 N).card : ℝ) := by simp
    _ = (N : ℝ) := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]

/-! ## Future Work

The remaining next-iteration deliverables are, in order of increasing
difficulty:

1. **`selbergSum2_eq_two_n_log_n_plus_O`** (Iter 5–6): Selberg's symmetry formula
        S₂(N) = 2 N · log N + O(N).
   The error-term step requires summation by parts and quantitative
   control of Σ_{d ≤ x} μ(d) — but only its `O(x)` form, which is well
   within elementary bounds. Iter 5a-β-1 (this iteration) lands the
   foundational `|M(N)| ≤ N` bound; Iter 5a-β assembles it with Abel
   summation against `1/d` to deliver the weak Mertens M1 estimate.

2. **Tauberian step → PNT** (Iter 7+): Erdős–Selberg's combinatorial
   finishing argument, the longest part of the elementary proof.

Iterations 3–4 (now closed) deliver the central algebraic identities of
the Selberg–Erdős elementary PNT proof: Iter 3's dual form
Σ_{d ∣ n} Λ₂(d) = (log n)² and Iter 4's Möbius-inverse literal form
Λ₂(n) = Σ_{d ∣ n} μ(d) · log²(n/d), together with the bridge lemma
`vonMangoldtConv_eq_mul` that connects this file's explicit divisor-sum
definition to Mathlib's `ArithmeticFunction` convolution. Iter 5a-β-1
(this iteration) adds the Mertens partial sum `mertensM` and its
trivial linear bound `mertensM_abs_le`. -/

end ChebyshevBoundsOQ04OQ01
