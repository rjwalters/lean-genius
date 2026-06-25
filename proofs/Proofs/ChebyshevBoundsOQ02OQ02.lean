/-
# Chebyshev Bounds OQ-02 (leaf oq-02): ψ and θ share the same main term

## Open question (from `chebyshev-bounds-oq-02`)

The parent `ChebyshevBoundsOQ02` introduced the second Chebyshev function
`ψ(n) = ∑_{m≤n} Λ(m) = ∑_{p^k≤n} log p` in von Mangoldt form (and Legendre's identity), as a
self-contained ℕ-indexed development that does **not** reference Mathlib's Chebyshev API. A
natural next step is to compare it with the **first** Chebyshev function `θ(n) = ∑_{p≤n} log p`
and show the two share the **same main term**: their difference is supported entirely on the
*proper* prime powers `p^k` with `k ≥ 2`, and is `O(√n · log n)`.

## What this file proves (0 sorries, 0 axioms)

**Gallery-facing statements over the parent's `chebyshevPsi`:**

* `chebyshevTheta n = ∑_{p ≤ n, p prime} log p` — the first Chebyshev function.
* `psi_sub_theta` : `ψ(n) − θ(n) = ∑_{m≤n, ¬ m prime} Λ(m)` — the difference is supported on the
  higher prime powers `m = p^k`, `k ≥ 2` (proved directly, the structural "same main term").
* `psi_sub_theta_nonneg`, `theta_le_psi`.
* `psi_sub_theta_eq_proper_prime_powers` : the difference as a sum over the prime powers in
  `[1,n]` that are not prime (the `k ≥ 2` support made explicit via `IsPrimePow`).

**The bridge to Mathlib + the quantitative content.** Mathlib's `Mathlib.NumberTheory.Chebyshev`
already proves the deep facts — the decomposition, the identity `ψ(x) = ∑_{k≥1} θ(x^{1/k})`, and
the sharp bound `|ψ(x) − θ(x)| ≤ 2√x·log x`. This file's genuine contribution is to **connect**
the parent's self-contained ℕ-indexed `chebyshevPsi` to Mathlib's `Chebyshev.psi` (and likewise
for θ), and then to **transport** those two results to the gallery's functions:

* `chebyshevPsi_eq_mathlib` : `chebyshevPsi n = Chebyshev.psi n`.
* `chebyshevTheta_eq_mathlib` : `chebyshevTheta n = Chebyshev.theta n`.
* **`psi_sub_theta_eq_sum_theta`** : `ψ(n) − θ(n) = ∑_{k=2}^{⌊log₂ n⌋} θ(n^{1/k})` — the exact
  "`Σ_{k≥2} θ(n^{1/k})`" same-main-term identity, for `n ≥ 2`.
* **`abs_psi_sub_theta_le`** : `|ψ(n) − θ(n)| ≤ 2·√n·log n` for `n ≥ 1` — the quantitative
  same-main-term bound (`O(√n·log n)`, sharper than the `O(√n log²n)` originally targeted).

The substantive analytic number theory in the last two results is **Mathlib's**
(`Chebyshev.psi_eq_theta_add_sum_theta`, `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`); the
work here is the formal bridge that makes the gallery's elementary `chebyshevPsi` inherit them.

*Reference:* Chebyshev's elementary method; `Mathlib.NumberTheory.Chebyshev`,
`Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt`.
-/

import Proofs.ChebyshevBoundsOQ02
import Mathlib

open Finset ArithmeticFunction

namespace ChebyshevBoundsOQ02OQ02

open ChebyshevBoundsOQ02

/-! ## I. The first Chebyshev function θ -/

/-- The **first Chebyshev function** `θ(n) = ∑_{p ≤ n, p prime} log p`. -/
noncomputable def chebyshevTheta (n : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 n).filter Nat.Prime, Real.log (p : ℝ)

/-- `[1,n] = (0,n]` as finsets of naturals — used to line up the parent's `Icc 1 n` indexing
    with Mathlib's `Ioc 0 ⌊x⌋₊` indexing. -/
private theorem Icc_one_eq_Ioc_zero (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n :=
  Finset.ext fun m => by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

/-- θ in von Mangoldt form: `θ(n) = ∑_{m≤n} [m prime] · Λ(m)`. The prime part of `ψ` is `θ`,
    because `Λ(p) = log p` for a prime `p`. -/
theorem chebyshevTheta_eq_sum_vonMangoldt (n : ℕ) :
    chebyshevTheta n = ∑ m ∈ Finset.Icc 1 n, (if m.Prime then Λ m else 0) := by
  rw [chebyshevTheta, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m.Prime
  · rw [if_pos hm, if_pos hm, vonMangoldt_apply_prime hm]
  · rw [if_neg hm, if_neg hm]

/-! ## II. The difference ψ − θ: same main term (direct, gallery-facing) -/

/-- **The structural heart.** `ψ(n) − θ(n) = ∑_{m≤n, ¬ m prime} Λ(m)`: the two Chebyshev
    functions share the same main term and differ only by the contribution of the higher
    prime powers (`m = p^k`, `k ≥ 2`). -/
theorem psi_sub_theta (n : ℕ) :
    chebyshevPsi n - chebyshevTheta n =
      ∑ m ∈ Finset.Icc 1 n, (if m.Prime then 0 else Λ m) := by
  rw [chebyshevPsi, chebyshevTheta_eq_sum_vonMangoldt, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m.Prime <;> simp [hm]

/-- Every term of `ψ − θ` is nonnegative. -/
theorem psi_sub_theta_nonneg (n : ℕ) : 0 ≤ chebyshevPsi n - chebyshevTheta n := by
  rw [psi_sub_theta]
  refine Finset.sum_nonneg fun m _ => ?_
  by_cases hm : m.Prime <;> simp [hm, vonMangoldt_nonneg]

/-- `θ(n) ≤ ψ(n)`. -/
theorem theta_le_psi (n : ℕ) : chebyshevTheta n ≤ chebyshevPsi n := by
  have := psi_sub_theta_nonneg n; linarith

/-- The difference, written explicitly over the *proper* prime powers in `[1,n]` (prime powers
    that are not themselves prime, i.e. `m = p^k` with `k ≥ 2`). A summand is nonzero iff
    `IsPrimePow m ∧ ¬ m.Prime`. -/
theorem psi_sub_theta_eq_proper_prime_powers (n : ℕ) :
    chebyshevPsi n - chebyshevTheta n =
      ∑ m ∈ (Finset.Icc 1 n).filter (fun m => IsPrimePow m ∧ ¬ m.Prime), Λ m := by
  rw [psi_sub_theta, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  by_cases hm : m.Prime
  · rw [if_pos hm]; simp [hm]
  · rw [if_neg hm]
    by_cases hpp : IsPrimePow m
    · rw [if_pos ⟨hpp, hm⟩]
    · rw [if_neg (fun h => hpp h.1)]
      exact vonMangoldt_eq_zero_iff.mpr hpp

/-! ## III. Bridge to Mathlib's `Chebyshev` and transported quantitative results -/

/-- **Bridge.** The parent's elementary ℕ-indexed second Chebyshev function agrees with
    Mathlib's `Chebyshev.psi`. -/
theorem chebyshevPsi_eq_mathlib (n : ℕ) : chebyshevPsi n = Chebyshev.psi (n : ℝ) := by
  rw [Chebyshev.psi, Nat.floor_natCast, chebyshevPsi]
  exact Finset.sum_congr (Icc_one_eq_Ioc_zero n) (fun _ _ => rfl)

/-- **Bridge.** `chebyshevTheta` agrees with Mathlib's `Chebyshev.theta`. -/
theorem chebyshevTheta_eq_mathlib (n : ℕ) : chebyshevTheta n = Chebyshev.theta (n : ℝ) := by
  rw [Chebyshev.theta, Nat.floor_natCast, chebyshevTheta]
  exact Finset.sum_congr (by rw [Icc_one_eq_Ioc_zero]) (fun _ _ => rfl)

/-- **Same-main-term identity** (the `Σ_{k≥2} θ(n^{1/k})` form). For `n ≥ 2`,
    `ψ(n) − θ(n) = ∑_{k=2}^{⌊log₂ n⌋} θ(n^{1/k})`.

    Transported from Mathlib's `Chebyshev.psi_eq_theta_add_sum_theta` via the bridge. -/
theorem psi_sub_theta_eq_sum_theta (n : ℕ) (hn : 2 ≤ n) :
    chebyshevPsi n - chebyshevTheta n =
      ∑ k ∈ Finset.Icc 2 ⌊Real.log n / Real.log 2⌋₊,
        Chebyshev.theta ((n : ℝ) ^ ((1 : ℝ) / k)) := by
  rw [chebyshevPsi_eq_mathlib, chebyshevTheta_eq_mathlib,
      Chebyshev.psi_eq_theta_add_sum_theta (by exact_mod_cast hn), add_sub_cancel_left]

/-- **Quantitative same-main-term bound.** For `n ≥ 1`,
    `|ψ(n) − θ(n)| ≤ 2·√n·log n` — so `ψ` and `θ` agree up to `O(√n·log n)`.

    Transported from Mathlib's `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` via the bridge. -/
theorem abs_psi_sub_theta_le (n : ℕ) (hn : 1 ≤ n) :
    |chebyshevPsi n - chebyshevTheta n| ≤ 2 * Real.sqrt n * Real.log n := by
  rw [chebyshevPsi_eq_mathlib, chebyshevTheta_eq_mathlib]
  exact Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by exact_mod_cast hn)

end ChebyshevBoundsOQ02OQ02
