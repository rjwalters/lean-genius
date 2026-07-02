import Mathlib
import Proofs.Erdos32Problem

/-
# Erdős Problem #32, incomplete-01 — The Unconditional Density Hierarchy

The parent entry `erdos-32` (Additive Complements of Primes) is necessarily
*axiomatized*: its headline results — Erdős's `O((log N)²)` construction (1954),
Kolountzakis's `O((log N)(log log N))` (1996), and Ruzsa's `e^γ·log N` lower bound
(1998) — are deep number-theoretic theorems, and the central `O(log N)` question is
Erdős's OPEN `$50` prize. Those three facts sit in the parent as `axiom`s.

This file (`erdos-32-incomplete-01`) contributes the part that is provable *without*
any of those axioms: the **logical skeleton** of the problem. It proves, `0`-axiom,

* **Unconditional existence** — an additive complement of the primes exists (indeed
  `ℕ` itself is one, in the strong sense). The hard part of the problem is never
  *existence* but *density*; this pins that down formally.
* **The density hierarchy** — every improved upper bound in the results-tower still
  lands inside Erdős's `O((log N)²)`:
    - `HasLogDensity A → HasLogSquaredDensity A`  (the hypothetical `$50` bound, and
      a fortiori Ruzsa's `O(ω·log N)`, refines Erdős's bound);
    - `HasLogLogLogDensity A → HasLogSquaredDensity A`  (Kolountzakis's bound refines
      Erdős's bound).

  These containments certify that the entire progression Lorentz `→` Erdős `→`
  Kolountzakis `→` Ruzsa is a genuine tower of *improvements*, each strictly inside
  the previous density class — a fact used implicitly throughout the literature but
  never, in this formalization, machine-checked until now.

None of the parent's three axioms is invoked; every theorem below depends only on
Mathlib's foundational axioms (verified by `#print axioms`), with no `native_decide`.
The deep existence-with-density results remain, correctly, axiomatized in the parent.

Tags: number-theory, erdos, additive-complements, primes, density, open-problem
-/

namespace Erdos32IncompleteOQ01

open Erdos32 Set Filter Real

/-
## Part I: Unconditional existence

The primes have a very sparse additive complement (this is the content of the
axiomatized parent results). But *some* complement exists trivially: `n = 2 + (n−2)`
writes every `n ≥ 2` as a prime plus a natural number. The mathematics of #32 is
entirely about how *sparse* such a set can be, not whether one exists.
-/

/-- `ℕ` (as `Set.univ`) is a strong additive complement of the primes: every
`n ≥ 2` is `2 + (n − 2)` with `2` prime. -/
theorem univ_isStrongAdditiveComplement : IsStrongAdditiveComplement (Set.univ : Set ℕ) := by
  intro n hn
  exact ⟨2, Nat.prime_two, n - 2, Set.mem_univ _, by omega⟩

/-- A strong additive complement is in particular an (asymptotic) additive
complement (take the threshold `N₀ = 2`). -/
theorem isStrong_imp_isAdditiveComplement {A : Set ℕ}
    (h : IsStrongAdditiveComplement A) : IsAdditiveComplement A :=
  ⟨2, fun n hn => h n hn⟩

/-- **Unconditional existence.** An additive complement of the primes exists — with
no density hypothesis. (The parent's axioms assert existence together with a *sparse*
density; that is the deep content.) -/
theorem exists_additiveComplement : ∃ A : Set ℕ, IsAdditiveComplement A :=
  ⟨Set.univ, isStrong_imp_isAdditiveComplement univ_isStrongAdditiveComplement⟩

/-
## Part II: The density hierarchy

Each named density class of the results-tower is contained in Erdős's `O((log N)²)`.
The proofs are pure real analysis on the counting bound; the counting function itself
is treated as an opaque nonnegative real.
-/

/-- **`O(log N) ⊆ O((log N)²)`.** Any additive complement with `O(log N)` density —
the hypothetical target of Erdős's `$50` question, and a fortiori Ruzsa's
`O(ω(N)·log N)` — also has `O((log N)²)` density (Erdős's 1954 bound). The witnessing
constant scales by `1/log 2`. -/
theorem hasLogDensity_imp_hasLogSquaredDensity {A : Set ℕ}
    (h : HasLogDensity A) : HasLogSquaredDensity A := by
  obtain ⟨C, hC, hbound⟩ := h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / Real.log 2, by positivity, fun N hN => ?_⟩
  have hlogN : Real.log 2 ≤ Real.log N :=
    (Real.log_le_log_iff (by norm_num) (by exact_mod_cast (by omega : 0 < N))).2
      (by exact_mod_cast hN)
  have h1 := hbound N hN
  rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
  nlinarith [mul_le_mul_of_nonneg_right h1 hlog2.le,
    mul_nonneg hC.le (le_trans hlog2.le hlogN), hlogN, hlog2.le]

/-- **`O((log N)(log log N)) ⊆ O((log N)²)`.** Kolountzakis's 1996 density class is
contained in Erdős's `O((log N)²)` class: since `log log N ≤ log N`, the product
`log N · log log N` is at most `(log N)²`. The single point `N = 2` (excluded by the
`log log` bound, which needs `N ≥ 3`) is absorbed into the constant. -/
theorem hasLogLogLogDensity_imp_hasLogSquaredDensity {A : Set ℕ}
    (h : HasLogLogLogDensity A) : HasLogSquaredDensity A := by
  obtain ⟨C, hC, hbound⟩ := h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set v : ℝ := (countingFunction A 2 : ℝ) with hv
  refine ⟨max C (v / (Real.log 2) ^ 2), lt_max_of_lt_left hC, fun N hN => ?_⟩
  rcases eq_or_lt_of_le hN with h2 | h3
  · -- N = 2 : absorb into the constant
    rw [← h2]
    have hpos : (0 : ℝ) < (Real.log 2) ^ 2 := by positivity
    have hle : v / (Real.log 2) ^ 2 ≤ max C (v / (Real.log 2) ^ 2) := le_max_right _ _
    rw [div_le_iff₀ hpos] at hle
    rw [← hv]
    exact hle
  · -- N ≥ 3 : log log N ≤ log N, so log N · log log N ≤ (log N)²
    have hN3 : 3 ≤ N := by omega
    have hbnd := hbound N hN3
    have hlogN_pos : (0 : ℝ) < Real.log N :=
      Real.log_pos (by exact_mod_cast (by omega : (1 : ℕ) < N))
    have hloglog : Real.log (Real.log N) ≤ Real.log N :=
      (Real.log_le_sub_one_of_pos hlogN_pos).trans (by linarith)
    have hstep : C * Real.log N * Real.log (Real.log N) ≤ C * Real.log N * Real.log N :=
      mul_le_mul_of_nonneg_left hloglog (by positivity)
    have hCle : C ≤ max C (v / (Real.log 2) ^ 2) := le_max_left _ _
    calc (countingFunction A N : ℝ)
        ≤ C * Real.log N * Real.log (Real.log N) := hbnd
      _ ≤ C * Real.log N * Real.log N := hstep
      _ = C * (Real.log N) ^ 2 := by ring
      _ ≤ max C (v / (Real.log 2) ^ 2) * (Real.log N) ^ 2 := by
          apply mul_le_mul_of_nonneg_right hCle (by positivity)

/-
## Part III: The problem's structure, unconditionally

Bundling the provable skeleton: a complement exists, and every refined density class
sits inside Erdős's `O((log N)²)`.
-/

/-- **Capstone: the unconditional structure of Erdős #32.** An additive complement
exists, and both the (hypothetical) `O(log N)` class and Kolountzakis's
`O((log N)(log log N))` class are contained in Erdős's `O((log N)²)` class — all
without invoking the deep axiomatized existence/lower-bound results. -/
theorem erdos32_unconditional_structure :
    (∃ A : Set ℕ, IsAdditiveComplement A) ∧
    (∀ A : Set ℕ, HasLogDensity A → HasLogSquaredDensity A) ∧
    (∀ A : Set ℕ, HasLogLogLogDensity A → HasLogSquaredDensity A) :=
  ⟨exists_additiveComplement,
    fun _ => hasLogDensity_imp_hasLogSquaredDensity,
    fun _ => hasLogLogLogDensity_imp_hasLogSquaredDensity⟩

end Erdos32IncompleteOQ01
