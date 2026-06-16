/-
Möbius–floor identity (PROVEN, 0 sorries, 0 axioms). Originally an
`*StatementOnly.lean` Aristotle/batch-submission stub (format from Loom #22468;
docs at research/SORRY-CLASSIFICATION.md); the `sorry` has since been discharged
by an elementary hyperbola-swap proof (see `moebius_mul_floor_sum_eq_one` below).

Follow-up target for research problem `chebyshev-bounds-oq-04-oq-01-oq-01`
(toward an elementary Selberg–Erdős proof of the Prime Number Theorem,
ψ(n)/n → 1). The parent chain lives in:

  - proofs/Proofs/ChebyshevBoundsOQ04.lean      (ψ-bounds; 2 deep PNT axioms)
  - proofs/Proofs/ChebyshevBoundsOQ04OQ01.lean  (Selberg Λ₂ scaffold; frozen,
                                                 18 theorems, 0 sorries, 0 axioms,
                                                 Iter 5a-β-1)

`ChebyshevBoundsOQ04OQ01.lean` is explicitly frozen at Iter 5a-β-1 with the
documented next step "Iter 5a-β-2: weak Mertens M₁ estimate". The keystone of
that step is the classical **Möbius–floor identity**

      Σ_{d=1}^{N} μ(d) · ⌊N/d⌋ = 1        (N ≥ 1)

from which the weak Mertens bound |M₁(N)| = |Σ_{d≤N} μ(d)/d| ≤ 1 follows by
separating ⌊N/d⌋ = N/d − {N/d}. This file queues the integer-valued floor
identity (the harder, reusable half) as a single batch target.

Math (why it is true and elementary):
  Σ_{d≤N} μ(d)⌊N/d⌋
    = Σ_{d≤N} μ(d) · #{m ≥ 1 : d·m ≤ N}          (⌊N/d⌋ counts multiples of d)
    = Σ_{d·m ≤ N} μ(d)                            (Fubini over the region d·m ≤ N)
    = Σ_{n=1}^{N} Σ_{d ∣ n} μ(d)                  (reindex by n = d·m)
    = Σ_{n=1}^{N} [n = 1]                         (Σ_{d∣n} μ(d) = δ_{n,1})
    = 1.

Expected Mathlib glue: `ArithmeticFunction.moebius`, the identity
`ArithmeticFunction.coe_moebius_mul_coe_zeta` (μ ∗ ζ = δ, i.e.
Σ_{d∣n} μ(d) = if n = 1 then 1 else 0 via `ArithmeticFunction.sum_moebius_...`),
and a hyperbola/Fubini reindexing of `Finset.Icc 1 N` against the divisor sum.
The proof requires only tactical search + bookkeeping (no creative insight),
which is the HARD-but-known classification suited to automated search.

Citations:
- Selberg, "An elementary proof of the prime-number theorem", Ann. of Math.
  50 (1949), 305–313.
- Tenenbaum, "Introduction to analytic and probabilistic number theory"
  (3rd ed., 2015), §I.3 (Möbius) and §I.6 (Selberg).
- Apostol, "Introduction to Analytic Number Theory", Theorem 3.10.

Answer: `∑ d ∈ Finset.Icc 1 N, μ d * (↑(N / d) : ℤ) = 1`.
-/

import Mathlib

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option autoImplicit false
set_option linter.all false

open scoped BigOperators
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace ChebyshevBoundsOQ04OQ01OQ01WeakMertens

/--
**Möbius–floor identity.** For every `N ≥ 1`,

    Σ_{d=1}^{N} μ(d) · ⌊N/d⌋ = 1.

Here `N / d` is `Nat` division, i.e. the floor `⌊N/d⌋`, and `μ` is the Möbius
function (`ArithmeticFunction.moebius`, ℤ-valued). This is the keystone for the
weak Mertens bound `|Σ_{d≤N} μ(d)/d| ≤ 1` (Iter 5a-β-2 of the Selberg–Erdős
elementary-PNT roadmap in `ChebyshevBoundsOQ04OQ01.lean`).

Proof idea: `⌊N/d⌋ = #{m ≥ 1 : d·m ≤ N}`, so the sum reindexes (Fubini /
hyperbola method) to `Σ_{n=1}^{N} Σ_{d ∣ n} μ(d) = Σ_{n=1}^{N} [n = 1] = 1`,
using `Σ_{d ∣ n} μ(d) = δ_{n,1}` (`μ ∗ ζ = δ`).
-/
theorem moebius_mul_floor_sum_eq_one (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 1 N, μ d * (↑(N / d) : ℤ) = 1 := by
  -- `Finset.Icc 1 N = Finset.Ioc 0 N` for ℕ, matching the counting lemma below.
  have hIcc : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  -- `⌊N/d⌋` counts the multiples of `d` in `{1,…,N}`.
  have hcard : ∀ d : ℕ,
      (Finset.filter (fun k => d ∣ k) (Finset.Icc 1 N)).card = N / d := by
    intro d
    rw [hIcc, Nat.Ioc_filter_dvd_card_eq_div]
  -- Rewrite each term `μ(d)·⌊N/d⌋` as an inner sum over `k ∈ {1,…,N}` guarded by `d ∣ k`.
  have key : ∀ d : ℕ,
      μ d * (↑(N / d) : ℤ)
        = ∑ k ∈ Finset.Icc 1 N, (if d ∣ k then μ d else 0) := by
    intro d
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, hcard d]
    ring
  calc
    ∑ d ∈ Finset.Icc 1 N, μ d * (↑(N / d) : ℤ)
        = ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 N, (if d ∣ k then μ d else 0) :=
          Finset.sum_congr rfl (fun d _ => key d)
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 N, (if d ∣ k then μ d else 0) :=
          Finset.sum_comm
    _ = ∑ k ∈ Finset.Icc 1 N, ∑ d ∈ k.divisors, μ d := by
          refine Finset.sum_congr rfl (fun k hk => ?_)
          simp only [Finset.mem_Icc] at hk
          rw [← Finset.sum_filter]
          congr 1
          ext d
          simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨_, _⟩, hdvd⟩
            exact ⟨hdvd, by omega⟩
          · rintro ⟨hdvd, _⟩
            have hkpos : 0 < k := by omega
            have hd_le : d ≤ k := Nat.le_of_dvd hkpos hdvd
            have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hkpos
            exact ⟨⟨hd_pos, by omega⟩, hdvd⟩
    _ = ∑ k ∈ Finset.Icc 1 N, (if k = 1 then (1 : ℤ) else 0) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← ArithmeticFunction.coe_mul_zeta_apply,
            ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
    _ = 1 := by
          simp [Finset.sum_ite_eq', Finset.mem_Icc, hN]

end ChebyshevBoundsOQ04OQ01OQ01WeakMertens
