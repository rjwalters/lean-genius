import Mathlib

/-
# De Moivre OQ-05-OQ-02: The Sum of the Primitive n-th Roots of Unity is μ(n)

## Research Problem: de-moivre-oq-05-oq-02

Let `μ` denote the Möbius function.  This file proves the classical identity

  ∑_{ζ a primitive n-th root of unity} ζ = μ(n)            (in ℂ, for every n).

This generalises the parent result `de-moivre-oq-05`, which records that the sum
of *all* n-th roots of unity vanishes for n > 1 (it equals `1` only for n = 1).

## Mathematical Content

Write
  g(n) = ∑_{ζ^n = 1} ζ            (sum of all n-th roots of unity)
  f(n) = ∑_{ζ primitive of order n} ζ   (sum of primitive n-th roots).

Two facts drive the proof:

1.  **Partition.**  Every n-th root of unity is a *primitive* d-th root for a
    unique divisor `d ∣ n`.  Summing over the partition,
        g(n) = ∑_{d ∣ n} f(d).

2.  **Evaluation of g.**  Picking a primitive n-th root `ζ`, the n-th roots are
    exactly `ζ^0, …, ζ^{n-1}`, so `g(n) = ∑_{i<n} ζ^i` is a finite geometric
    series.  For n > 1 this telescopes to `0`; for n = 1 it is `1`.  Hence
        g(n) = [n = 1].

Applying Möbius inversion to (1) gives
        f(n) = ∑_{d ∣ n} μ(n/d) · g(d) = μ(n) · g(1) = μ(n),
since the only surviving term is the one with `d = 1`.

## Mathlib ingredients
- `IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots` — the partition (1).
- `IsPrimitiveRoot.disjoint` — distinct orders give disjoint primitive-root sets.
- `IsPrimitiveRoot.geom_sum_eq_zero` — the geometric-series vanishing.
- `Complex.isPrimitiveRoot_exp` — existence of a primitive root in ℂ.
- `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` — Möbius inversion over a ring.

## References
- Standard fact; see e.g. Apostol, *Introduction to Analytic Number Theory*,
  Theorem 2.7 (the Möbius function as a sum of primitive roots of unity).
-/

open Finset Polynomial
open scoped ArithmeticFunction.Moebius

namespace DeMoivreOQ05OQ02

/-- If `ζ` is a primitive `n`-th root of unity in `ℂ` (with `0 < n`), then the
finset of `n`-th roots of unity is the image of `range n` under `i ↦ ζ ^ i`. -/
lemma nthRootsFinset_eq_image {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    nthRootsFinset n (1 : ℂ) = (range n).image (ζ ^ ·) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  ext x
  simp only [mem_nthRootsFinset hn, mem_image, mem_range]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

/-- The sum of all `n`-th roots of unity in `ℂ` is `1` when `n = 1` and `0`
otherwise (the parent result, restated as an evaluation of `g`). -/
lemma sum_nthRootsFinset {n : ℕ} (hn : 0 < n) :
    ∑ x ∈ nthRootsFinset n (1 : ℂ), x = if n = 1 then 1 else 0 := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ n :=
    ⟨_, Complex.isPrimitiveRoot_exp n hn.ne'⟩
  rw [nthRootsFinset_eq_image hn hζ, sum_image hζ.injOn_pow]
  by_cases hn1 : n = 1
  · subst hn1; simp
  · rw [if_neg hn1]
    exact hζ.geom_sum_eq_zero (by omega)

/-- **Sum of the primitive `n`-th roots of unity equals `μ(n)`.**
For every natural number `n`, the sum over the primitive `n`-th roots of unity
in `ℂ` equals the value of the Möbius function at `n` (cast into `ℂ`). -/
theorem sum_primitiveRoots_eq_moebius (n : ℕ) :
    ∑ ζ ∈ primitiveRoots n ℂ, ζ = (μ n : ℂ) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  -- (1) Partition: ∑_{d ∣ k} f(d) = g(k) for every k > 0.
  have hpart : ∀ k > 0,
      ∑ d ∈ k.divisors, (∑ ζ ∈ primitiveRoots d ℂ, ζ)
        = ∑ x ∈ nthRootsFinset k (1 : ℂ), x := by
    intro k hk
    haveI : NeZero k := ⟨hk.ne'⟩
    have hdisj : Set.PairwiseDisjoint (↑k.divisors) (fun i => primitiveRoots i ℂ) := by
      intro a _ b _ hab
      exact IsPrimitiveRoot.disjoint hab
    rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, Finset.sum_biUnion hdisj]
  -- (2) Möbius inversion turns the partition into a formula for f(n).
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun k => ∑ ζ ∈ primitiveRoots k ℂ, ζ)
      (g := fun k => ∑ x ∈ nthRootsFinset k (1 : ℂ), x)).mp hpart n hn
  -- (3) Möbius inversion, then only the divisor `d = 1` survives (`μ(n) · 1`).
  calc ∑ ζ ∈ primitiveRoots n ℂ, ζ
      = ∑ x ∈ n.divisorsAntidiagonal,
          (μ x.1 : ℂ) * (∑ y ∈ nthRootsFinset x.2 (1 : ℂ), y) := hinv.symm
    _ = (μ n : ℂ) := by
        rw [Finset.sum_eq_single (n, 1)]
        · dsimp only
          rw [show (∑ x ∈ nthRootsFinset 1 (1 : ℂ), x) = 1 from by
                simpa using sum_nthRootsFinset (n := 1) one_pos, mul_one]
        · rintro ⟨a, b⟩ hab hne
          dsimp only
          simp only [Nat.mem_divisorsAntidiagonal] at hab
          obtain ⟨hprod, hn0⟩ := hab
          have hbpos : 0 < b := by
            rcases Nat.eq_zero_or_pos b with rfl | h
            · simp only [Nat.mul_zero] at hprod; exact absurd hprod.symm hn0
            · exact h
          have hb1 : b ≠ 1 := by
            rintro rfl
            exact hne (by simp only [Nat.mul_one] at hprod; rw [hprod])
          rw [sum_nthRootsFinset hbpos, if_neg hb1, mul_zero]
        · intro hns
          exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_one n, hn.ne'⟩) hns

end DeMoivreOQ05OQ02
