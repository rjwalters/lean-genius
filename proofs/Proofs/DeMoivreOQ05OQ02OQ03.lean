import Mathlib

/-
# De Moivre OQ-05-OQ-02-OQ-03: Sum of Primitive n-th Roots = μ(n) in any Integral Domain

## Research Problem: de-moivre-oq-05-oq-02-oq-03

> Formalize the companion identity `∑_{ord ζ = n} ζ` over a general field
> containing a primitive n-th root of unity.

The parent file `DeMoivreOQ05OQ02.lean` proves, in `ℂ`,

  ∑_{ζ primitive n-th root of unity} ζ = μ(n).

Here we remove `ℂ` entirely: the identity holds, verbatim, in **any commutative
integral domain `R`** as soon as `R` contains a primitive n-th root of unity.
Concretely, for a fixed primitive n-th root `ζ : R` (existence is a *hypothesis*,
not a construction),

  ∑_{z ∈ primitiveRoots n R} z = (μ n : R).

This subsumes the requested "general field" statement (every field is a domain)
and strictly extends the parent (`ℂ` is one such domain), covering e.g. finite
fields `𝔽_q` with `n ∣ q - 1`, cyclotomic number fields, and `p`-adic fields.

## Why the domain hypothesis is exactly right

If `IsPrimitiveRoot ζ n` holds in a domain of characteristic `p`, then `p ∤ n`
automatically: were `p ∣ n`, writing `n = pᵃ·m` with `p ∤ m`, injectivity of the
Frobenius `x ↦ x^{pᵃ}` would force `ζ^m = 1` with `m < n`, contradicting
primitivity. Hence `n` is invertible-order in `R` and the Möbius value `(μ n : R)`
is the honest cast of an integer — no auxiliary characteristic hypothesis is
needed. The single assumption `IsPrimitiveRoot ζ n` carries all of it.

## Proof (identical skeleton to the parent, ℂ replaced by `R`)

Let `f(k) = ∑_{z ∈ primitiveRoots k R} z` and `g(k) = ∑_{x ∈ nthRootsFinset k 1} x`.

1. **Partition** (holds in *every* domain, no primitive root needed): the `k`-th
   roots present in `R` split by their exact order, so `g(k) = ∑_{d ∣ k} f(d)`.
   This is `IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots` + disjointness.

2. **Local evaluation of `g`**: for each divisor `d ∣ n`, the element `ζ^{n/d}`
   is a primitive `d`-th root (`IsPrimitiveRoot.pow`), which enumerates the `d`-th
   roots as a geometric progression; hence `g(d) = [d = 1]`
   (`IsPrimitiveRoot.geom_sum_eq_zero` for `d > 1`).

3. **Möbius inversion** (`ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq`, valid
   over any ring) turns (1) into `f(n) = ∑_{d ∣ n} μ(n/d)·g(d)`, and by (2) only
   the divisor `d = 1` survives, giving `f(n) = μ(n)·g(1) = μ(n)`.

## Mathlib ingredients
- `IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots` — the partition (any domain).
- `IsPrimitiveRoot.disjoint`, `IsPrimitiveRoot.injOn_pow` — bookkeeping.
- `IsPrimitiveRoot.geom_sum_eq_zero` — geometric-series vanishing (any domain).
- `IsPrimitiveRoot.pow` — `ζ^a` is a primitive `b`-th root when `n = a·b`.
- `ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq` — Möbius inversion over a ring.

All results are 0-axiom, no `sorry`, no `native_decide`.

Parent: `DeMoivreOQ05OQ02.lean` (the `ℂ` case, 0 axioms).
-/

open Finset Polynomial
open scoped ArithmeticFunction.Moebius

namespace DeMoivreOQ05OQ02OQ03

variable {R : Type*} [CommRing R] [IsDomain R]

/-- If `ζ` is a primitive `k`-th root of unity in a domain `R` (with `0 < k`), the
finset of `k`-th roots of unity is the image of `range k` under `i ↦ ζ ^ i`. -/
lemma nthRootsFinset_eq_image [DecidableEq R] {k : ℕ} (hk : 0 < k) {ζ : R}
    (hζ : IsPrimitiveRoot ζ k) :
    nthRootsFinset k (1 : R) = (range k).image (ζ ^ ·) := by
  haveI : NeZero k := ⟨hk.ne'⟩
  ext x
  simp only [mem_nthRootsFinset hk, mem_image, mem_range]
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]

/-- **Local evaluation of `g`.** If `R` contains a primitive `k`-th root of unity
(`0 < k`), then the sum of all `k`-th roots of unity in `R` is `1` when `k = 1`
and `0` otherwise. -/
lemma sum_nthRootsFinset_of_prim [DecidableEq R] {k : ℕ} (hk : 0 < k) {ζ : R}
    (hζ : IsPrimitiveRoot ζ k) :
    ∑ x ∈ nthRootsFinset k (1 : R), x = if k = 1 then 1 else 0 := by
  rw [nthRootsFinset_eq_image hk hζ, sum_image hζ.injOn_pow]
  by_cases hk1 : k = 1
  · subst hk1; simp
  · rw [if_neg hk1]
    exact hζ.geom_sum_eq_zero (by omega)

/-- **Sum of the primitive `n`-th roots of unity equals `μ(n)` in any integral
domain containing one.** Given a primitive `n`-th root of unity `ζ : R`, the sum
over the primitive `n`-th roots of unity in `R` equals `(μ n : R)`. -/
theorem sum_primitiveRoots_eq_moebius {n : ℕ} {ζ : R} (hζ : IsPrimitiveRoot ζ n) :
    ∑ z ∈ primitiveRoots n R, z = (μ n : R) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  -- (1) Partition: `∑_{d ∣ k} f(d) = g(k)` for every `k > 0`, in the ambient domain.
  have hpart : ∀ k > 0,
      ∑ d ∈ k.divisors, (∑ z ∈ primitiveRoots d R, z)
        = ∑ x ∈ nthRootsFinset k (1 : R), x := by
    intro k hk
    haveI : NeZero k := ⟨hk.ne'⟩
    have hdisj : Set.PairwiseDisjoint (↑k.divisors) (fun i => primitiveRoots i R) := by
      intro a _ b _ hab
      exact IsPrimitiveRoot.disjoint hab
    rw [IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots, Finset.sum_biUnion hdisj]
  -- (2) Möbius inversion turns the partition into a formula for `f(n)`.
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun k => ∑ z ∈ primitiveRoots k R, z)
      (g := fun k => ∑ x ∈ nthRootsFinset k (1 : R), x)).mp hpart n hn
  -- (3) Only the divisor `d = 1` survives; every other `g(d)` vanishes since `R`
  --     contains the primitive `d`-th root `ζ^(n/d)`.
  calc ∑ z ∈ primitiveRoots n R, z
      = ∑ x ∈ n.divisorsAntidiagonal,
          (μ x.1 : R) * (∑ y ∈ nthRootsFinset x.2 (1 : R), y) := hinv.symm
    _ = (μ n : R) := by
        rw [Finset.sum_eq_single (n, 1)]
        · dsimp only
          rw [show (∑ x ∈ nthRootsFinset 1 (1 : R), x) = 1 from by
                simpa using sum_nthRootsFinset_of_prim (k := 1) one_pos
                  (ζ := (1 : R)) IsPrimitiveRoot.one, mul_one]
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
          -- `ζ^a` is a primitive `b`-th root of unity, since `n = a * b`.
          have hprim_b : IsPrimitiveRoot (ζ ^ a) b := hζ.pow hn hprod.symm
          rw [sum_nthRootsFinset_of_prim hbpos hprim_b, if_neg hb1, mul_zero]
        · intro hns
          exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_one n, hn.ne'⟩) hns

/-- **Field specialization.** The requested statement over a general field `K`
containing a primitive `n`-th root of unity is the immediate special case. -/
theorem sum_primitiveRoots_eq_moebius_field {K : Type*} [Field K] {n : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) :
    ∑ z ∈ primitiveRoots n K, z = (μ n : K) :=
  sum_primitiveRoots_eq_moebius hζ

/- Axiom audit: both headline theorems should report only the foundational
   trio `propext`, `Classical.choice`, `Quot.sound`. -/
#print axioms sum_primitiveRoots_eq_moebius
#print axioms sum_primitiveRoots_eq_moebius_field

end DeMoivreOQ05OQ02OQ03
