import Mathlib
import Proofs.DeMoivreOQ04

/-
# De Moivre OQ-04-OQ-01: Which powers ωᵏ are primitive, and the φ(n) count

## Research Problem: de-moivre-oq-04-oq-01

Parent `de-moivre-oq-04` isolated ω = cos(2π/n) + i·sin(2π/n) as a *primitive*
n-th root of unity whose powers ω⁰, ω¹, …, ωⁿ⁻¹ enumerate **all** n-th roots of
unity.  This file answers the parent's own follow-up:

  *Which of the powers ωᵏ are themselves primitive n-th roots of unity, and how
  many are there?*

## Mathematical Content

A power ζ = ωᵏ of a primitive n-th root ω is again primitive **iff** gcd(k, n) = 1.
Indeed, the (multiplicative) order of ωᵏ is n / gcd(k, n), so ωᵏ has order n —
i.e. is primitive — exactly when gcd(k, n) = 1.  Counting the exponents
0 ≤ k < n with gcd(k, n) = 1 *is* the definition of Euler's totient, so there
are precisely **φ(n)** primitive n-th roots of unity, and they are exactly the
powers ωᵏ with k coprime to n.

This recovers — concretely, in terms of the trigonometric generator
ω = cos(2π/n) + i·sin(2π/n) — the classical fact that
`(primitiveRoots n ℂ).card = φ(n)`.

## Results
- `omega_pow_isPrimitiveRoot_iff` — **headline**: ωᵏ is primitive ⟺ gcd(k,n)=1.
- `primitiveRoots_eq_omega_image` — the primitive n-th roots are *exactly* the
  ωᵏ with 0 ≤ k < n and gcd(k,n)=1.
- `card_coprime_powers_eq_totient` — there are φ(n) such exponents k.
- `card_primitiveRoots_via_omega` — hence `(primitiveRoots n ℂ).card = φ(n)`,
  recovered through the explicit generator ω.

## References
- Mathlib: `IsPrimitiveRoot.pow_iff_coprime`, `IsPrimitiveRoot.eq_pow_of_pow_eq_one`,
  `mem_primitiveRoots`, `Nat.totient_eq_card_coprime`.
- Parent: `Proofs.DeMoivreOQ04` (`omega`, `omega_isPrimitiveRoot`, `omega_pow_injOn`).
-/

open Complex Real DeMoivreOQ04

namespace DeMoivreOQ04OQ01

/-! ## Part I: the primitivity criterion for a single power -/

/-- **Headline.** The power ωᵏ is itself a primitive n-th root of unity **iff**
    `k` is coprime to `n`.  Immediate from `pow_iff_coprime` applied to the
    parent's primitive root ω. -/
theorem omega_pow_isPrimitiveRoot_iff (n k : ℕ) (hn : 0 < n) :
    IsPrimitiveRoot (omega n ^ k) n ↔ Nat.Coprime k n :=
  (omega_isPrimitiveRoot n hn).pow_iff_coprime hn k

/-- For example ω itself (k = 1) is primitive, since `gcd(1, n) = 1`. -/
example (n : ℕ) (hn : 0 < n) : IsPrimitiveRoot (omega n ^ 1) n :=
  (omega_pow_isPrimitiveRoot_iff n 1 hn).mpr (Nat.coprime_one_left n)

/-! ## Part II: the primitive n-th roots are exactly the coprime powers of ω -/

/-- **Structure theorem.** The set of primitive n-th roots of unity is *exactly*
    the image of the coprime exponents `{k ∈ [0, n) : gcd(k, n) = 1}` under
    `k ↦ ωᵏ`.

    `⊇` is the headline criterion.  `⊆`: a primitive root ζ satisfies ζⁿ = 1, so
    by `eq_pow_of_pow_eq_one` it equals ωⁱ for some `i < n`; primitivity of ωⁱ
    then forces gcd(i, n) = 1. -/
theorem primitiveRoots_eq_omega_image (n : ℕ) (hn : 0 < n) :
    primitiveRoots n ℂ =
      ((Finset.range n).filter (fun k => Nat.Coprime k n)).image (fun k => omega n ^ k) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  ext ζ
  simp only [mem_primitiveRoots hn, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hζ
    obtain ⟨i, hi, rfl⟩ := (omega_isPrimitiveRoot n hn).eq_pow_of_pow_eq_one hζ.pow_eq_one
    exact ⟨i, ⟨hi, (omega_pow_isPrimitiveRoot_iff n i hn).mp hζ⟩, rfl⟩
  · rintro ⟨i, ⟨_, hcop⟩, rfl⟩
    exact (omega_pow_isPrimitiveRoot_iff n i hn).mpr hcop

/-! ## Part III: the count is Euler's totient φ(n) -/

/-- The number of exponents `0 ≤ k < n` with `gcd(k, n) = 1` is `φ(n)`.
    This is `Nat.totient` up to the symmetry of coprimality. -/
theorem card_coprime_powers_eq_totient (n : ℕ) :
    ((Finset.range n).filter (fun k => Nat.Coprime k n)).card = Nat.totient n := by
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext k
  simp [Finset.mem_filter, Finset.mem_range, Nat.coprime_comm]

/-- **Euler's totient count, recovered through ω.** There are exactly `φ(n)`
    primitive n-th roots of unity.  We obtain the standard
    `(primitiveRoots n ℂ).card = φ(n)` by counting the coprime powers of the
    explicit generator ω = cos(2π/n) + i·sin(2π/n): the map `k ↦ ωᵏ` is injective
    on `[0, n)` (parent `omega_pow_injOn`), so the image has the same cardinality
    as the index set of coprime exponents. -/
theorem card_primitiveRoots_via_omega (n : ℕ) (hn : 0 < n) :
    (primitiveRoots n ℂ).card = Nat.totient n := by
  rw [primitiveRoots_eq_omega_image n hn,
    Finset.card_image_of_injOn
      ((omega_pow_injOn n hn).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))),
    card_coprime_powers_eq_totient n]

/-! ## Part IV: Summary -/

/-- **De Moivre OQ-04-OQ-01 Summary.** For n > 0, with ω = cos(2π/n) + i·sin(2π/n):
    (1) ωᵏ is a primitive n-th root of unity ⟺ gcd(k, n) = 1;
    (2) the primitive n-th roots of unity are exactly the powers ωᵏ with
        0 ≤ k < n and gcd(k, n) = 1;
    (3) there are exactly φ(n) of them. -/
theorem demoivre_oq04_oq01_summary (n : ℕ) (hn : 0 < n) :
    (∀ k, IsPrimitiveRoot (omega n ^ k) n ↔ Nat.Coprime k n) ∧
    primitiveRoots n ℂ =
      ((Finset.range n).filter (fun k => Nat.Coprime k n)).image (fun k => omega n ^ k) ∧
    (primitiveRoots n ℂ).card = Nat.totient n :=
  ⟨fun k => omega_pow_isPrimitiveRoot_iff n k hn,
   primitiveRoots_eq_omega_image n hn,
   card_primitiveRoots_via_omega n hn⟩

end DeMoivreOQ04OQ01
