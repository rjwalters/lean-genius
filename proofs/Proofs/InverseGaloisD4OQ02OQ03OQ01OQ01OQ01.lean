/-
# Inverse Galois at prime degree: `|Gal(Xˡ-p)| = ℓ·(ℓ-1) = |AGL(1,ℓ)|`
  (inverse-galois-d4-oq-02-oq-03-oq-01-oq-01-oq-01)

The parent chain established, for a prime `p` and `n ≥ 2`, the two-sided squeeze on the order
of `Gal(Xⁿ - p / ℚ)`:

      lcm(n, φ(n)) ∣ |Gal|        (lower, unconditional)
      |Gal| ≤ n·φ(n)              (`gal_card_le_n_mul_totient`, the metacyclic ceiling)
      n·φ(n) ∣ |Gal|  when gcd(n, φ(n)) = 1   (lower, coprime case)

so that **whenever `gcd(n, φ(n)) = 1` the order is pinned exactly at `n·φ(n)`**
(`gal_card_eq_n_mul_totient_of_coprime`).  The parent extracted the single instance
`|Gal(X⁵-p)| = 20`.

This file extracts the *general prime-degree* consequence.  For a prime degree `ℓ` the
coprimality hypothesis is **automatic**: `φ(ℓ) = ℓ - 1`, and `ℓ` is coprime to `ℓ - 1`
(a prime never divides a smaller positive number).  Hence the coprime pin applies at *every*
prime degree, giving a closed form uniform in both `ℓ` and `p`:

  * `gal_card_prime_degree`   : `|Gal(Xˡ-p/ℚ)| = ℓ·(ℓ-1)` for every prime `ℓ` and prime `p`.
        This is the order of the one-dimensional affine group `AGL(1, ℓ) = 𝔽ₗ ⋊ 𝔽ₗˣ` over the
        prime field — the largest solvable transitive subgroup of `Sₗ`, and exactly the Galois
        group of the radical extension `ℚ(ⁿ√p, ζₗ)/ℚ`.  It subsumes the parent instances
        `2` (`ℓ=2`), `6` (`ℓ=3`), `20` (`ℓ=5`) in one statement.

  * `gal_index_in_symm`       : `|Gal| · (ℓ-2)! = ℓ!`, i.e. `Gal(Xˡ-p)` sits inside `Sₗ` with
        index exactly `(ℓ-2)!`.  For `ℓ ≥ 5` this index exceeds `1`, so the Galois group of the
        irreducible `Xˡ - p` is a **proper** subgroup of the full symmetric group — radical
        polynomials are never "generic" at prime degree `≥ 5`, despite being irreducible and
        separable.  (Contrast: a generic degree-`ℓ` polynomial has Galois group `Sₗ`.)

  * `gal_card_septic_eq_42`   : `|Gal(X⁷-p/ℚ)| = 42 = |AGL(1,7)|` for every prime `p` — the next
        instance beyond the parent's quintic `20`, where the factorial bound `|Gal| ∣ 7! = 5040`
        is hopelessly loose (`42 ≪ 5040`).

Status: 0 sorries, 0 axioms, no `native_decide`.  `#print axioms` on the headline theorems
reports only `propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.InverseGaloisD4OQ02OQ03OQ01OQ01

namespace InverseGaloisExtensions

open Polynomial

-- ============================================================================
-- Prime degree forces coprimality for free
-- ============================================================================

/-- For a prime `ℓ`, the degree `ℓ` and its totient `φ(ℓ) = ℓ - 1` are coprime.  A prime
cannot divide a strictly smaller positive number, so `ℓ ∤ (ℓ - 1)`, and `Nat.Prime.coprime_iff_not_dvd`
turns non-divisibility into coprimality.  This is the hypothesis of the parent's coprime pin,
supplied automatically at every prime degree. -/
theorem coprime_self_totient_of_prime {ℓ : ℕ} (hℓ : ℓ.Prime) :
    Nat.Coprime ℓ ℓ.totient := by
  have h2 := hℓ.two_le
  rw [Nat.totient_prime hℓ, hℓ.coprime_iff_not_dvd]
  intro hdvd
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

-- ============================================================================
-- The prime-degree closed form |Gal(Xˡ-p)| = ℓ·(ℓ-1)
-- ============================================================================

/-- **`|Gal(Xˡ-p/ℚ)| = ℓ·(ℓ-1)`** for every prime degree `ℓ` and prime `p` — the order of the
affine group `AGL(1, ℓ)`.  Prime degree makes the coprimality hypothesis of the parent's
exact pin (`gal_card_eq_n_mul_totient_of_coprime`) automatic, so the metacyclic ceiling
`|Gal| ≤ ℓ·φ(ℓ)` is met by the coprime lower bound `ℓ·φ(ℓ) ∣ |Gal|`, and `φ(ℓ) = ℓ - 1`.
Uniform in `p`, with no genericity hypothesis. -/
theorem gal_card_prime_degree (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) :
    Fintype.card (X ^ ℓ - C (p : ℚ) : ℚ[X]).Gal = ℓ * (ℓ - 1) := by
  have h := gal_card_eq_n_mul_totient_of_coprime ℓ p hℓ.two_le hp
    (coprime_self_totient_of_prime hℓ)
  rw [h, Nat.totient_prime hℓ]

-- ============================================================================
-- Index of Gal inside the symmetric group Sₗ
-- ============================================================================

/-- **`|Gal(Xˡ-p)| · (ℓ-2)! = ℓ!`.**  The Galois group of `Xˡ - p` sits inside the symmetric
group `Sₗ` (acting faithfully on the `ℓ` roots) with index exactly `(ℓ-2)!`.  Writing `ℓ = m+2`,
this is the factorisation `ℓ! = ℓ·(ℓ-1)·(ℓ-2)!`.  For `ℓ ≥ 5` the index `(ℓ-2)! > 1`, so the
Galois group is a *proper* subgroup of `Sₗ`: radical polynomials are never `Sₗ`-generic at prime
degree `≥ 5`. -/
theorem gal_index_in_symm (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) :
    Fintype.card (X ^ ℓ - C (p : ℚ) : ℚ[X]).Gal * (ℓ - 2).factorial = ℓ.factorial := by
  rw [gal_card_prime_degree ℓ p hℓ hp]
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 2 := ⟨ℓ - 2, by have := hℓ.two_le; omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2, Nat.factorial_succ, Nat.factorial_succ]
  ring

-- ============================================================================
-- Concrete instance: the septic AGL(1,7)
-- ============================================================================

/-- **`|Gal(X⁷-p/ℚ)| = 42`** for every prime `p` — the affine group `AGL(1, 7)`.  The next
prime-degree instance after the parent's quintic `|Gal(X⁵-p)| = 20`; the factorial bound
`|Gal| ∣ 7! = 5040` is far too loose to see this (`42 ≪ 5040`). -/
theorem gal_card_septic_eq_42 (p : ℕ) (hp : p.Prime) :
    Fintype.card (X ^ 7 - C (p : ℚ) : ℚ[X]).Gal = 42 := by
  rw [gal_card_prime_degree 7 p (by norm_num) hp]

end InverseGaloisExtensions

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `Lean.ofReduceBool` (no `native_decide`) and no `sorryAx`.
#print axioms InverseGaloisExtensions.gal_card_prime_degree
#print axioms InverseGaloisExtensions.gal_index_in_symm
#print axioms InverseGaloisExtensions.gal_card_septic_eq_42
