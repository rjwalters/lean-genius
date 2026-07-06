/-
# Prime-degree radical extensions: the affine lower bound ℓ(ℓ-1) ∣ |Gal(Xˡ - p)|
  (open question inverse-galois-d4-oq-02-oq-04)

The parent entry `Proofs.InverseGaloisD4OQ02` establishes the metacyclic divisibility
bracket for `Gal(Xⁿ-p/ℚ)`:

      n ∣ |Gal(Xⁿ-p/ℚ)| ∣ n!,      φ(n) ∣ |Gal|,

and the *coprime* sharpening `n·φ(n) ∣ |Gal|` valid only when `gcd(n, φ(n)) = 1`.  The
parent illustrates the coprime regime with two scattered, hand-checked instances —
`n = 3` (`gcd(3,2)=1`, lower bound `6 = |S₃|`) and `n = 5` (`gcd(5,4)=1`, lower bound
`20 = |F₂₀|`) — each requiring an explicit `by decide` coprimality check.

This file removes the case-by-case coprimality verification for the entire family of
**prime degrees** at once.  The key observation is purely number-theoretic:

> For a prime `ℓ`, `φ(ℓ) = ℓ - 1`, and `ℓ` is automatically coprime to `ℓ - 1`
> because they are *consecutive integers*.

So the coprime hypothesis of `mul_totient_dvd_gal_card_of_coprime` is **free** at every
prime degree, with no per-`ℓ` `decide`.  The metacyclic lower bound therefore reads,
uniformly in the prime `ℓ`,

      ℓ·(ℓ-1)  ∣  |Gal(Xˡ-p/ℚ)|        (`gal_card_affine_lower_bound`)

— the order of the affine group `AGL(1, ℓ) = ℤ/ℓ ⋊ (ℤ/ℓ)ˣ` of order `ℓ(ℓ-1)`, which is
the conjectured *exact* Galois group of a prime-degree radical extension under genericity.
Combined with the parent's `Sₗ`-embedding upper bound this gives the two-sided bracket

      ℓ·(ℓ-1)  ∣  |Gal(Xˡ-p/ℚ)|  ∣  ℓ!        (`gal_card_prime_degree_bracket`)

and, as a numerical consequence, the strict lower bound on the order

      |Gal(Xˡ-p/ℚ)|  ≥  ℓ·(ℓ-1)              (`gal_card_ge_affine`),

quadratic in the degree.  The base entry's `n = 4` is *not* of this form — `4` is not
prime, `gcd(4, φ(4)) = gcd(4, 2) = 2 ≠ 1` — which is exactly why the dihedral case needed
a separate real-embedding argument; the affine bracket here applies precisely to the prime
degrees the parent's coprime examples sampled.

The new prime degree `ℓ = 7` (`42 = 7·6 ∣ |Gal| ∣ 5040 = 7!`) is recorded as a concrete
instance beyond the parent's `ℓ ∈ {3, 5}`.

Status: 0 sorries, 0 axioms, no `native_decide`.  `#print axioms` reports only
`propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.InverseGaloisD4OQ02

namespace InverseGaloisExtensions.PrimeDegree

open Polynomial

-- ============================================================================
-- Part I: Automatic coprimality of a prime with its totient
-- ============================================================================

/-- **`gcd(ℓ, φ(ℓ)) = 1` for every prime `ℓ`.**  Since `φ(ℓ) = ℓ - 1`, the degree `ℓ`
and the totient `ℓ - 1` are consecutive integers, hence coprime — no case analysis.

This is what makes the coprime metacyclic lower bound of the parent file apply *uniformly*
to every prime degree, in contrast to the parent's per-`n` `by decide` coprimality checks. -/
theorem coprime_prime_totient (ℓ : ℕ) (hℓ : ℓ.Prime) : Nat.Coprime ℓ ℓ.totient := by
  rw [Nat.totient_prime hℓ]
  have h2 := hℓ.two_le
  -- A prime `ℓ` is coprime to `m` iff `ℓ ∤ m`; here `0 < ℓ - 1 < ℓ`, so `ℓ ∤ (ℓ - 1)`.
  rw [hℓ.coprime_iff_not_dvd]
  intro hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

-- ============================================================================
-- Part II: The affine lower bound ℓ(ℓ-1) ∣ |Gal(Xˡ - p)|
-- ============================================================================

/-- **`ℓ·(ℓ-1) ∣ |Gal(Xˡ-p/ℚ)|` for every prime degree `ℓ` and prime `p`.**  At a prime
degree the kernel order `ℓ` and the cyclotomic quotient order `φ(ℓ) = ℓ - 1` are coprime
(`coprime_prime_totient`), so the parent's coprime metacyclic bound delivers the *full*
generic order `ℓ·(ℓ-1) = |AGL(1, ℓ)|` as a lower bound with no extra hypothesis.

This is the uniform form of the parent's hand-checked `n = 3` (`6 ∣ |Gal|`) and `n = 5`
(`20 ∣ |Gal|`) examples: both are the special cases `ℓ ∈ {3, 5}` of this single theorem. -/
theorem gal_card_affine_lower_bound (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) :
    ℓ * (ℓ - 1) ∣ Fintype.card (X ^ ℓ - C (p : ℚ) : ℚ[X]).Gal := by
  -- The kernel factor `ℓ ∣ |Gal|` and the cyclotomic quotient factor `φ(ℓ) ∣ |Gal|`,
  -- being coprime at a prime degree, combine into the affine product `ℓ·φ(ℓ) ∣ |Gal|`.
  have h := (coprime_prime_totient ℓ hℓ).mul_dvd_of_dvd_of_dvd
    (InverseGaloisExtensions.n_dvd_gal_card ℓ p hℓ.two_le hp)
    (InverseGaloisExtensions.totient_dvd_gal_card ℓ p hℓ.two_le hp)
  rwa [Nat.totient_prime hℓ] at h

/-- **Two-sided bracket at prime degree:** `ℓ·(ℓ-1) ∣ |Gal(Xˡ-p/ℚ)| ∣ ℓ!`.  The affine
lower bound (`AGL(1, ℓ) ⊆ Gal`) and the symmetric-group upper bound (`Gal ⊆ Sₗ`) sandwich
the order between `ℓ(ℓ-1)` and `ℓ!` for every prime degree `ℓ`.  Equality on the left is
the genericity conjecture; equality of the two bounds (`ℓ(ℓ-1) = ℓ!`) happens only at
`ℓ ∈ {2, 3}`, recovering the parent's exact pins `|Gal(X²-p)| = 2` and `|Gal(X³-p)| = 6`. -/
theorem gal_card_prime_degree_bracket (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) :
    ℓ * (ℓ - 1) ∣ Fintype.card (X ^ ℓ - C (p : ℚ) : ℚ[X]).Gal ∧
      Fintype.card (X ^ ℓ - C (p : ℚ) : ℚ[X]).Gal ∣ ℓ.factorial :=
  ⟨gal_card_affine_lower_bound ℓ p hℓ hp,
    InverseGaloisExtensions.gal_card_dvd_factorial ℓ p hℓ.two_le hp⟩

/-- **`|Gal(Xˡ-p/ℚ)| ≥ ℓ·(ℓ-1)`.**  Turning the affine divisibility into a numerical
lower bound (the Galois group is finite and nonempty): the order of the Galois group of a
prime-degree radical extension grows at least quadratically in the degree. -/
theorem gal_card_ge_affine (ℓ p : ℕ) (hℓ : ℓ.Prime) (hp : p.Prime) :
    ℓ * (ℓ - 1) ≤ Fintype.card (X ^ ℓ - C (p : ℚ) : ℚ[X]).Gal :=
  Nat.le_of_dvd Fintype.card_pos (gal_card_affine_lower_bound ℓ p hℓ hp)

-- ============================================================================
-- Part III: Concrete instances
-- ============================================================================

/-- `6 ∣ |Gal(X³-p/ℚ)|` for every prime `p` (the `ℓ = 3` case, `|S₃|`). -/
example (p : ℕ) (hp : p.Prime) :
    (6 : ℕ) ∣ Fintype.card (X ^ 3 - C (p : ℚ) : ℚ[X]).Gal := by
  have h := gal_card_affine_lower_bound 3 p (by norm_num) hp
  norm_num at h
  exact h

/-- `20 ∣ |Gal(X⁵-p/ℚ)|` for every prime `p` (the `ℓ = 5` case, `|F₂₀|`). -/
example (p : ℕ) (hp : p.Prime) :
    (20 : ℕ) ∣ Fintype.card (X ^ 5 - C (p : ℚ) : ℚ[X]).Gal := by
  have h := gal_card_affine_lower_bound 5 p (by norm_num) hp
  norm_num at h
  exact h

/-- **New prime degree `ℓ = 7`:** `42 = 7·6 ∣ |Gal(X⁷-p/ℚ)| ∣ 5040 = 7!` for every prime
`p` — the affine group `AGL(1, 7)` of order `42` sits inside `Gal`, which embeds in `S₇`. -/
example (p : ℕ) (hp : p.Prime) :
    (42 : ℕ) ∣ Fintype.card (X ^ 7 - C (p : ℚ) : ℚ[X]).Gal := by
  have h := gal_card_affine_lower_bound 7 p (by norm_num) hp
  norm_num at h
  exact h

end InverseGaloisExtensions.PrimeDegree
