/-
# Inverse Galois: the coprime sharpness of the metacyclic bracket (inverse-galois-d4-oq-02-oq-03)

The parent entry `Proofs.InverseGaloisD4OQ02` establishes, for a prime `p` and `n ≥ 2`,
the two independent lower divisibilities of the order of `Gal(Xⁿ - p / ℚ)`

      n ∣ |Gal|        (`n_dvd_gal_card`,      the radical/kernel factor `Cₙ`)
      φ(n) ∣ |Gal|     (`totient_dvd_gal_card`, the cyclotomic/quotient factor `(ℤ/n)ˣ`)

together with the upper bound `|Gal| ∣ n!` (`gal_card_dvd_factorial`).  The metacyclic
order conjectured under genericity is `n·φ(n)`, the order of the holomorph
`ℤ/n ⋊ (ℤ/n)ˣ`.

This file resolves the third open question of the parent: it *combines* the two lower
factors into a single lower bound and characterizes when that bound already reaches the
full metacyclic order without any genericity hypothesis.

  * `lcm_dvd_gal_card`            : `lcm(n, φ(n)) ∣ |Gal|`, the sharp combination of the
                                     two independent factors (`lcm`, not the product,
                                     because `n` and `φ(n)` may share factors — e.g.
                                     `n = 4`, `φ(4) = 2`, `lcm = 4`).
  * `mul_totient_dvd_gal_card_of_coprime`
                                   : when `gcd(n, φ(n)) = 1` the lcm *is* the product,
                                     so the full metacyclic order `n·φ(n) ∣ |Gal|`
                                     drops out for free — a lower bound with no
                                     linear-disjointness assumption.

The cubic case `n = 3` is the sharp witness.  There `gcd(3, φ(3)) = gcd(3, 2) = 1`, so
`3·φ(3) = 6 ∣ |Gal(X³-p)|`; combined with `|Gal| ∣ 3! = 6` this *pins the order exactly*:

      |Gal(X³ - p / ℚ)| = 6  =  |S₃|   for EVERY prime p   (`gal_card_cubic_eq_six`).

This is the cubic analogue of the base entry's `|Gal(X⁴-2/ℚ)| = 8`, but it is uniform in
the prime `p` and falls straight out of the divisibility bracket plus coprimality — no
separate ℝ-embedding or resolvent argument is needed.  (For `n = 4` the two factors
overlap, `lcm(4, 2) = 4 ≠ 8`, so coprimality fails and the bracket alone does not pin the
order — exactly why the base entry needed an extra argument for `|Gal| = 8`.)

Status: 0 sorries, 0 axioms, no `native_decide`.  `#print axioms` on the headline
theorems reports only `propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.InverseGaloisD4OQ02

namespace InverseGaloisExtensions

open Polynomial

-- ============================================================================
-- Parts I & II: The combined lower bound `lcm(n, φ(n)) ∣ |Gal|` and its coprime
-- sharpening `gcd(n, φ(n)) = 1 ⟹ n·φ(n) ∣ |Gal|` were originally proved here;
-- identical statements were later merged into the parent `InverseGaloisD4OQ02.lean`
-- (PR #31408: `lcm_dvd_gal_card`, `mul_totient_dvd_gal_card_of_coprime`), which
-- this file imports — the duplicates were removed to keep the namespace coherent.
-- ============================================================================
-- Part III: The sharp cubic witness  |Gal(X³-p/ℚ)| = 6  for every prime p
-- ============================================================================

/-- **`6 ∣ |Gal(X³-p/ℚ)|`.** For `n = 3` the factors are coprime,
`gcd(3, φ(3)) = gcd(3, 2) = 1`, so the full metacyclic order `3·φ(3) = 6` divides the
order of the cubic Galois group for every prime `p`. -/
theorem six_dvd_gal_card_cubic (p : ℕ) (hp : p.Prime) :
    6 ∣ Fintype.card (X ^ 3 - C (p : ℚ) : ℚ[X]).Gal := by
  have h := mul_totient_dvd_gal_card_of_coprime 3 p (by norm_num) hp (by decide)
  have h6 : (3 : ℕ) * Nat.totient 3 = 6 := by decide
  rwa [h6] at h

/-- **`|Gal(X³-p/ℚ)| = 6`** for every prime `p`.  The coprime lower bound `6 ∣ |Gal|`
and the symmetric-group upper bound `|Gal| ∣ 3! = 6` squeeze the order to exactly `6`,
identifying the cubic Galois group with `S₃` uniformly in `p`.  This is the cubic
analogue of the base entry's `|Gal(X⁴-2/ℚ)| = 8`, here uniform in the prime and derived
purely from the divisibility bracket. -/
theorem gal_card_cubic_eq_six (p : ℕ) (hp : p.Prime) :
    Fintype.card (X ^ 3 - C (p : ℚ) : ℚ[X]).Gal = 6 := by
  have hlow := six_dvd_gal_card_cubic p hp
  have hhigh := gal_card_dvd_factorial 3 p (by norm_num) hp
  have h6 : Nat.factorial 3 = 6 := by decide
  rw [h6] at hhigh
  exact Nat.dvd_antisymm hhigh hlow

end InverseGaloisExtensions
