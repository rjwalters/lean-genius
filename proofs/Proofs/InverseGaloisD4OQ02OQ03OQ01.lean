/-
# Inverse Galois: the sharp degree boundary of the metacyclic bracket
  (inverse-galois-d4-oq-02-oq-03-oq-01)

The parent entry `Proofs.InverseGaloisD4OQ02OQ03` pins the cubic Galois group exactly,

      |Gal(X³ - p / ℚ)| = 6   for every prime p     (`gal_card_cubic_eq_six`),

by squeezing the coprime lower bound `n·φ(n) ∣ |Gal|` (valid when `gcd(n, φ(n)) = 1`,
`mul_totient_dvd_gal_card_of_coprime`) against the symmetric-group upper bound
`|Gal| ∣ n!` (`gal_card_dvd_factorial`).  The squeeze closes precisely because at `n = 3`
the metacyclic order *equals* the factorial bound: `3·φ(3) = 6 = 3!`.

This raises the open question the parent left implicit: **for which degrees `n` does the
elementary bracket pin `|Gal(Xⁿ - p)|` exactly?**  The squeeze succeeds iff the lower and
upper bounds coincide, i.e. iff

      n · φ(n) = n!.

This file resolves that boundary completely.

  * `totient_mul_eq_factorial_iff`  : for `n ≥ 2`,  `n·φ(n) = n!  ↔  n = 2 ∨ n = 3`.
                                       For `n ≥ 4` the metacyclic order `n·φ(n) ≤ n(n-1)`
                                       is dwarfed by `n! ≥ 2·n(n-1)`, so the bracket has
                                       slack and cannot pin the order on its own.
  * `gal_card_eq_factorial_of_pin`  : whenever `n·φ(n) = n!` the order is pinned to `n!`
                                       — and since the only solutions `n ∈ {2, 3}` are
                                       automatically coprime, *no separate coprimality
                                       hypothesis is needed*.
  * `gal_card_quadratic_eq_two`     : the quadratic companion of the cubic witness,
                                       `|Gal(X² - p / ℚ)| = 2` for every prime `p`.

So the elementary divisibility bracket pins the Galois group of `Xⁿ - p` *exactly* at the
two degrees `n = 2` (giving `2 = |C₂|`) and `n = 3` (giving `6 = |S₃|`), and at no other
degree.  For `n ≥ 4` (the smallest being the base entry's own `n = 4`, where
`4·φ(4) = 8 ≠ 24 = 4!`) the bracket leaves a genuine gap, which is exactly why the base
entry `|Gal(X⁴-2)| = 8` required an extra resolvent/embedding argument beyond the bracket.

Status: 0 sorries, 0 axioms, no `native_decide`.  `#print axioms` on the headline
theorems reports only `propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.InverseGaloisD4OQ02OQ03

namespace InverseGaloisExtensions

open Polynomial

-- ============================================================================
-- Part I: The sharp degree boundary  n·φ(n) = n!  ⟺  n ∈ {2, 3}
-- ============================================================================

/-- **The metacyclic order meets the factorial bound only at `n = 2, 3`.**
The bracket squeeze `n·φ(n) ∣ |Gal| ∣ n!` pins the order exactly when its two ends
coincide, i.e. when `n·φ(n) = n!`.  For `n ≥ 2` this happens precisely for `n = 2` and
`n = 3`: for `n ≥ 4` we have `φ(n) ≤ n-1`, so `n·φ(n) ≤ n(n-1)`, while
`n! = n(n-1)·(n-2)! ≥ 2·n(n-1)` strictly exceeds it. -/
theorem totient_mul_eq_factorial_iff {n : ℕ} (hn : 2 ≤ n) :
    n * n.totient = n.factorial ↔ n = 2 ∨ n = 3 := by
  refine ⟨fun h => ?_, by rintro (rfl | rfl) <;> decide⟩
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne2, hne3⟩ := hcon
  -- so n ≥ 4; write n = m + 2 with m ≥ 2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm2 : 2 ≤ m := by omega
  -- φ(n) ≤ n - 1 = m + 1
  have hφ : (m + 2).totient ≤ m + 1 := by
    have := Nat.totient_lt (m + 2) (by omega); omega
  -- (m+2)! = (m+2)·(m+1)·m!
  have hfac : (m + 2).factorial = (m + 2) * ((m + 1) * m.factorial) := by
    rw [Nat.factorial_succ, Nat.factorial_succ]
  -- m! ≥ 2 since m ≥ 2
  have hmfac : 2 ≤ m.factorial := by
    calc (2 : ℕ) = Nat.factorial 2 := by decide
      _ ≤ m.factorial := Nat.factorial_le hm2
  -- lower-degree bound on the metacyclic order
  have hlhs : (m + 2) * (m + 2).totient ≤ (m + 2) * (m + 1) := by gcongr
  -- the factorial dominates twice the metacyclic order
  have hrhs : (m + 2) * (m + 1) * 2 ≤ (m + 2).factorial := by
    rw [hfac]
    calc (m + 2) * (m + 1) * 2 ≤ (m + 2) * (m + 1) * m.factorial := by gcongr
      _ = (m + 2) * ((m + 1) * m.factorial) := by ring
  have hApos : 0 < (m + 2) * (m + 1) := by positivity
  -- (m+2)! = lhs ≤ (m+2)(m+1) but also 2·(m+2)(m+1) ≤ (m+2)!  ⟹  contradiction
  nlinarith [h, hlhs, hrhs, hApos]

-- ============================================================================
-- Part II: The pin theorem — coprimality is automatic at the boundary
-- ============================================================================

/-- **`n·φ(n) = n! ⟹ |Gal(Xⁿ-p/ℚ)| = n!`.**  The hypothesis is exactly the squeeze
condition.  Crucially it carries *no* separate coprimality assumption: by
`totient_mul_eq_factorial_iff` the only degrees satisfying it are `n ∈ {2, 3}`, both of
which have `gcd(n, φ(n)) = 1`, so the coprime lower bound
`mul_totient_dvd_gal_card_of_coprime` applies and meets the upper bound `|Gal| ∣ n!`. -/
theorem gal_card_eq_factorial_of_pin (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime)
    (hpin : n * n.totient = n.factorial) :
    Fintype.card (X ^ n - C (p : ℚ) : ℚ[X]).Gal = n.factorial := by
  have hcop : Nat.Coprime n n.totient := by
    rcases (totient_mul_eq_factorial_iff hn).mp hpin with rfl | rfl <;> decide
  have hlow := mul_totient_dvd_gal_card_of_coprime n p hn hp hcop
  rw [hpin] at hlow
  exact Nat.dvd_antisymm (gal_card_dvd_factorial n p hn hp) hlow

-- ============================================================================
-- Part III: The quadratic companion witness  |Gal(X²-p/ℚ)| = 2
-- ============================================================================

/-- **`|Gal(X²-p/ℚ)| = 2`** for every prime `p`.  The quadratic companion of the cubic
witness `gal_card_cubic_eq_six`: here `2·φ(2) = 2·1 = 2 = 2!`, so the bracket pins the
order to `2 = |C₂|`, the Galois group of the quadratic field `ℚ(√p)`. -/
theorem gal_card_quadratic_eq_two (p : ℕ) (hp : p.Prime) :
    Fintype.card (X ^ 2 - C (p : ℚ) : ℚ[X]).Gal = 2 := by
  have h := gal_card_eq_factorial_of_pin 2 p (by norm_num) hp (by decide)
  simpa using h

end InverseGaloisExtensions
