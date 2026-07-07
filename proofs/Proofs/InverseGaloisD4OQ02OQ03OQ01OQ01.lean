/-
# Inverse Galois: the metacyclic upper bound `|Gal(Xⁿ-p)| ≤ n·φ(n)`
  (inverse-galois-d4-oq-02-oq-03-oq-01-oq-01)

The parent chain establishes, for a prime `p` and `n ≥ 2`, the lower divisibilities of the
order of `Gal(Xⁿ - p / ℚ)`

      n ∣ |Gal|        (`n_dvd_gal_card`,       the radical/kernel factor `Cₙ`)
      φ(n) ∣ |Gal|     (`totient_dvd_gal_card`,  the cyclotomic/quotient factor `(ℤ/n)ˣ`)
      lcm(n, φ(n)) ∣ |Gal|, and when `gcd(n, φ(n)) = 1` the product `n·φ(n) ∣ |Gal|`
                       (`lcm_dvd_gal_card`, `mul_totient_dvd_gal_card_of_coprime`),

together with the *symmetric-group* upper bound `|Gal| ∣ n!` (`gal_card_dvd_factorial`).
The conjectured metacyclic order under genericity is `n·φ(n)`, the order of the holomorph
`ℤ/n ⋊ (ℤ/n)ˣ`.  The deepest parent entry (`...OQ02OQ03OQ01`) pins the order *exactly* only
at `n = 2, 3`, precisely because there the elementary bracket closes — `n·φ(n) = n!`.  For
`n ≥ 4` the factorial bound has genuine slack (`n·φ(n) < n!`), so the order was left open;
its first listed open question asks for the *matching upper bound* `|Gal| ≤ n·φ(n)` via the
tower `SF = ℚ(ζₙ)(ⁿ√p)`, sharp where the `Sₙ` bound is not (e.g. `n = 5`).

This file supplies that upper bound, **unconditionally** — no genericity / linear-disjointness
hypothesis is needed.

  * `gal_card_le_n_mul_totient`        : `|Gal(Xⁿ-p/ℚ)| ≤ n·φ(n)` for every `n ≥ 2`, prime `p`.
        The splitting field `L` is generated over `ℚ` by a single root `α` and a primitive
        `n`-th root of unity `ζ` (every root is `ζⁱ·α`), so it sits in the tower
        `ℚ ⊆ ℚ(ζ) ⊆ ℚ(ζ)(α) = L` with `[ℚ(ζ):ℚ] = φ(n)` and `[L:ℚ(ζ)] ≤ n` (because `α` is a
        root of the degree-`n` polynomial `Xⁿ - p` over `ℚ(ζ)`).  Multiplying the tower
        degrees gives `[L:ℚ] = |Gal| ≤ n·φ(n)`.  This replaces the weak `n!` bound with the
        metacyclic bound — the missing ceiling of the bracket.

  * `gal_card_eq_n_mul_totient_of_coprime`
                                       : when `gcd(n, φ(n)) = 1` the coprime lower bound
        `n·φ(n) ∣ |Gal|` meets this ceiling, pinning `|Gal(Xⁿ-p/ℚ)| = n·φ(n)` exactly — for
        *every* prime `p`, with no genericity hypothesis.  Unlike the parent's `n = 2, 3`
        squeeze (which used the factorial bound), this works at every coprime degree,
        including those where `n·φ(n) < n!`.

  * `gal_card_quintic_eq_twenty`       : the first genuinely-new pin beyond the factorial
        squeeze — `|Gal(X⁵-p/ℚ)| = 20 = |F₂₀|` for every prime `p`.  Here `gcd(5, φ(5)) =
        gcd(5,4) = 1` so `5·φ(5) = 20 ∣ |Gal|`, while the meta-bound gives `|Gal| ≤ 20`; the
        factorial bound `|Gal| ∣ 120` alone could *not* close this (`20 < 120`).  This resolves
        the parent entry's first open question, exhibiting the affine group `F₂₀ = AGL(1,5)`
        as the uniform Galois group of `X⁵ - p`.

Status: 0 sorries, 0 axioms, no `native_decide`.  `#print axioms` on the headline theorems
reports only `propext, Classical.choice, Quot.sound`.
-/
import Mathlib
import Proofs.InverseGaloisD4OQ02OQ03

namespace InverseGaloisExtensions

open Polynomial

-- ============================================================================
-- The metacyclic ceiling `|Gal| ≤ n·φ(n)` and the coprime pin
-- `|Gal| = n·φ(n)` were originally proved here; identical statements were later
-- merged into the ancestor `InverseGaloisD4OQ02.lean` (PR #31630:
-- `gal_card_le_n_mul_totient`, `gal_card_eq_n_mul_totient_of_coprime`), which this
-- file imports transitively — the duplicates were removed to keep the namespace
-- coherent. The quintic instance below is this file's own contribution.
-- ============================================================================

/-- **`|Gal(X⁵-p/ℚ)| = 20`** for every prime `p` — the affine group `F₂₀ = AGL(1,5)`.
Since `gcd(5, φ(5)) = gcd(5, 4) = 1`, the coprime bracket pins the order: `5·φ(5) = 20 ∣
|Gal|` while the metacyclic ceiling gives `|Gal| ≤ 20`.  The factorial bound `|Gal| ∣ 5! =
120` alone cannot close this (`20 < 120`); the cyclotomic ceiling is essential.  This is the
first genuinely-new exact pin beyond the parent's `n = 2, 3` factorial squeeze. -/
theorem gal_card_quintic_eq_twenty (p : ℕ) (hp : p.Prime) :
    Fintype.card (X ^ 5 - C (p : ℚ) : ℚ[X]).Gal = 20 := by
  have h := gal_card_eq_n_mul_totient_of_coprime 5 p (by norm_num) hp (by decide)
  rw [h]; decide

end InverseGaloisExtensions
