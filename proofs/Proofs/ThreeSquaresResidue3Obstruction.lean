/-
  The residue-3 obstruction for Legendre's three-square theorem.

  CONTEXT.  `Proofs.ThreeSquares` leaves the sufficiency direction as an axiom
  `not_excluded_form_is_sum_three_sq`, whose representation engine is
  `dirichlet_key_lemma` (ThreeSquares.lean:615): given `n > 1`, `d > 0`, a prime
  `p = d·n − 1`, and `legendreSym p (−d) = 1`, it produces `x²+y²+z² = n`.

  The corrected sufficiency split (`Proofs.ThreeSquaresSufficiencyCorrected`)
  routes the residue class `m ≡ 3 (mod 8)` through a SEPARATE `Residue3Property`
  rather than through `dirichlet_key_lemma`.  The justification, recorded across
  several sessions as a purely NUMERICAL observation ("no Dirichlet witness for
  any 4-free core `m ≡ 3 (mod 8)`, 0/750"), is upgraded here to a THEOREM:

      For `m ≡ 3 (mod 4)` and any odd prime `p` with `p ≡ −1 (mod m)`,
            legendreSym p (−m) = −1,
      and consequently (since `d·m ≡ 1 (mod p)` ⟹ `legendreSym p (−d) =
      legendreSym p (−m)`)  the witness condition `legendreSym p (−d) = 1` is
      UNSATISFIABLE.

  Hence `dirichlet_key_lemma` provably cannot reach `m ≡ 3 (mod 4)` — among the
  non-excluded 4-free cores that is exactly `m ≡ 3 (mod 8)` — so the residue-3
  carve-out is not an artifact of a finite search but a genuine obstruction.

  PROOF.  Pure quadratic reciprocity for the Jacobi symbol.  Writing
  `(−m | p) = χ₄(p) · (m | p)` and `(m | p) = ± (p | m)` (sign from `p mod 4`,
  using `m ≡ 3 (mod 4)`), together with `(p | m) = (−1 | m) = χ₄(m) = −1`
  (because `p ≡ −1 (mod m)` and `m ≡ 3 (mod 4)`), the two `p`-dependent signs
  cancel in BOTH residue classes `p ≡ 1, 3 (mod 4)`, leaving `(−m | p) = −1`.

  All Mathlib bearers are name-checked against the pinned rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).  Independently certified
  build-free over 51 986 prime pairs by
  `research/problems/lagrange-four-squares-waring-g2-oq-03/verify_residue3_obstruction.py`.

  NOTE: build-pending — the worktree `.lake` is a circular self-symlink that
  defeats the olean cache, so `docker-build` cannot verify this file locally;
  the cache-warm deployer build-gate is the verifier.  Not registered in
  `Proofs.lean`; harmless to the rest of the build.
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.Basic

namespace ThreeSquares

/-- Core reciprocity computation: for `m ≡ 3 (mod 4)` and `p ≡ −1 (mod m)`,
the Jacobi symbol `J(p | m) = −1`.  Here `m` may be composite, which is why the
Jacobi (not Legendre) symbol is used on the `m` side. -/
lemma jacobi_p_mod_m_eq_neg_one {m p : ℕ} (hm3 : m % 4 = 3) (hdvd : m ∣ (p + 1)) :
    jacobiSym (p : ℤ) m = -1 := by
  have hm_odd : Odd m := Nat.odd_iff.mpr (by omega)
  -- `p ≡ −1 (mod m)` as integers.
  have hme : (p : ℤ) % (m : ℤ) = (-1 : ℤ) % (m : ℤ) := by
    have hdvdZ : (m : ℤ) ∣ ((p : ℤ) + 1) := by exact_mod_cast hdvd
    have hdvd2 : (m : ℤ) ∣ ((-1 : ℤ) - (p : ℤ)) := by
      have hrw : (-1 : ℤ) - (p : ℤ) = -((p : ℤ) + 1) := by ring
      rw [hrw]; exact (dvd_neg).mpr hdvdZ
    exact Int.modEq_iff_dvd.mpr hdvd2
  rw [jacobiSym.mod_left' hme, jacobiSym.at_neg_one hm_odd]
  exact ZMod.χ₄_nat_three_mod_four hm3

/-- **The residue-3 obstruction.**  For `m ≡ 3 (mod 4)`, any odd prime `p` with
`p ≡ −1 (mod m)` has `−m` as a quadratic NON-residue: `legendreSym p (−m) = −1`. -/
theorem legendreSym_neg_m_eq_neg_one {m p : ℕ} [Fact (Nat.Prime p)]
    (hm3 : m % 4 = 3) (hp_odd : Odd p) (hdvd : m ∣ (p + 1)) :
    legendreSym p (-(m : ℤ)) = -1 := by
  have hm_odd : Odd m := Nat.odd_iff.mpr (by omega)
  have hJpm : jacobiSym (p : ℤ) m = -1 := jacobi_p_mod_m_eq_neg_one hm3 hdvd
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.neg (m : ℤ) hp_odd]
  -- goal: χ₄ p * J(m | p) = -1
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hp_odd
  rcases (by omega : p % 4 = 1 ∨ p % 4 = 3) with hp1 | hp3
  · -- p ≡ 1 (mod 4): χ₄ p = 1 and J(m | p) = J(p | m) = -1.
    rw [ZMod.χ₄_nat_one_mod_four hp1, one_mul,
        ← jacobiSym.quadratic_reciprocity_one_mod_four hp1 hm_odd]
    exact hJpm
  · -- p ≡ 3 (mod 4): χ₄ p = -1 and J(m | p) = -J(p | m) = 1.
    rw [ZMod.χ₄_nat_three_mod_four hp3,
        jacobiSym.quadratic_reciprocity_three_mod_four hm3 hp3, hJpm]
    norm_num

/-- The witness multiplier `d` carries the same Legendre symbol as `m`: since
`p = d·m − 1` gives `d·m ≡ 1 (mod p)`, we have `legendreSym p (−d) =
legendreSym p (−m)`. -/
theorem legendreSym_neg_d_eq_neg_m {m d p : ℕ} [Fact (Nat.Prime p)]
    (hp : p = d * m - 1) (hd : 0 < d) (hm : 0 < m) :
    legendreSym p (-(d : ℤ)) = legendreSym p (-(m : ℤ)) := by
  have hk : 1 ≤ d * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdm : d * m = p + 1 := by omega
  have hdmZ : (d : ℤ) * (m : ℤ) = (p : ℤ) + 1 := by exact_mod_cast hdm
  -- `m` is a unit mod `p`, hence nonzero mod `p`.
  have hunit : (m : ZMod p) * (d : ZMod p) = 1 := by
    have hcast : ((d * m : ℕ) : ZMod p) = 1 := by
      rw [hdm]; push_cast; rw [ZMod.natCast_self]; ring
    push_cast at hcast; linear_combination hcast
  have hm0 : (m : ZMod p) ≠ 0 := by
    intro h; rw [h, zero_mul] at hunit; exact zero_ne_one hunit
  -- product of the two symbols is 1
  have key : legendreSym p (-(d : ℤ)) * legendreSym p (-(m : ℤ)) = 1 := by
    rw [← legendreSym.mul]
    have hprod : (-(d : ℤ)) * (-(m : ℤ)) = (d : ℤ) * (m : ℤ) := by ring
    rw [hprod, legendreSym.mod]
    have hmod : ((d : ℤ) * (m : ℤ)) % (p : ℤ) = (1 : ℤ) % (p : ℤ) := by
      rw [hdmZ, show ((p : ℤ) + 1) = 1 + (p : ℤ) * 1 by ring, Int.add_mul_emod_self_left]
    rw [hmod, ← legendreSym.mod, legendreSym.at_one]
  -- conclude equality using `(−m | p)² = 1`
  have hb2 : legendreSym p (-(m : ℤ)) ^ 2 = 1 := by
    apply legendreSym.sq_one; push_cast; simpa using hm0
  calc legendreSym p (-(d : ℤ))
      = legendreSym p (-(d : ℤ)) * legendreSym p (-(m : ℤ)) ^ 2 := by rw [hb2, mul_one]
    _ = (legendreSym p (-(d : ℤ)) * legendreSym p (-(m : ℤ))) * legendreSym p (-(m : ℤ)) := by
          ring
    _ = 1 * legendreSym p (-(m : ℤ)) := by rw [key]
    _ = legendreSym p (-(m : ℤ)) := one_mul _

/-- **No Dirichlet witness for the residue-3 class.**  For `m ≡ 3 (mod 4)` and a
multiplier `d > 0` with `p = d·m − 1` an odd prime, the witness condition of
`dirichlet_key_lemma` fails: `legendreSym p (−d) = −1 ≠ 1`.  This is the exact
statement justifying the `Residue3Property` carve-out (the witness is provably
unsatisfiable on `m ≡ 3 (mod 8)`, the non-excluded 4-free cores in this class). -/
theorem no_residue3_witness {m d p : ℕ} [Fact (Nat.Prime p)]
    (hm3 : m % 4 = 3) (hp_odd : Odd p) (hp : p = d * m - 1) (hd : 0 < d) (hm : 0 < m) :
    legendreSym p (-(d : ℤ)) = -1 := by
  have hk : 1 ≤ d * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdvd : m ∣ (p + 1) := ⟨d, by rw [show p + 1 = d * m by omega, Nat.mul_comm]⟩
  rw [legendreSym_neg_d_eq_neg_m hp hd hm]
  exact legendreSym_neg_m_eq_neg_one hm3 hp_odd hdvd

end ThreeSquares
