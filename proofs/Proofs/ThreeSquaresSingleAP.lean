/-
  The single-AP witness for Legendre's three-square theorem (positive direction).

  CONTEXT.  `Proofs.ThreeSquares` leaves the sufficiency direction
  (`n ≠ 4^a(8b+7) ⟹ ∃ x y z, x²+y²+z² = n`) as an axiom, whose representation
  engine `dirichlet_key_lemma` (ThreeSquares.lean:615) consumes a prime `p` with
  `legendreSym p (−d) = 1`.  Earlier sessions baked the witness into the rigid
  shape `p = d·n − 1`; `Proofs.ThreeSquaresResidue3Obstruction` then proved that
  shape is UNSATISFIABLE for the residue class `n ≡ 3 (mod 4)`
  (`no_residue3_witness`), forcing a separate `Residue3Property` carve-out and a
  delicate `m = t² + 2p` Hardy–Littlewood-type existence input.

  THIS FILE supplies the quadratic side-condition `legendreSym p (−n) = 1` for a
  *relaxed* form of the key lemma — one that would consume ANY prime `p` carrying
  that residue condition, rather than the rigid `p = d·n − 1`.  For such a relaxed
  engine the side-condition is satisfied by a SINGLE universal arithmetic
  progression:

      **Single-AP witness.**  For odd `n` and any prime `p ≡ 1 (mod 4n)`,
            legendreSym p (−n) = 1.

  Dirichlet's theorem on primes in AP (`Mathlib.NumberTheory.LSeries.PrimesInAP`)
  supplies a prime in the always-admissible class `1 (mod 4n)` (`gcd(1,4n)=1`),
  so every odd `n` — including `n ≡ 3 (mod 8)` — gets a usable witness from one
  uniform branch.  No `t² + 2p`, no multi-residue spread, no Residue3 carve-out.

  CAVEAT (corrected S15, 2026-06-19 — see `ThreeSquaresResidue3Obstruction`).  The
  `dirichlet_key_lemma` ACTUALLY PROVED in `ThreeSquares.lean:1440` is NOT that
  relaxed engine: its elementary descent uses the tie `p = d·n − 1` essentially
  (`p ∣ z` together with `d·z² ≥ p² > p` forces `z = 0`, after which `x² + d·y² =
  d·n − 1` reconstructs `n`).  A large Dirichlet prime `p ≡ 1 (mod 4n)` is not of
  the form `d·n − 1`, so the witness below does NOT slot into the proved key lemma,
  and this file contains no descent reconnecting such a `p` to `n = x²+y²+z²`.
  Consequently `legendreSym_neg_n_eq_one` and `exists_prime_eq_one_mod_four_mul`
  are currently ORPHAN: a correct, reusable quadratic witness held in reserve for a
  future relaxed-key-lemma route, not consumed by the current representation engine.

  PROOF.  Pure quadratic reciprocity, the positive mirror of the obstruction:
  `p ≡ 1 (mod 4) ⇒ (−1 | p) = 1`, so `(−n | p) = (n | p)`; `p ≡ 1 (mod 4)` makes
  the reciprocity sign `+1`, so `(n | p) = (p | n)`; and `p ≡ 1 (mod n) ⇒
  (p | n) = (1 | n) = 1`.

  Mathlib bearers name-checked against the pinned rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0):
  `jacobiSym.one_left`, `jacobiSym.mod_left'`,
  `jacobiSym.quadratic_reciprocity_one_mod_four`, `jacobiSym.neg`,
  `legendreSym.to_jacobiSym`, `ZMod.χ₄_nat_one_mod_four`.

  Independently certified build-free over square-free `n ≡ 3 (mod 8)` in
  `[3,4000)` by
  `research/problems/lagrange-four-squares-waring-g2-oq-03/verify_single_ap_residue3.py`.

  STATUS: 0 sorries, 0 axioms.  The Dirichlet existence input
  (`exists_prime_eq_one_mod_four_mul`) is discharged via
  `Nat.forall_exists_prime_gt_and_modEq` at the always-admissible class `1 (mod 4n)`.
  Registered in `Proofs.lean`.  Build-verified S15 (2026-06-19):
  `docker-build.sh Proofs.ThreeSquaresSingleAP` → `Build completed successfully`.
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP

namespace ThreeSquares

/-- `p ≡ 1 (mod n)` (via `n ∣ p − 1`, `p ≥ 1`) forces the Jacobi symbol
`J(p | n) = 1`.  Positive mirror of `jacobi_p_mod_m_eq_neg_one` in
`ThreeSquaresResidue3Obstruction`; `n` may be composite, hence Jacobi. -/
lemma jacobi_p_mod_n_eq_one {n p : ℕ} (hple : 1 ≤ p) (hdvd : n ∣ (p - 1)) :
    jacobiSym (p : ℤ) n = 1 := by
  -- `p ≡ 1 (mod n)` as integers.
  have hme : (p : ℤ) % (n : ℤ) = (1 : ℤ) % (n : ℤ) := by
    have hdvdZ : (n : ℤ) ∣ ((p : ℤ) - 1) := by
      have h : (n : ℤ) ∣ ((p - 1 : ℕ) : ℤ) := by exact_mod_cast hdvd
      rwa [Nat.cast_sub hple, Nat.cast_one] at h
    have hdvd2 : (n : ℤ) ∣ ((1 : ℤ) - (p : ℤ)) := by
      have hrw : (1 : ℤ) - (p : ℤ) = -((p : ℤ) - 1) := by ring
      rw [hrw]; exact (dvd_neg).mpr hdvdZ
    exact Int.modEq_iff_dvd.mpr hdvd2
  rw [jacobiSym.mod_left' hme, jacobiSym.one_left]

/-- **Single-AP witness.**  For odd `n` and any prime `p ≡ 1 (mod 4n)`, `−n` is a
quadratic residue: `legendreSym p (−n) = 1`.  This is the quadratic side-condition
of `dirichlet_key_lemma` (after dropping the rigid `p = d·n − 1` tie), satisfied
uniformly by the single arithmetic progression `1 (mod 4n)`. -/
theorem legendreSym_neg_n_eq_one {n p : ℕ} [Fact (Nat.Prime p)]
    (hn_odd : Odd n) (hp4n : p % (4 * n) = 1) :
    legendreSym p (-(n : ℤ)) = 1 := by
  have hp_pos : 1 ≤ p := (Fact.out : Nat.Prime p).one_lt.le
  have hn_pos : 1 ≤ n := hn_odd.pos
  -- `4n ∣ p − 1`, hence `4 ∣ p − 1` and `n ∣ p − 1`.
  have hdecomp : p = (4 * n) * (p / (4 * n)) + 1 := by
    conv_lhs => rw [← Nat.div_add_mod p (4 * n)]
    rw [hp4n]
  have h4n_dvd : (4 * n) ∣ (p - 1) := ⟨p / (4 * n), by omega⟩
  have hn_dvd : n ∣ (p - 1) := dvd_trans ⟨4, by ring⟩ h4n_dvd
  have h4_dvd : (4 : ℕ) ∣ (p - 1) := dvd_trans ⟨n, by ring⟩ h4n_dvd
  have hp4 : p % 4 = 1 := by omega
  -- `J(p | n) = 1`.
  have hJpn : jacobiSym (p : ℤ) n = 1 := jacobi_p_mod_n_eq_one hp_pos hn_dvd
  -- `p` is odd (needed for `jacobiSym.neg`).
  have hp_odd : Odd p := Nat.odd_iff.mpr (by omega)
  rw [jacobiSym.legendreSym.to_jacobiSym, jacobiSym.neg (n : ℤ) hp_odd]
  -- goal: `χ₄ p * J(n | p) = 1`
  rw [ZMod.χ₄_nat_one_mod_four hp4, one_mul,
      ← jacobiSym.quadratic_reciprocity_one_mod_four hp4 hn_odd]
  exact hJpn

/-- The existence input from Dirichlet's theorem: for any odd `n` there is a prime
`p` in the class `1 (mod 4n)` (always admissible, `gcd(1, 4n) = 1`).  Combined
with `legendreSym_neg_n_eq_one` this discharges the quadratic side-condition of
`dirichlet_key_lemma` for EVERY odd `n` in a single branch.

Bearer: Dirichlet's theorem on primes in arithmetic progressions,
`Nat.forall_exists_prime_gt_and_modEq` (in `Mathlib.NumberTheory.LSeries.PrimesInAP`):
for `q ≠ 0` and `Coprime a q`, there is a prime `> n` with `p ≡ a [MOD q]`.  The
class `a = 1`, `q = 4n` is always admissible (`Coprime 1 (4n)`). -/
theorem exists_prime_eq_one_mod_four_mul (n : ℕ) (hn_odd : Odd n) :
    ∃ p : ℕ, Nat.Prime p ∧ p % (4 * n) = 1 := by
  have hn_pos : 1 ≤ n := hn_odd.pos
  obtain ⟨p, _, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 0 (by omega : 4 * n ≠ 0)
      (Nat.coprime_one_left (4 * n))
  refine ⟨p, hp, ?_⟩
  have hmod' : p % (4 * n) = 1 % (4 * n) := hmod
  have h1 : (1 : ℕ) % (4 * n) = 1 := Nat.mod_eq_of_lt (by omega)
  omega

end ThreeSquares
