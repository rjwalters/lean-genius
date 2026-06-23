/-
  Milestone 2 of the permutation-sign (Zolotarev) route to quadratic reciprocity.

  Milestone 1 (`Proofs.QuadraticReciprocityAlgorithmOQ03`) proved Zolotarev's
  lemma `legendreSym p a = Equiv.Perm.sign (Equiv.mulLeft a)` (verified, merged).
  Milestone 2 is the reciprocity step: the product `(p/q)·(q/p)` equals the sign
  of a single "grid-transpose" permutation of `Fin (p*q)`, and that sign is
  `(-1) ^ ((p-1)/2 · (q-1)/2)`.

  The grid-transpose `σ` reinterprets a row-major linear index of the `p × q`
  grid as the corresponding column-major index.  Its number of inversions is
  `C(p,2)·C(q,2) = [p(p-1)/2]·[q(q-1)/2]`, which for odd `p, q` is congruent mod 2
  to `(p-1)/2·(q-1)/2`; hence `sign σ = (-1)^((p-1)/2·(q-1)/2)`.  This inversion
  count is primality-free and was certified build-free in
  `research/problems/quadratic-reciprocity-algorithm-oq-03/verify_grid_inversions.py`
  (S8) and `verify_reciprocity_m2.py` (S6).

  STATUS (this file). The combinatorial heart of M2 is split into three pieces:

    1. `gridTranspose`            — the permutation itself.                [def, complete]
    2. `sign_gridTranspose_eq_choose`
                                  — `sign σ = (-1)^(C(p,2)·C(q,2))`.       [SORRY: the one
                                     genuinely-new combinatorial fact, no upstream Mathlib
                                     bearer (S8/S18); ideal single-lemma Aristotle target.]
    3. `neg_one_pow_choose_two`   — parity reduction `(-1)^(C(p,2)·C(q,2)) =
                                     (-1)^((p-1)/2·(q-1)/2)` for odd p,q.   [VERIFIED]
    4. `sign_gridTranspose`       — assembly of 2 + 3.                      [VERIFIED modulo 2]

  Only step 2 carries a `sorry`.  Steps 3 and 4 are fully proved here, so the
  remaining open obligation is isolated to a single inversion-count identity.
  Unregistered (carries a sorry); harmless to the gallery build.
-/
import Mathlib

namespace QuadraticReciprocityAlgorithmOQ03M2

open Equiv

/-- The grid-transpose permutation of `Fin (p*q)`.

Decode a linear index as a row-major `(i, j) : Fin p × Fin q`, swap to
`(j, i) : Fin q × Fin p`, re-encode as a linear index of the transposed grid,
and `finCongr` the `q*p = p*q` cast back.  This is the permutation whose sign
carries the quadratic-reciprocity factor (the Zolotarev–Frobenius shuffle). -/
def gridTranspose (p q : ℕ) : Equiv.Perm (Fin (p * q)) :=
  (finProdFinEquiv (m := p) (n := q)).symm.trans <|
    (Equiv.prodComm (Fin p) (Fin q)).trans <|
      (finProdFinEquiv (m := q) (n := p)).trans (finCongr (Nat.mul_comm q p))

/-- For odd `n`, the parity of `C(n,2)` equals the parity of `(n-1)/2`.
(`C(n,2) = n·(n-1)/2 = n · (n-1)/2`; for odd `n` the leading factor `n` is odd,
so it does not change the parity of `(n-1)/2`.) -/
theorem choose_two_mod_two {n : ℕ} (hn : Odd n) :
    Nat.choose n 2 % 2 = ((n - 1) / 2) % 2 := by
  obtain ⟨m, rfl⟩ := hn
  rw [Nat.choose_two_right]
  have h1 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [h1]
  have hmul : (2 * m + 1) * (2 * m) = 2 * ((2 * m + 1) * m) := by ring
  rw [hmul, Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 2)]
  have h2 : 2 * m / 2 = m := by omega
  rw [h2, Nat.mul_mod]
  have h3 : (2 * m + 1) % 2 = 1 := by omega
  rw [h3, one_mul]
  omega

/-- In `ℤˣ` (a monoid, not a ring), `(-1)^n` depends only on `n` mod 2.
`Mathlib.neg_one_pow_eq_pow_mod_two` needs `[Ring R]`, which `ℤˣ` is not, so we
derive it directly from `neg_one_sq : (-1)^2 = 1` (which holds for any
`[Monoid R] [HasDistribNeg R]`, in particular `ℤˣ`). -/
theorem neg_one_units_pow_mod_two (n : ℕ) : (-1 : ℤˣ) ^ n = (-1 : ℤˣ) ^ (n % 2) := by
  nth_rewrite 1 [← Nat.mod_add_div n 2]
  rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

/-- **Parity reduction** (the verified elementary step of Milestone 2).
For odd `p, q`, `(-1)^(C(p,2)·C(q,2)) = (-1)^((p-1)/2 · (q-1)/2)`. -/
theorem neg_one_pow_choose_two {p q : ℕ} (hp : Odd p) (hq : Odd q) :
    (-1 : ℤˣ) ^ (Nat.choose p 2 * Nat.choose q 2)
      = (-1 : ℤˣ) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have key : (Nat.choose p 2 * Nat.choose q 2) % 2
      = ((p - 1) / 2 * ((q - 1) / 2)) % 2 := by
    rw [Nat.mul_mod, Nat.mul_mod ((p - 1) / 2), choose_two_mod_two hp, choose_two_mod_two hq]
  rw [neg_one_units_pow_mod_two (Nat.choose p 2 * Nat.choose q 2),
      neg_one_units_pow_mod_two ((p - 1) / 2 * ((q - 1) / 2)), key]

/-- **Milestone 2 core combinatorial lemma** (the single remaining obligation).
The sign of the grid-transpose equals `(-1)` to the inversion count
`C(p,2)·C(q,2)`.  Mathlib has no closed-form sign or inversion count for the grid
transpose (S8/S18), so this is the genuinely-new content.  It is primality-free
(holds for all `p, q`) and was certified numerically in
`verify_grid_inversions.py`.  Left as a `sorry`; a self-contained Aristotle target. -/
theorem sign_gridTranspose_eq_choose (p q : ℕ) :
    Equiv.Perm.sign (gridTranspose p q)
      = (-1 : ℤˣ) ^ (Nat.choose p 2 * Nat.choose q 2) := by
  sorry

/-- **Milestone 2 core lemma.**  For odd `p, q`, the sign of the grid-transpose
permutation is the quadratic-reciprocity factor `(-1) ^ ((p-1)/2 · (q-1)/2)`.

Assembled from the inversion count `sign_gridTranspose_eq_choose` and the parity
reduction `neg_one_pow_choose_two`. -/
theorem sign_gridTranspose {p q : ℕ} (hp : Odd p) (hq : Odd q) :
    Equiv.Perm.sign (gridTranspose p q) = (-1 : ℤˣ) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  rw [sign_gridTranspose_eq_choose, neg_one_pow_choose_two hp hq]

end QuadraticReciprocityAlgorithmOQ03M2
