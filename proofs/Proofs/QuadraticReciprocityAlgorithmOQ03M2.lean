/-
  Milestone 2 of the permutation-sign (Zolotarev) route to quadratic reciprocity.

  Milestone 1 (`Proofs.QuadraticReciprocityAlgorithmOQ03`) proved Zolotarev's
  lemma `legendreSym p a = Equiv.Perm.sign (Equiv.mulLeft a)` (verified, merged).
  Milestone 2 is the reciprocity step: the product `(p/q)·(q/p)` equals the sign
  of a single "grid-transpose" permutation of `Fin (p*q)`, and that sign is
  `(-1) ^ ((p-1)/2 · (q-1)/2)`.

  The grid-transpose `σ` reinterprets a row-major linear index of the `p × q`
  grid as the corresponding column-major index (swap the two coordinates between
  the two `finProdFinEquiv` encodings).  Its number of inversions is
  `C(p,2)·C(q,2) = [p(p-1)/2]·[q(q-1)/2]`, which for odd `p, q` is congruent mod 2
  to `(p-1)/2·(q-1)/2`; hence `sign σ = (-1)^((p-1)/2·(q-1)/2)`.  This inversion
  count is primality-free and was certified build-free in
  `research/problems/quadratic-reciprocity-algorithm-oq-03/verify_grid_inversions.py`
  (S8) and `verify_reciprocity_m2.py` (S6).

  STATUS: the `gridTranspose` definition is complete; the sign value
  (`sign_gridTranspose`) is the single genuinely-new combinatorial lemma with no
  upstream Mathlib bearer — it is left as a `sorry` here and submitted to the
  Aristotle prover.  Unregistered (carries a sorry); harmless to the build.
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

/-- **Milestone 2 core lemma.**  For odd `p, q`, the sign of the grid-transpose
permutation is the quadratic-reciprocity factor `(-1) ^ ((p-1)/2 · (q-1)/2)`.

This is the genuinely-new content of Milestone 2: Mathlib has no closed-form sign
(or inversion count) for the grid transpose.  The proof goes through the
inversion count `C(p,2)·C(q,2)` (Mathlib defines `sign` via parity of inversions,
`signAux`/`finPairsLT`) and the elementary parity reduction
`C(p,2)·C(q,2) ≡ (p-1)/2·(q-1)/2 (mod 2)` for odd `p, q`. -/
theorem sign_gridTranspose {p q : ℕ} (hp : Odd p) (hq : Odd q) :
    Equiv.Perm.sign (gridTranspose p q) = (-1 : ℤˣ) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  sorry

end QuadraticReciprocityAlgorithmOQ03M2
