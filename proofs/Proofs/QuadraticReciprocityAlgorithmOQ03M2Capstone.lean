/-
  Milestone 2 capstone of the permutation-sign (Zolotarev) route to quadratic
  reciprocity.

  `Proofs.QuadraticReciprocityAlgorithmOQ03M2` proved the genuinely-new,
  primality-free combinatorial fact that the grid-transpose permutation of
  `Fin (p*q)` has sign

      sign (gridTranspose p q) = (-1) ^ ((p-1)/2 · (q-1)/2)        (M2, verified)

  computed from first principles via its inversion count `C(p,2)·C(q,2)` — a
  closed form Mathlib does not provide.  This file records the capstone of the
  Zolotarev route: that this combinatorial sign IS the quadratic-reciprocity
  factor, i.e. it equals the product of Legendre symbols

      legendreSym q p · legendreSym p q = (sign (gridTranspose p q) : ℤ)

  for distinct odd primes `p, q`.  This is the headline the entry was built
  toward and the statement flagged "not yet in Lean" in the open questions of
  `quadratic-reciprocity-algorithm-oq-03`.

  HONESTY / SCOPE.  The *arithmetic* equality of the two `±1` factors — that the
  Legendre product equals `(-1)^(p/2·q/2)` — is supplied here by Mathlib's
  `legendreSym.quadratic_reciprocity`; this file does NOT re-derive quadratic
  reciprocity independently of Mathlib.  The new content this entry contributes
  is the M2 sign computation; the capstone below ties that combinatorial
  invariant to the Legendre product, exhibiting `(p/q)·(q/p)` concretely as the
  sign of a single explicit permutation.  The only bridging steps are the
  exponent identity `p/2 = (p-1)/2` for odd `p` and the `ℤˣ → ℤ` cast of
  `(-1)^n`.

  #print axioms confirms dependence only on `propext, Classical.choice,
  Quot.sound` (no `sorryAx`, no `native_decide`).
-/
import Mathlib
import Proofs.QuadraticReciprocityAlgorithmOQ03M2

namespace QuadraticReciprocityAlgorithmOQ03M2

open Equiv

/-- For an odd natural number `n`, integer division by two is unchanged by first
subtracting one: `n / 2 = (n - 1) / 2`.  (Mathlib's quadratic reciprocity uses the
`n/2` form; Milestone 2 uses the `(n-1)/2` form.) -/
theorem odd_div_two_eq {n : ℕ} (hn : Odd n) : n / 2 = (n - 1) / 2 := by
  obtain ⟨k, hk⟩ := hn
  omega

/-- **Zolotarev reciprocity headline (Milestone 2 capstone).**
For distinct odd primes `p, q`, the product of Legendre symbols equals the sign of
the grid-transpose permutation of `Fin (p*q)`:

    legendreSym q p · legendreSym p q = (sign (gridTranspose p q) : ℤ).

The right-hand side is the purely combinatorial, primality-free invariant computed
in `sign_gridTranspose`; the equality with the left-hand side packages the
quadratic-reciprocity factor (Mathlib's `legendreSym.quadratic_reciprocity`) as a
single explicit permutation sign — the goal of the Zolotarev route. -/
theorem legendreSym_mul_eq_sign_gridTranspose
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q
      = ((Equiv.Perm.sign (gridTranspose p q) : ℤˣ) : ℤ) := by
  have pp : p.Prime := Fact.out
  have qp : q.Prime := Fact.out
  have oddp : Odd p := pp.eq_two_or_odd'.resolve_left hp
  have oddq : Odd q := qp.eq_two_or_odd'.resolve_left hq
  rw [legendreSym.quadratic_reciprocity hp hq hpq, sign_gridTranspose oddp oddq,
      odd_div_two_eq oddp, odd_div_two_eq oddq, Units.val_pow_eq_pow_val]
  norm_num

end QuadraticReciprocityAlgorithmOQ03M2
