/-
# Lifting the Gauss-sum QR identity from `ZMod q` to `ℤ`

This file answers the open question

> `elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02-oq-01`:
> Can the `gauss_sum_zmod_qr` theorem be used to prove quadratic reciprocity
> *independently* of `legendreSym.quadratic_reciprocity`, i.e. lifting from
> `ZMod q` to `ℤ` directly?

The parent entry `elementary-quadratic-reciprocity-oq-01-oq-01-oq-01-oq-02`
establishes, for distinct odd primes `p ≠ q`, the **`ZMod q`-level** identity

    (-1)^(⌊p/2⌋·⌊q/2⌋) · (legendreSym q p : ZMod q) = (legendreSym p q : ZMod q)

via the four-step Gauss-sum architecture (`gauss_sum_zmod_qr`).  That identity
lives in the residue ring `ZMod q`, whereas the genuine reciprocity law is an
equality of *integers* (each Legendre symbol is `±1 ∈ ℤ`).

The remaining content of the open question is the **descent**: turning the
`ZMod q` congruence into an honest integer equality.  This is exactly what is
proved here in `int_qr_of_zmod_qr`, using nothing but:

* the multiplicativity / `±1`-valuedness of the Legendre symbol
  (`legendreSym.sq_one`, `legendreSym.eq_one_or_neg_one`), and
* injectivity of `ℤ → ZMod q` on the three-element set `{-1, 0, 1}` when
  `q ≥ 3` (a multiple of `q` whose absolute value is `≤ 2` must vanish).

Crucially the descent **does not** invoke `legendreSym.quadratic_reciprocity`.
Composing `int_qr_of_zmod_qr` with the parent's `gauss_sum_zmod_qr` therefore
yields a proof of integer quadratic reciprocity that is independent of
Mathlib's reciprocity theorem — answering the open question in the affirmative.

The hypothesis `hzmod` here is *verbatim* the conclusion of the parent's
`gauss_sum_zmod_qr`, so the two results plug together directly.

Self-contained: imports only Mathlib, no `sorry`, no `axiom`,
no `native_decide`.
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

namespace EQRDescentOQ010101020Q01

variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]

/-- For distinct primes `p ≠ q`, the integer `↑p` is nonzero in `ZMod q`
(equivalently, `q ∤ p`). -/
theorem castInt_ne_zero (hpq : p ≠ q) : ((p : ℤ) : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast]
  intro hdvd
  exact hpq ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).mp hdvd).symm

/--
**`ZMod q → ℤ` descent for quadratic reciprocity.**

Given the `ZMod q`-level Gauss-sum reciprocity identity `hzmod` (the exact
conclusion of the parent's `gauss_sum_zmod_qr`), the integer reciprocity law

    legendreSym p q · legendreSym q p = (-1)^(⌊p/2⌋·⌊q/2⌋)

follows *without* using `legendreSym.quadratic_reciprocity`.

Idea: multiply `hzmod` by `(legendreSym q p : ZMod q)` and use
`(legendreSym q p)² = 1` to obtain
`((-1)^e : ZMod q) = (legendreSym p q · legendreSym q p : ZMod q)`.
Both sides are integers in `{-1, 1}`, and the map `ℤ → ZMod q` separates them
because `q ≥ 3`; hence the equality already holds in `ℤ`.
-/
theorem int_qr_of_zmod_qr (_hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p ≠ q)
    (hzmod : (-1 : ZMod q) ^ (p / 2 * (q / 2)) * (legendreSym q (p : ℤ) : ZMod q)
        = (legendreSym p (q : ℤ) : ZMod q)) :
    legendreSym p (q : ℤ) * legendreSym q (p : ℤ) = (-1) ^ (p / 2 * (q / 2)) := by
  set e := p / 2 * (q / 2) with he
  -- `↑p ≠ 0` in `ZMod q` and `↑q ≠ 0` in `ZMod p`.
  have hpne : ((p : ℤ) : ZMod q) ≠ 0 := castInt_ne_zero p q hpq
  have hqne : ((q : ℤ) : ZMod p) ≠ 0 := castInt_ne_zero q p (Ne.symm hpq)
  -- `(legendreSym q p)² = 1`, transported into `ZMod q`.
  have hsq : legendreSym q (p : ℤ) ^ 2 = 1 := legendreSym.sq_one (p := q) hpne
  have hB2 : (legendreSym q (p : ℤ) : ZMod q) ^ 2 = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod q)) hsq
    push_cast at this
    exact this
  -- Multiply `hzmod` by `(legendreSym q p : ZMod q)` and cancel the square.
  have key : (-1 : ZMod q) ^ e
      = (legendreSym p (q : ℤ) : ZMod q) * (legendreSym q (p : ℤ) : ZMod q) := by
    calc (-1 : ZMod q) ^ e
        = (-1 : ZMod q) ^ e * (legendreSym q (p : ℤ) : ZMod q) ^ 2 := by rw [hB2, mul_one]
      _ = (-1 : ZMod q) ^ e * (legendreSym q (p : ℤ) : ZMod q)
            * (legendreSym q (p : ℤ) : ZMod q) := by ring
      _ = (legendreSym p (q : ℤ) : ZMod q) * (legendreSym q (p : ℤ) : ZMod q) := by
            rw [hzmod]
  -- Read the equality back as a divisibility statement over `ℤ`.
  have hdvd : (q : ℤ) ∣ ((-1 : ℤ) ^ e - legendreSym p (q : ℤ) * legendreSym q (p : ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [sub_eq_zero]
    exact key
  -- The difference lies in `{-2, 0, 2}` since every factor is `±1`.
  have hbound : |(-1 : ℤ) ^ e - legendreSym p (q : ℤ) * legendreSym q (p : ℤ)| ≤ 2 := by
    have h1 : (-1 : ℤ) ^ e = 1 ∨ (-1 : ℤ) ^ e = -1 := neg_one_pow_eq_or ℤ e
    have h2 : legendreSym p (q : ℤ) = 1 ∨ legendreSym p (q : ℤ) = -1 :=
      legendreSym.eq_one_or_neg_one (p := p) hqne
    have h3 : legendreSym q (p : ℤ) = 1 ∨ legendreSym q (p : ℤ) = -1 :=
      legendreSym.eq_one_or_neg_one (p := q) hpne
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
      rw [h1, h2, h3] <;> norm_num
  -- `q ≥ 3`, so the only multiple of `q` with `|·| ≤ 2` is `0`.
  have hq3 : (3 : ℤ) ≤ (q : ℤ) := by
    have h2le := (Fact.out : q.Prime).two_le
    have : (3 : ℕ) ≤ q := by omega
    exact_mod_cast this
  have hdzero : (-1 : ℤ) ^ e - legendreSym p (q : ℤ) * legendreSym q (p : ℤ) = 0 := by
    by_contra hne
    have hle : (q : ℤ) ≤ |(-1 : ℤ) ^ e - legendreSym p (q : ℤ) * legendreSym q (p : ℤ)| :=
      Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
    linarith
  linarith [hdzero]

end EQRDescentOQ010101020Q01
