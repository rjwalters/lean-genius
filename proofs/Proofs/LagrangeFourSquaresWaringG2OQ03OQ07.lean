import Mathlib

/-!
# The multiplier–quadratic-residue reduction for three-square sufficiency

**Open question (`lagrange-four-squares-waring-g2-oq-03-oq-07`)**, a slice of the
"if" direction of Legendre's three-square theorem
(`lagrange-four-squares-waring-g2-oq-03`).

## Background: the multiplier mechanism

The classical Dirichlet/Minkowski route to *sufficiency*
(`n ≠ 4^a(8b+7) ⟹ n = x²+y²+z²`) hinges on a geometry-of-numbers step
(`Proofs.ThreeSquares.dirichlet_key_lemma`) whose hypotheses are:

* a **multiplier** `d ≥ 1` and a **prime** `p = d·n − 1`, and
* a **quadratic-residue condition** `legendreSym p (−d) = 1`.

From such data the sublattice `L = {(x,y,z) : p ∣ x − r·y, p ∣ z}` carries a
short vector that descends to a representation of `n`.  Dirichlet's theorem on
primes in arithmetic progressions (now in Mathlib as
`Nat.forall_exists_prime_gt_and_modEq`) is what supplies the prime `p` once the
right congruence class is identified.

The friction in the existing development is that the QR condition is phrased in
terms of the **multiplier** `d`, which — for the residue classes
`n mod 8 ∈ {1,2,5,6}` — must be allowed to grow unboundedly (no small `d` works).
That makes the Dirichlet selection look like it must control a moving target.

## What this file proves

The QR condition on the multiplier collapses to a QR condition on `n` **alone**.

Because `p = d·n − 1`, we have `d·n ≡ 1 (mod p)`, hence
`(−d)·(−n) = d·n ≡ 1 (mod p)`, so `−d` and `−n` are inverse modulo `p`.  Two
numbers that are inverse mod `p` are simultaneously squares or simultaneously
non-squares, therefore

  `legendreSym p (−d) = legendreSym p (−n)`     (`legendreSym_neg_multiplier_eq`).

In particular the geometry's hypothesis `legendreSym p (−d) = 1` is **equivalent**
to `legendreSym p (−n) = 1` — a condition that depends only on `p` (through
`p mod 4n`, by quadratic reciprocity), with the awkward multiplier `d` entirely
eliminated.  This is exactly the simplification that makes the Dirichlet
selection a fixed-target problem.

We also record the Dirichlet **supply** of multiplier primes
(`exists_multiplier_prime`): for every `n ≥ 2` and every bound `N` there is a
prime `p > N` of the form `p = d·n − 1`.  Combining the two
(`exists_multiplier_prime_qr_reduces`) yields, for every bound, a multiplier
prime for which the geometry's QR hypothesis is governed solely by
`legendreSym p (−n)`.

## Honest scope

This is the **selection / number-theoretic** layer.  It is `0`-axiom and
self-contained.  It does **not** by itself discharge the sufficiency axiom
`Proofs.ThreeSquares.not_excluded_form_is_sum_three_sq`: the companion geometry
lemma `dirichlet_key_lemma` is currently established only for `d ∈ {1,2}` (its
final descent `x² + d·y² = d·n − 1 ⟹ three squares` is special to those
multipliers), whereas the classes needing unbounded `d` would require a
`d`-uniform geometric construction.  What this file removes is the *apparent*
need to track `d` inside the residue/QR bookkeeping.

No `axiom`, no `sorry`, no `native_decide`.
-/

namespace ThreeSquaresMultiplierQR

/-- **Key residue identity.**  If `p = d·n − 1` (encoded as `d·n = p + 1`), then
`d·n ≡ 1 (mod p)`, i.e. `(d : ZMod p) · (n : ZMod p) = 1`. -/
lemma natCast_mul_eq_one {n d p : ℕ} [Fact p.Prime] (hdn : d * n = p + 1) :
    (d : ZMod p) * (n : ZMod p) = 1 := by
  have h : (d : ZMod p) * (n : ZMod p) = ((d * n : ℕ) : ZMod p) := by push_cast; ring
  rw [h, hdn]
  push_cast
  rw [ZMod.natCast_self]
  ring

/-- **Multiplier–QR reduction (Legendre-symbol form).**
For a prime `p = d·n − 1`, the Legendre symbol of the *multiplier* `−d` equals
that of `−n`:

  `legendreSym p (−d) = legendreSym p (−n)`.

The point is that `(−d)·(−n) = d·n ≡ 1 (mod p)`, so `−d` and `−n` are inverse
modulo `p`; a unit and its inverse are simultaneously squares mod `p`. -/
theorem legendreSym_neg_multiplier_eq {n d p : ℕ} [Fact p.Prime]
    (hdn : d * n = p + 1) :
    legendreSym p (-(d : ℤ)) = legendreSym p (-(n : ℤ)) := by
  have hpc : (d : ZMod p) * (n : ZMod p) = 1 := natCast_mul_eq_one hdn
  -- `d` and `n` are units mod `p`, hence nonzero, hence so are their negations.
  have hdne : (d : ZMod p) ≠ 0 := by
    intro h; rw [h, zero_mul] at hpc; exact zero_ne_one hpc
  have hnne : (n : ZMod p) ≠ 0 := by
    intro h; rw [h, mul_zero] at hpc; exact zero_ne_one hpc
  -- `(−d)·(−n) ≡ 1 (mod p)`, so its Legendre symbol is `1` (it is a square).
  have hz : (((-(d : ℤ)) * (-(n : ℤ)) : ℤ) : ZMod p) = 1 := by
    push_cast; linear_combination hpc
  have hprod : legendreSym p (-(d : ℤ)) * legendreSym p (-(n : ℤ)) = 1 := by
    rw [← legendreSym.mul p]
    rw [legendreSym.eq_one_iff p (by rw [hz]; exact one_ne_zero)]
    rw [hz]; exact IsSquare.one
  -- Both symbols are `±1`; a product of `1` forces them equal.  (The nonzero
  -- hypotheses are elaborated directly against the expected `↑(-↑·) ≠ 0` form.)
  rcases legendreSym.eq_one_or_neg_one (p := p) (a := -(d : ℤ))
      (by push_cast; simpa using hdne) with hd | hd <;>
    rcases legendreSym.eq_one_or_neg_one (p := p) (a := -(n : ℤ))
      (by push_cast; simpa using hnne) with hn | hn <;>
    rw [hd, hn] at hprod ⊢ <;> simp_all

/-- **Selection criterion.**  The geometry's QR hypothesis on the multiplier is
equivalent to the QR condition on `n` itself. -/
theorem legendreSym_neg_d_eq_one_iff {n d p : ℕ} [Fact p.Prime]
    (hdn : d * n = p + 1) :
    legendreSym p (-(d : ℤ)) = 1 ↔ legendreSym p (-(n : ℤ)) = 1 := by
  rw [legendreSym_neg_multiplier_eq hdn]

/-- The QR condition on `n` *suffices* for the geometry's QR hypothesis on the
multiplier — the direction actually consumed by `dirichlet_key_lemma`. -/
theorem legendreSym_neg_n_one_imp_neg_d_one {n d p : ℕ} [Fact p.Prime]
    (hdn : d * n = p + 1) (h : legendreSym p (-(n : ℤ)) = 1) :
    legendreSym p (-(d : ℤ)) = 1 :=
  (legendreSym_neg_d_eq_one_iff hdn).2 h

/-- `n - 1` is coprime to `n` for `n ≥ 1` (consecutive integers). -/
lemma coprime_pred_self {n : ℕ} (hn : 1 ≤ n) : Nat.Coprime (n - 1) n := by
  rw [Nat.coprime_self_sub_left hn]
  exact Nat.coprime_one_left n

/-- **Dirichlet supply of multiplier primes.**  For every `n ≥ 2` and every
bound `N` there is a prime `p > N` of the multiplier shape `p = d·n − 1` with
`d ≥ 1`.  Here `p` is produced by Dirichlet's theorem in the residue class
`p ≡ n − 1 (mod n)`, i.e. `p ≡ −1`. -/
theorem exists_multiplier_prime {n : ℕ} (hn : 2 ≤ n) (N : ℕ) :
    ∃ p d : ℕ, N < p ∧ p.Prime ∧ 1 ≤ d ∧ d * n = p + 1 := by
  have hq : n ≠ 0 := by omega
  have hcop : Nat.Coprime (n - 1) n := coprime_pred_self (by omega)
  obtain ⟨p, hpgt, hpp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N n) hq hcop
  have hpN : N < p := lt_of_le_of_lt (le_max_left _ _) hpgt
  have hpn : n < p := lt_of_le_of_lt (le_max_right _ _) hpgt
  -- `p ≡ n − 1 (mod n)` pins down `p % n = n − 1`.
  have hpmod' : p % n = n - 1 := by
    have h1 : p % n = (n - 1) % n := hpmod
    rw [Nat.mod_eq_of_lt (show n - 1 < n by omega)] at h1
    exact h1
  -- Repackage the quotient as a fresh variable `q` (avoiding `p / n`, which
  -- `omega` cannot reason about for a variable divisor `n`).
  obtain ⟨q, hq⟩ : ∃ q, n * q + (n - 1) = p :=
    ⟨p / n, by rw [← hpmod']; exact Nat.div_add_mod p n⟩
  -- The multiplier is `d := q + 1`.
  refine ⟨p, q + 1, hpN, hpp, by omega, ?_⟩
  have hexp : (q + 1) * n = n * q + n := by ring
  rw [hexp]
  omega

/-- **Selection assembled.**  For every `n ≥ 2` and every bound `N` there is a
prime `p > N` of multiplier shape `p = d·n − 1` for which the geometry's QR
hypothesis `legendreSym p (−d) = 1` is governed *solely* by `legendreSym p (−n)`:
the latter being `1` already forces the former.  (The supplied `Fact p.Prime`
instance is the standard hook for `legendreSym`.) -/
theorem exists_multiplier_prime_qr_reduces {n : ℕ} (hn : 2 ≤ n) (N : ℕ) :
    ∃ p d : ℕ, N < p ∧ p.Prime ∧ 1 ≤ d ∧ d * n = p + 1 ∧
      ∀ _ : Fact p.Prime,
        legendreSym p (-(n : ℤ)) = 1 → legendreSym p (-(d : ℤ)) = 1 := by
  obtain ⟨p, d, hpN, hpp, hd1, hdn⟩ := exists_multiplier_prime hn N
  exact ⟨p, d, hpN, hpp, hd1, hdn, fun _ h =>
    legendreSym_neg_n_one_imp_neg_d_one hdn h⟩

end ThreeSquaresMultiplierQR
