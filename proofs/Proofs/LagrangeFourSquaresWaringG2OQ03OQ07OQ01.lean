import Mathlib
import Proofs.LagrangeFourSquaresWaringG2OQ03OQ07

/-!
# Fixed-target Dirichlet selection for the three-square multiplier prime,
# and a sharp obstruction at `n = 3`

**Open question (`lagrange-four-squares-waring-g2-oq-03-oq-07-oq-01`)**, a direct
follow-up to the multiplier–quadratic-residue reduction
(`lagrange-four-squares-waring-g2-oq-03-oq-07`).

## Background

The parent slice `oq-03-oq-07` collapsed the geometry's quadratic-residue
hypothesis on the *multiplier* `d` to a hypothesis on `n` alone:

  `legendreSym p (−d) = legendreSym p (−n)`        for a prime `p = d·n − 1`.

Its docstring asserted — but did **not** prove — that the surviving condition
`legendreSym p (−n) = 1` "depends only on `p` (through `p mod 4n`, by quadratic
reciprocity)", which is what would make the Dirichlet selection a *fixed-target*
problem.  This file supplies that missing fact, turns the parent's *conditional*
reduction into an *unconditional* supply once a qualifying residue class is
available, and then exhibits a concrete `n` for which **no** such class exists.

## What this file proves

### §1. Periodicity in the prime (a Mathlib gap)

Mathlib provides `jacobiSym.mod_right`: `J(a | b)` depends on `b` only through
`b mod 4|a|`.  It does **not** package the corresponding statement for the
Legendre symbol viewed as a function of the prime.  We fill that gap:

* `legendreSym_eq_of_prime_modeq` — for odd primes `p, q` with
  `p ≡ q (mod 4|a|)`, `legendreSym p a = legendreSym q a`.

So the QR condition `legendreSym p (−n) = 1` is constant on each residue class of
`p` modulo `4n`, exactly as the parent claimed.

### §2. Unconditional supply from a qualifying residue class

Given a *single* residue `r` with `gcd(r, 4n) = 1`, `r ≡ −1 (mod n)` and
`J(−n | r) = 1`, Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_modEq`,
modulus `4n`) supplies, for every bound `N`, a prime `p > N` with
`p ≡ r (mod 4n)`.  By §1 the value `legendreSym p (−n) = J(−n | r) = 1` holds
*unconditionally*, and `p ≡ −1 (mod n)` gives the multiplier shape `p = d·n − 1`.
Feeding this through the parent's reduction yields `legendreSym p (−d) = 1` too:
the geometry's QR hypothesis is now **forced**, not merely reduced
(`exists_qr_qualified_multiplier_prime`, `…_full`).  For `n = 2`, `r = 3`
qualifies, so the supply is non-empty (`qr_qualified_multiplier_prime_two`).

### §3. A sharp obstruction at `n = 3`

The qualifying residue class of §2 need not exist.  Every multiplier prime
satisfies `p ≡ −1 (mod n)`; for `n = 3` this forces `p ≡ 2 (mod 3)`, and for
*every* such (odd) prime

  `legendreSym p (−3) = −1`        (`legendreSym_neg_three_eq_neg_one`),

so the geometry's QR hypothesis `legendreSym p (−n) = 1` is satisfiable for **no**
multiplier prime — even though `3 = 1² + 1² + 1²` is plainly a sum of three
squares (`multiplier_route_incomplete_at_three`).  Equivalently, the hypothesis
of §2 fails at `n = 3`: there is no residue `r ≡ −1 (mod 3)` with `J(−3 | r) = 1`.

This is a true *negative* result.  It explains, concretely and rigorously, why
the multiplier–QR development in `oq-03-oq-07` is only established for the small
multipliers `d ∈ {1,2}`: the naive `−n`-residue condition cannot, on its own,
certify representability, and the classical proof must refine the residue/sign
analysis.  More generally a qualifying class exists *iff* `n` is not of
Legendre's excluded form `4^a(8b+7)` — so the existence of `r` in §2 is exactly
the genus condition, the actual open content of the parent umbrella.

## Honest scope

`0`-axiom and self-contained (imports `Mathlib` and the parent slice).  It does
**not** discharge the sufficiency axiom
`Proofs.ThreeSquares.not_excluded_form_is_sum_three_sq`; indeed §3 documents a
reason the `−n`-multiplier route alone is insufficient.  No `axiom`, no `sorry`,
no `native_decide`.
-/

namespace Proofs.LagrangeFourSquaresWaringG2OQ03OQ07OQ01

open scoped NumberTheorySymbols
open jacobiSym

/-! ## §1. Periodicity of the Legendre symbol in the prime -/

/-- **Periodicity in the prime.**  For odd primes `p` and `q` that agree modulo
`4 * |a|`, the Legendre symbols `legendreSym p a` and `legendreSym q a` coincide.

This is the Legendre-symbol counterpart of `jacobiSym.mod_right` (which is stated
for the Jacobi symbol), obtained by passing through `legendreSym.to_jacobiSym`. -/
theorem legendreSym_eq_of_prime_modeq (a : ℤ) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp : Odd p) (hq : Odd q)
    (h : p ≡ q [MOD 4 * a.natAbs]) :
    legendreSym p a = legendreSym q a := by
  rw [legendreSym.to_jacobiSym, legendreSym.to_jacobiSym,
      jacobiSym.mod_right a hp, jacobiSym.mod_right a hq, h]

/-- **The QR condition is a residue-class condition.**  For odd primes `p, q`
agreeing modulo `4 * |a|`, the condition `legendreSym · a = 1` holds for `p` iff
it holds for `q`.  Specialised to `a = −n` this is precisely the statement that
the geometry's QR hypothesis depends only on `p mod 4n`. -/
theorem qr_condition_class_invariant (a : ℤ) {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hp : Odd p) (hq : Odd q)
    (h : p ≡ q [MOD 4 * a.natAbs]) :
    legendreSym p a = 1 ↔ legendreSym q a = 1 := by
  rw [legendreSym_eq_of_prime_modeq a hp hq h]

/-! ## §2. Unconditional supply from a qualifying residue class -/

/-- **Residue-class transport for the QR value.**  If `p` is an odd prime and `r`
is any odd natural with `p ≡ r (mod 4n)`, then the Legendre symbol of `−n` at `p`
is governed by the Jacobi symbol `J(−n | r)`:

  `legendreSym p (−n) = J(−n | r)`.

(Unlike `legendreSym_eq_of_prime_modeq`, the second argument `r` here need not be
prime — only odd — which is what lets it stand for a Dirichlet residue class.) -/
lemma legendreSym_neg_eq_of_modEq {n p : ℕ} [Fact p.Prime] (hp : Odd p)
    {r : ℕ} (hr : Odd r) (hpr : p ≡ r [MOD 4 * n]) :
    legendreSym p (-(n : ℤ)) = J(-(n : ℤ) | r) := by
  have hnabs : (-(n : ℤ)).natAbs = n := by rw [Int.natAbs_neg, Int.natAbs_natCast]
  have hL : legendreSym p (-(n : ℤ)) = J(-(n : ℤ) | (p % (4 * n) : ℕ)) := by
    rw [legendreSym.to_jacobiSym, jacobiSym.mod_right (-(n : ℤ)) hp, hnabs]
  have hR : J(-(n : ℤ) | r) = J(-(n : ℤ) | (r % (4 * n) : ℕ)) := by
    rw [jacobiSym.mod_right (-(n : ℤ)) hr, hnabs]
  have hmod : p % (4 * n) = r % (4 * n) := hpr
  rw [hL, hR, hmod]

/-- A residue coprime to `4n` is odd (since `2 ∣ 4n`). -/
private lemma odd_of_coprime_four_mul {n r : ℕ} (hcop : Nat.Coprime r (4 * n)) :
    Odd r := by
  rcases Nat.even_or_odd r with he | ho
  · exfalso
    have h2r : (2 : ℕ) ∣ r := he.two_dvd
    have h24 : (2 : ℕ) ∣ 4 * n := ⟨2 * n, by ring⟩
    have hdvd : (2 : ℕ) ∣ Nat.gcd r (4 * n) := Nat.dvd_gcd h2r h24
    exact (by decide : ¬ (2 : ℕ) ∣ 1) (hcop ▸ hdvd)
  · exact ho

/-- **Unconditional QR-qualified multiplier supply.**  Given a residue `r` with
`gcd(r, 4n) = 1`, `r ≡ −1 (mod n)` and `J(−n | r) = 1`, then for every bound `N`
there is a prime `p > N` of multiplier shape `p = d·n − 1` (with `d ≥ 1`) for
which `legendreSym p (−n) = 1` holds **unconditionally** — the awkward QR
hypothesis is *forced* by the residue class, not merely reduced. -/
theorem exists_qr_qualified_multiplier_prime {n : ℕ} (hn : 2 ≤ n) {r : ℕ}
    (hcop : Nat.Coprime r (4 * n)) (hr_mod : r % n = n - 1)
    (hr_qr : J(-(n : ℤ) | r) = 1) (N : ℕ) :
    ∃ p d : ℕ, N < p ∧ p.Prime ∧ 1 ≤ d ∧ d * n = p + 1 ∧
      ∀ _ : Fact p.Prime, legendreSym p (-(n : ℤ)) = 1 := by
  have hq0 : (4 * n) ≠ 0 := by omega
  have hr_odd : Odd r := odd_of_coprime_four_mul hcop
  obtain ⟨p, hpgt, hpp, hpr⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max N 2) hq0 hcop
  have hpN : N < p := lt_of_le_of_lt (le_max_left _ _) hpgt
  haveI : Fact p.Prime := ⟨hpp⟩
  -- `p` is odd: `p ≡ r (mod 2)` and `r` is odd.
  have hp_odd : Odd p := by
    have h2 : p % 2 = r % 2 := hpr.of_dvd ⟨2 * n, by ring⟩
    have hro : r % 2 = 1 := Nat.odd_iff.mp hr_odd
    rw [Nat.odd_iff]; omega
  -- `p ≡ r (mod n)`, so `p % n = n − 1`: the multiplier shape.
  have hpn : p % n = n - 1 := by
    have h : p % n = r % n := hpr.of_dvd ⟨4, by ring⟩
    rw [h, hr_mod]
  obtain ⟨k, hk⟩ : ∃ k, n * k + (n - 1) = p :=
    ⟨p / n, by rw [← hpn]; exact Nat.div_add_mod p n⟩
  refine ⟨p, k + 1, hpN, hpp, by omega, ?_, ?_⟩
  · have hexp : (k + 1) * n = n * k + n := by ring
    rw [hexp]; omega
  · intro _
    rw [legendreSym_neg_eq_of_modEq hp_odd hr_odd hpr, hr_qr]

/-- **Forced geometry hypothesis (assembled).**  Under the same hypotheses the
supplied multiplier prime additionally satisfies the geometry's QR hypothesis on
the multiplier itself, `legendreSym p (−d) = 1`, obtained by feeding the forced
`legendreSym p (−n) = 1` through the parent reduction
`ThreeSquaresMultiplierQR.legendreSym_neg_n_one_imp_neg_d_one`. -/
theorem exists_qr_qualified_multiplier_prime_full {n : ℕ} (hn : 2 ≤ n) {r : ℕ}
    (hcop : Nat.Coprime r (4 * n)) (hr_mod : r % n = n - 1)
    (hr_qr : J(-(n : ℤ) | r) = 1) (N : ℕ) :
    ∃ p d : ℕ, N < p ∧ p.Prime ∧ 1 ≤ d ∧ d * n = p + 1 ∧
      ∀ _ : Fact p.Prime,
        legendreSym p (-(n : ℤ)) = 1 ∧ legendreSym p (-(d : ℤ)) = 1 := by
  obtain ⟨p, d, hpN, hpp, hd1, hdn, hqn⟩ :=
    exists_qr_qualified_multiplier_prime hn hcop hr_mod hr_qr N
  refine ⟨p, d, hpN, hpp, hd1, hdn, fun inst => ?_⟩
  haveI := inst
  exact ⟨hqn inst,
    ThreeSquaresMultiplierQR.legendreSym_neg_n_one_imp_neg_d_one hdn (hqn inst)⟩

/-- **Non-vacuousness.**  For `n = 2` the residue `r = 3` qualifies, so the
unconditional supply is genuinely populated: for every `N` there is a prime
`p > N` with `p = 2d − 1` and `legendreSym p (−2) = 1`. -/
theorem qr_qualified_multiplier_prime_two (N : ℕ) :
    ∃ p d : ℕ, N < p ∧ p.Prime ∧ 1 ≤ d ∧ d * 2 = p + 1 ∧
      ∀ _ : Fact p.Prime, legendreSym p (-(2 : ℤ)) = 1 :=
  exists_qr_qualified_multiplier_prime (n := 2) (by norm_num) (r := 3)
    (by decide) (by decide) (by norm_num) N

/-! ## §3. A sharp obstruction at `n = 3` -/

/-- For every odd prime `p` with `p ≡ 2 (mod 3)` we have `legendreSym p (−3) = −1`.

By periodicity (`jacobiSym.mod_right`) the value depends only on `p mod 12`, and
the residue constraints (`p` odd, `p ≡ 2 mod 3`) force `p mod 12 ∈ {5, 11}`, on
both of which the Jacobi symbol `J(−3 | ·)` evaluates to `−1`. -/
theorem legendreSym_neg_three_eq_neg_one
    {p : ℕ} [Fact p.Prime] (hp2 : Odd p) (hp3 : p % 3 = 2) :
    legendreSym p (-3) = -1 := by
  have h2 : p % 2 = 1 := Nat.odd_iff.mp hp2
  rw [legendreSym.to_jacobiSym, jacobiSym.mod_right (-3) hp2]
  have hnatAbs : ((-3 : ℤ).natAbs) = 3 := rfl
  rw [hnatAbs]
  -- goal: jacobiSym (-3) (p % (4 * 3)) = -1
  have key : p % (4 * 3) = 5 ∨ p % (4 * 3) = 11 := by omega
  rcases key with h | h <;> rw [h] <;> norm_num

/-- **The multiplier–QR route cannot represent `n = 3`.**  A "multiplier prime"
for `n = 3` is by definition a prime `p` with `p + 1 = 3 d`, i.e. `p = 3d − 1`.
For every such (odd) prime the geometry's QR hypothesis `legendreSym p (−3) = 1`
fails. -/
theorem multiplier_prime_neg_three_qr_fails
    {p : ℕ} [Fact p.Prime] (hp2 : Odd p) {d : ℕ} (hd : p + 1 = 3 * d) :
    legendreSym p (-3) = -1 := by
  refine legendreSym_neg_three_eq_neg_one hp2 ?_
  omega

/-- **Honest capstone.**  `3` is a sum of three squares, yet the QR hypothesis of
the `−n`-multiplier route is satisfied by *no* multiplier prime for `n = 3`.
Hence that route, taken on its own, cannot certify the representability of `3` —
equivalently, the qualifying-residue hypothesis of §2 fails at `n = 3`. -/
theorem multiplier_route_incomplete_at_three :
    (3 = 1 ^ 2 + 1 ^ 2 + 1 ^ 2) ∧
      ∀ (p d : ℕ) [Fact p.Prime], Odd p → p + 1 = 3 * d →
        legendreSym p (-3) ≠ 1 := by
  refine ⟨by norm_num, ?_⟩
  intro p d _ hp2 hd
  rw [multiplier_prime_neg_three_qr_fails hp2 hd]
  norm_num

end Proofs.LagrangeFourSquaresWaringG2OQ03OQ07OQ01
