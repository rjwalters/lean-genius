import Mathlib.NumberTheory.ZetaValues
import Mathlib.NumberTheory.Real.Irrational
import Proofs.PiTranscendental

/-
# Every even zeta value ζ(2n) is irrational — and the odd case ζ(2n+1) is open

## What This Proves

For every `n ≥ 1` the even-argument zeta value

  `ζ(2n) = ∑' k, 1 / k^(2n)`

is **irrational**.  This is the sharp arithmetic contrast to the parent Basel
open question about `ζ(7)` / `ζ(2n+1)`:

  * **Even values** `ζ(2), ζ(4), ζ(6), …` are *all* irrational — proved here.
  * **Odd values** `ζ(5), ζ(7), ζ(9), …` : irrationality is a **genuinely open
    problem**.  Apéry (1979) proved `ζ(3)` irrational (the only individual odd
    value known), and Ball–Rivoal (2001) showed infinitely many `ζ(2n+1)` are
    irrational, but no single `ζ(2n+1)` with `n ≥ 2` is known to be irrational.
    None of this is in Mathlib.

## Why this is `axiomatized`, not `verified`

Euler's formula (`hasSum_zeta_nat`) gives `ζ(2n) = qₙ · π^(2n)` with `qₙ ∈ ℚ`,
so `ζ(2n)` is irrational **iff** `π^(2n)` is.  Irrationality is *not* closed
under powers (`√2` is irrational, its square is not), so `irrational_pi` alone
is insufficient: we genuinely need the **transcendence of π**, and Mathlib does
not (yet) contain a complete Lindemann–Weierstrass development.  This file
therefore routes through the repository's `axiom hermite_lindemann`
(via `Proofs.PiTranscendental.pi_transcendental_over_rationals`).  The single
assumption is exactly that axiom; everything else is machine-checked.

The nonzero-ness of the rational coefficient `qₙ` is obtained *for free* from
positivity of the series (`ζ(2n) > 0`), so no Bernoulli-number vanishing lemma
is needed.

## Approach

  1. `Transcendental ℚ π`  (from `pi_transcendental_over_rationals`, i.e.
     `hermite_lindemann`).
  2. `Transcendental.pow` ⟹ `Transcendental ℚ (π^m)` for `m ≥ 1`, hence
     `Irrational (π^m)` via `Transcendental.irrational`.
  3. `hasSum_zeta_nat` ⟹ `ζ(2n) = ↑qₙ · π^(2n)`; positivity forces `qₙ ≠ 0`;
     `Irrational.ratCast_mul` finishes.
-/

open Real

namespace BaselProblemOQ01OQ02

/-- **Euler's structure theorem for even zeta values — axiom-free.**  Every even zeta value is a
    *nonzero rational* multiple of `π^(2n)`:  `∑' k, 1/k^(2n) = qₙ · π^(2n)` with `qₙ ∈ ℚ∖{0}`.

    This is the axiom-free skeleton beneath the irrationality/transcendence results below: it uses
    only Mathlib's Bernoulli closed form (`hasSum_zeta_nat`) together with strict positivity of the
    series — **no** `hermite_lindemann`.  The single remaining step, from "rational multiple of
    `π^(2n)`" to "irrational", is *exactly* where transcendence of π enters.  So this lemma marks
    the sharp boundary between what is unconditional (the rational-multiple structure) and what
    requires the deep transcendence input (irrationality of the value itself). -/
theorem zeta_even_eq_rat_mul_pi_pow (n : ℕ) (hn : 0 < n) :
    ∃ q : ℚ, q ≠ 0 ∧ (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) = (q : ℝ) * π ^ (2 * n) := by
  have hS := hasSum_zeta_nat (k := n) hn.ne'
  obtain ⟨q, hq⟩ :
      ∃ q : ℚ, (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) = (q : ℝ) * π ^ (2 * n) := by
    refine ⟨(-1) ^ (n + 1) * 2 ^ (2 * n - 1) * bernoulli (2 * n) / (2 * n).factorial, ?_⟩
    rw [hS.tsum_eq]; push_cast; ring
  -- The series is strictly positive (its k = 1 term is 1), forcing q ≠ 0.
  have hpos : 0 < ∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n) :=
    hS.summable.tsum_pos (fun m => by positivity) 1 (by norm_num)
  have hqne : q ≠ 0 := by
    intro h0; rw [hq, h0] at hpos; simp at hpos
  exact ⟨q, hqne, hq⟩

/-- **Powers of π are irrational** (`m ≥ 1`).

    Mathlib provides `irrational_pi` but nothing about `π^m` for `m ≥ 2`
    (irrationality does not lift through powers).  This follows from the
    *transcendence* of π: if `π^m` were algebraic over ℚ then so would π be
    (compose the witnessing polynomial with `Xᵐ`), contradicting
    `pi_transcendental_over_rationals`.

    **Assumption:** `hermite_lindemann` (Lindemann–Weierstrass), via
    `Proofs.PiTranscendental`. -/
theorem pi_pow_irrational (m : ℕ) (hm : 0 < m) : Irrational (π ^ m) :=
  (pi_transcendental_over_rationals.pow hm).irrational

/-- **Every even zeta value is irrational.**

    For `n ≥ 1`, `ζ(2n) = ∑' k, 1/k^(2n)` is irrational.  Concretely
    `ζ(2) = π²/6`, `ζ(4) = π⁴/90`, `ζ(6) = π⁶/945`, … are all irrational.

    This is the arithmetic counterpoint to the *open* odd case: whether any
    single `ζ(2n+1)` with `n ≥ 2` (e.g. `ζ(7)`) is irrational is unknown.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_irrational (n : ℕ) (hn : 0 < n) :
    Irrational (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) := by
  -- Euler's axiom-free structure: the sum is a nonzero-rational multiple of π^(2n).
  obtain ⟨q, hqne, hq⟩ := zeta_even_eq_rat_mul_pi_pow n hn
  rw [hq]
  -- π^(2n) is irrational; scaling by the nonzero rational q keeps it irrational.
  exact (pi_pow_irrational (2 * n) (by omega)).ratCast_mul hqne

/-- **ζ(2) = ∑' k, 1/k² is irrational** (the classical Basel value). -/
theorem zeta_two_irrational : Irrational (∑' k : ℕ, 1 / (k : ℝ) ^ 2) := by
  have := zeta_even_irrational 1 one_pos
  simpa using this

/-- **ζ(4) = ∑' k, 1/k⁴ is irrational.** -/
theorem zeta_four_irrational : Irrational (∑' k : ℕ, 1 / (k : ℝ) ^ 4) := by
  have := zeta_even_irrational 2 (by norm_num)
  simpa using this

/-- **ζ(6) = ∑' k, 1/k⁶ is irrational.** -/
theorem zeta_six_irrational : Irrational (∑' k : ℕ, 1 / (k : ℝ) ^ 6) := by
  have := zeta_even_irrational 3 (by norm_num)
  simpa using this

/-- **Every even zeta value is transcendental over ℚ** — strictly stronger than
    irrationality.

    Since `ζ(2n) = qₙ · π^(2n)` with `qₙ ∈ ℚ∖{0}` and `π^(2n)` is transcendental
    over ℚ (transcendence of π, `pi_transcendental_over_rationals`, lifted through
    powers by `Transcendental.pow`), scaling by the nonzero rational `qₙ`
    preserves transcendence: an algebraic `qₙ·π^(2n)` would make
    `π^(2n) = qₙ⁻¹·(qₙ·π^(2n))` algebraic, contradicting transcendence of `π^(2n)`.
    Transcendence over ℚ implies irrationality (`Transcendental.irrational`), so
    this refines `zeta_even_irrational`.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_transcendental (n : ℕ) (hn : 0 < n) :
    Transcendental ℚ (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) := by
  -- Euler's axiom-free structure: the sum is a nonzero-rational multiple of π^(2n).
  obtain ⟨q, hqne, hq⟩ := zeta_even_eq_rat_mul_pi_pow n hn
  have hqne' : (q : ℝ) ≠ 0 := by exact_mod_cast hqne
  -- π^(2n) is transcendental over ℚ.
  have hpi : Transcendental ℚ (π ^ (2 * n)) :=
    pi_transcendental_over_rationals.pow (by omega)
  rw [hq]
  -- Transcendence is preserved under scaling by the nonzero rational q:
  -- if q·π^(2n) were algebraic then π^(2n) = q⁻¹·(q·π^(2n)) would be too.
  intro halg
  apply hpi
  have hqinv : IsAlgebraic ℚ ((q⁻¹ : ℚ) : ℝ) := isAlgebraic_algebraMap (q⁻¹ : ℚ)
  have hmul := halg.mul hqinv
  rwa [show (q : ℝ) * π ^ (2 * n) * ((q⁻¹ : ℚ) : ℝ) = π ^ (2 * n) from by
    push_cast; rw [mul_right_comm, mul_inv_cancel₀ hqne', one_mul]] at hmul

/-- **ζ(2) = ∑' k, 1/k² is transcendental over ℚ** (hence irrational). -/
theorem zeta_two_transcendental : Transcendental ℚ (∑' k : ℕ, 1 / (k : ℝ) ^ 2) := by
  have := zeta_even_transcendental 1 one_pos
  simpa using this

/-- **Scaling by a nonzero rational preserves transcendence over ℚ.**

    If `x` is transcendental over ℚ and `q ∈ ℚ∖{0}`, then `q·x` is transcendental:
    were `q·x` algebraic, so would be `x = q⁻¹·(q·x)` (product of algebraics),
    contradicting transcendence of `x`.  This is the reusable engine behind
    `zeta_even_transcendental` and the ratio result below. -/
theorem transcendental_ratCast_mul {x : ℝ} (hx : Transcendental ℚ x) {q : ℚ}
    (hq : q ≠ 0) : Transcendental ℚ ((q : ℝ) * x) := by
  intro halg
  apply hx
  have hqne' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hqinv : IsAlgebraic ℚ ((q⁻¹ : ℚ) : ℝ) := isAlgebraic_algebraMap (q⁻¹ : ℚ)
  have hmul := halg.mul hqinv
  rwa [show (q : ℝ) * x * ((q⁻¹ : ℚ) : ℝ) = x from by
    push_cast; rw [mul_right_comm, mul_inv_cancel₀ hqne', one_mul]] at hmul

/-- **Structural ratio identity for even zeta values — axiom-free.**  For `m < n` the
    quotient of two even zeta values is a *nonzero-rational* multiple of a *positive* even
    power of π:
    `ζ(2n)/ζ(2m) = (qₙ · π^(2n)) / (qₘ · π^(2m)) = (qₙ/qₘ) · π^(2(n−m))`,  with `2(n−m) ≥ 2`.

    This is the unconditional skeleton beneath `zeta_even_ratio_transcendental` — it uses
    only Euler's closed form (`zeta_even_eq_rat_mul_pi_pow`), **no** `hermite_lindemann`.
    Mathematically it already records the key structural fact that the even zeta values are
    *multiplicatively π-power-incommensurable over ℚ*: their quotient can never be a mere
    rational number, because it always carries a leftover nonzero even power of π.
    Transcendence enters only afterwards, exactly when `π^(2(n−m))` is declared transcendental
    (mirroring how `zeta_even_eq_rat_mul_pi_pow` isolates the axiom for the single-value case). -/
theorem zeta_even_ratio_eq_rat_mul_pi_pow (n m : ℕ) (hm : 0 < m) (hmn : m < n) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) / (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m))
        = (q : ℝ) * π ^ (2 * n - 2 * m) := by
  obtain ⟨qn, hqn, hqn_eq⟩ := zeta_even_eq_rat_mul_pi_pow n (by omega)
  obtain ⟨qm, hqm, hqm_eq⟩ := zeta_even_eq_rat_mul_pi_pow m hm
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hle : 2 * m ≤ 2 * n := by omega
  refine ⟨qn / qm, div_ne_zero hqn hqm, ?_⟩
  rw [hqn_eq, hqm_eq, mul_div_mul_comm, pow_sub₀ π hπ hle]
  push_cast; ring

/-- **Ratios of distinct even zeta values are transcendental over ℚ.**

    For `m < n`,
    `ζ(2n)/ζ(2m) = (qₙ · π^(2n)) / (qₘ · π^(2m)) = (qₙ/qₘ) · π^(2(n−m))`
    is a nonzero rational multiple of a *positive* even power of π, hence
    transcendental over ℚ (`transcendental_ratCast_mul` applied to
    `Transcendental.pow` of `π`).  Concretely `ζ(4)/ζ(2) = π²/15`,
    `ζ(6)/ζ(4) = 2π²/21`, … are all transcendental.

    Structurally this says the even zeta values are *multiplicatively
    π-power-incommensurable over ℚ*: no two distinct ones are related by a mere
    rational factor — their quotient always carries a leftover nonzero even power
    of π.  (For `n < m` the ratio is the reciprocal, so the same conclusion holds
    by symmetry.)  The nonzero-rational-multiple-of-π-power structure is the
    axiom-free `zeta_even_ratio_eq_rat_mul_pi_pow`; only the final step uses the axiom.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_ratio_transcendental (n m : ℕ) (hm : 0 < m) (hmn : m < n) :
    Transcendental ℚ
      ((∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) / (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m))) := by
  obtain ⟨q, hq, hratio⟩ := zeta_even_ratio_eq_rat_mul_pi_pow n m hm hmn
  rw [hratio]
  exact transcendental_ratCast_mul (pi_transcendental_over_rationals.pow (by omega)) hq

/-- **ζ(4)/ζ(2) = π²/15 is transcendental over ℚ** — a concrete distinct-index ratio. -/
theorem zeta_four_div_zeta_two_transcendental :
    Transcendental ℚ ((∑' k : ℕ, 1 / (k : ℝ) ^ 4) / (∑' k : ℕ, 1 / (k : ℝ) ^ 2)) := by
  have := zeta_even_ratio_transcendental 2 1 one_pos (by norm_num)
  simpa using this

/-- **Structural product identity for even zeta values — axiom-free.**  The product of two
    even zeta values is a *nonzero-rational* multiple of a *positive* even power of π:
    `ζ(2n)·ζ(2m) = (qₙqₘ)·π^(2n+2m)`.  Companion to `zeta_even_ratio_eq_rat_mul_pi_pow`: the
    quotient strips π-powers, the product adds them, and both stay inside `ℚ·π^(even)`.  Uses
    only Euler's closed form (`zeta_even_eq_rat_mul_pi_pow`), **no** `hermite_lindemann`. -/
theorem zeta_even_product_eq_rat_mul_pi_pow (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) * (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m))
        = (q : ℝ) * π ^ (2 * n + 2 * m) := by
  obtain ⟨qn, hqn, hqn_eq⟩ := zeta_even_eq_rat_mul_pi_pow n hn
  obtain ⟨qm, hqm, hqm_eq⟩ := zeta_even_eq_rat_mul_pi_pow m hm
  refine ⟨qn * qm, mul_ne_zero hqn hqm, ?_⟩
  rw [hqn_eq, hqm_eq, pow_add]
  push_cast; ring

/-- **Products of even zeta values are transcendental over ℚ.**

    For `n, m ≥ 1`, `ζ(2n)·ζ(2m) = (qₙqₘ)·π^(2n+2m)` is a nonzero rational multiple of a
    positive even power of π, hence transcendental over ℚ.  Concretely `ζ(2)·ζ(4) = π⁶/540`,
    etc.  The multiplicative companion of `zeta_even_ratio_transcendental`: the even zeta
    values are closed under multiplication into the transcendental class `ℚ∖{0} · π^(even>0)`.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_product_transcendental (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    Transcendental ℚ
      ((∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) * (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m))) := by
  obtain ⟨q, hq, hprod⟩ := zeta_even_product_eq_rat_mul_pi_pow n m hn hm
  rw [hprod]
  exact transcendental_ratCast_mul (pi_transcendental_over_rationals.pow (by omega)) hq

/-- **Normalization returns to ℚ — the sharp axiom-free contrast.**  Dividing `ζ(2n)` by the
    *matching* power `π^(2n)` lands back in the rationals: `ζ(2n)/π^(2n) = qₙ ∈ ℚ`.  This pins
    down exactly which factor carries the transcendence — it is precisely the `π^(2n)` and
    nothing else.  Together with `zeta_even_transcendental` (the value itself is transcendental)
    it isolates the transcendental content to a single π-power.  Uses only Euler's closed form,
    **no** `hermite_lindemann`. -/
theorem zeta_even_div_pi_pow_rational (n : ℕ) (hn : 0 < n) :
    ∃ q : ℚ, (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) / π ^ (2 * n) = (q : ℝ) := by
  obtain ⟨q, _, hq⟩ := zeta_even_eq_rat_mul_pi_pow n hn
  exact ⟨q, by rw [hq, mul_div_assoc, div_self (pow_ne_zero (2 * n) Real.pi_ne_zero), mul_one]⟩

/-- **Structural power identity for even zeta values — axiom-free.**  Every positive integer
    power of an even zeta value is again a *nonzero-rational* multiple of a *positive* even power
    of π:  `ζ(2n)^j = (qₙ · π^(2n))^j = qₙ^j · π^(2nj)`,  with `2nj ≥ 2`.

    The `j`-fold companion of `zeta_even_product_eq_rat_mul_pi_pow` (which multiplies two possibly
    distinct values): the class `ℚ∖{0} · π^(even>0)` housing the even zeta values is closed under
    taking powers, not merely pairwise products.  Uses only Euler's closed form
    (`zeta_even_eq_rat_mul_pi_pow`), **no** `hermite_lindemann`. -/
theorem zeta_even_pow_eq_rat_mul_pi_pow (n j : ℕ) (hn : 0 < n) (hj : 0 < j) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) ^ j = (q : ℝ) * π ^ (2 * n * j) := by
  obtain ⟨qn, hqn, hqn_eq⟩ := zeta_even_eq_rat_mul_pi_pow n hn
  refine ⟨qn ^ j, pow_ne_zero j hqn, ?_⟩
  rw [hqn_eq, mul_pow, ← pow_mul]
  push_cast; ring

/-- **Positive integer powers of even zeta values are transcendental over ℚ.**

    For `n, j ≥ 1`, `ζ(2n)^j = qₙ^j · π^(2nj)` is a nonzero rational multiple of a *positive*
    even power of π, hence transcendental over ℚ (`transcendental_ratCast_mul` applied to
    `Transcendental.pow` of `π`).  Concretely `ζ(2)² = π⁴/36`, `ζ(2)³ = π⁶/216`, … are all
    transcendental.  The power companion of `zeta_even_product_transcendental`.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_pow_transcendental (n j : ℕ) (hn : 0 < n) (hj : 0 < j) :
    Transcendental ℚ ((∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) ^ j) := by
  obtain ⟨q, hq, hpow⟩ := zeta_even_pow_eq_rat_mul_pi_pow n j hn hj
  rw [hpow]
  exact transcendental_ratCast_mul
    (pi_transcendental_over_rationals.pow (Nat.mul_pos (Nat.mul_pos (by norm_num) hn) hj)) hq

/-- **ζ(2)² = (∑' k, 1/k²)² is transcendental over ℚ** — a concrete power instance
    (`ζ(2)² = π⁴/36`). -/
theorem zeta_two_sq_transcendental :
    Transcendental ℚ ((∑' k : ℕ, 1 / (k : ℝ) ^ 2) ^ 2) := by
  have := zeta_even_pow_transcendental 1 2 one_pos (by norm_num)
  simpa using this

/-- **Dividing a transcendental by a nonzero rational preserves transcendence over ℚ.**

    The division companion of `transcendental_ratCast_mul`: since `x / q = q⁻¹ · x` and
    `q⁻¹ ≠ 0`, transcendence of `x` transfers to `x / q`.  Reusable engine for the
    normalised even-zeta values (e.g. `ζ(2n)/2`, `ζ(2n)/qₙ`). -/
theorem transcendental_div_ratCast {x : ℝ} (hx : Transcendental ℚ x) {q : ℚ}
    (hq : q ≠ 0) : Transcendental ℚ (x / (q : ℝ)) := by
  have hxq : x / (q : ℝ) = ((q⁻¹ : ℚ) : ℝ) * x := by push_cast; ring
  rw [hxq]
  exact transcendental_ratCast_mul hx (inv_ne_zero hq)

/-- **The class `ℚ∖{0} · π^(2n)` is closed under scaling by nonzero rationals — axiom-free.**
    For any `c ∈ ℚ∖{0}`, `c · ζ(2n) = (c·qₙ) · π^(2n)` is again a nonzero-rational multiple
    of the same positive even power of π.  Together with `zeta_even_product_eq_rat_mul_pi_pow`
    (products) and `zeta_even_pow_eq_rat_mul_pi_pow` (powers) this completes the algebraic
    picture: the even zeta values live in a set closed under ℚ*-scaling, products, and powers.
    Uses only Euler's closed form (`zeta_even_eq_rat_mul_pi_pow`), **no** `hermite_lindemann`. -/
theorem zeta_even_ratCast_mul_eq_rat_mul_pi_pow (n : ℕ) (hn : 0 < n) (c : ℚ) (hc : c ≠ 0) :
    ∃ q : ℚ, q ≠ 0 ∧
      (c : ℝ) * (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) = (q : ℝ) * π ^ (2 * n) := by
  obtain ⟨qn, hqn, hq⟩ := zeta_even_eq_rat_mul_pi_pow n hn
  refine ⟨c * qn, mul_ne_zero hc hqn, ?_⟩
  rw [hq]; push_cast; ring

/-- **Nonzero-rational multiples of even zeta values are transcendental over ℚ.**
    For `n ≥ 1` and `c ∈ ℚ∖{0}`, `c · ζ(2n)` is transcendental — the transcendence-level
    statement of the ℚ*-scaling closure, immediate from `zeta_even_transcendental` and the
    scaling engine `transcendental_ratCast_mul`.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_ratCast_mul_transcendental (n : ℕ) (hn : 0 < n) (c : ℚ) (hc : c ≠ 0) :
    Transcendental ℚ ((c : ℝ) * (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n))) :=
  transcendental_ratCast_mul (zeta_even_transcendental n hn) hc

/-- **General finite-product structure for even zeta values — axiom-free.**  For an arbitrary
    finite family of positive indices `(f i)_{i ∈ s}`, the product of the even zeta values
    `ζ(2·f i)` is a *single* nonzero-rational multiple of a *single* power of π, whose exponent is
    the doubled index sum:
    `∏_{i∈s} ζ(2 f i) = (∏_{i∈s} q_{f i}) · π^(2 ∑_{i∈s} f i)`.
    This is the `Finset` generalisation of the pairwise `zeta_even_product_eq_rat_mul_pi_pow`:
    the class `ℚ∖{0} · π^(even)` housing the even zeta values is closed under *all* finite
    products, not merely two factors.  Proved by induction on `s`, feeding each factor through
    Euler's closed form and collecting the π-powers with `pow_add`.  Uses only
    `zeta_even_eq_rat_mul_pi_pow`, **no** `hermite_lindemann`. -/
theorem zeta_even_finset_prod_eq_rat_mul_pi_pow {ι : Type*} (f : ι → ℕ) (s : Finset ι)
    (hf : ∀ i ∈ s, 0 < f i) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∏ i ∈ s, ∑' k : ℕ, 1 / (k : ℝ) ^ (2 * f i))
        = (q : ℝ) * π ^ (2 * ∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨q, hq, hqeq⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      obtain ⟨qa, hqa, hqaeq⟩ :=
        zeta_even_eq_rat_mul_pi_pow (f a) (hf a (Finset.mem_insert_self a s))
      refine ⟨qa * q, mul_ne_zero hqa hq, ?_⟩
      rw [Finset.prod_insert ha, Finset.sum_insert ha, hqeq, hqaeq, mul_add, pow_add]
      push_cast; ring

/-- **Arbitrary finite products of even zeta values are transcendental over ℚ.**

    For a nonempty finite family of positive indices, `∏_{i∈s} ζ(2 f i)` is a nonzero rational
    multiple of a *positive* even power of π (`2 ∑ f i ≥ 2`), hence transcendental over ℚ.  The
    `Finset` companion of `zeta_even_product_transcendental`: no finite product of even zeta
    values can be algebraic.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_finset_prod_transcendental {ι : Type*} (f : ι → ℕ) (s : Finset ι)
    (hs : s.Nonempty) (hf : ∀ i ∈ s, 0 < f i) :
    Transcendental ℚ (∏ i ∈ s, ∑' k : ℕ, 1 / (k : ℝ) ^ (2 * f i)) := by
  obtain ⟨q, hq, heq⟩ := zeta_even_finset_prod_eq_rat_mul_pi_pow f s hf
  rw [heq]
  refine transcendental_ratCast_mul (pi_transcendental_over_rationals.pow ?_) hq
  have : 0 < ∑ i ∈ s, f i := Finset.sum_pos hf hs
  omega

/-- **Weighted finite-product structure for even zeta values — axiom-free.**  For arbitrary
    finite families of positive indices `(f i)` and positive exponents `(g i)` over `s`, the
    weighted product `∏_{i∈s} ζ(2 f i)^(g i)` is a *single* nonzero-rational multiple of a
    *single* power of π, whose exponent is the doubled weighted sum:
    `∏_{i∈s} ζ(2 f i)^(g i) = (∏_{i∈s} q_{f i}^{g i}) · π^(2 ∑_{i∈s} f i · g i)`.
    This is the common generalisation of *both* `zeta_even_pow_eq_rat_mul_pi_pow` (a single index
    raised to a power — the case `s = {i}`) and `zeta_even_finset_prod_eq_rat_mul_pi_pow` (a product
    with all exponents `1`): the class `ℚ∖{0} · π^(even)` is closed under arbitrary finite
    products of *powers*, i.e. under every monomial in the even zeta values.  Proved by induction
    on `s`, feeding each factor through the power identity `zeta_even_pow_eq_rat_mul_pi_pow` and
    collecting the π-powers with `pow_add`.  Uses only Euler's closed form, **no**
    `hermite_lindemann`. -/
theorem zeta_even_weighted_prod_eq_rat_mul_pi_pow {ι : Type*} (f g : ι → ℕ) (s : Finset ι)
    (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) :
    ∃ q : ℚ, q ≠ 0 ∧
      (∏ i ∈ s, (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * f i)) ^ g i)
        = (q : ℝ) * π ^ (2 * ∑ i ∈ s, f i * g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨q, hq, hqeq⟩ :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
           (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      obtain ⟨qa, hqa, hqaeq⟩ :=
        zeta_even_pow_eq_rat_mul_pi_pow (f a) (g a)
          (hf a (Finset.mem_insert_self a s)) (hg a (Finset.mem_insert_self a s))
      refine ⟨qa * q, mul_ne_zero hqa hq, ?_⟩
      rw [Finset.prod_insert ha, Finset.sum_insert ha, hqeq, hqaeq, mul_add, pow_add]
      push_cast; ring

/-- **Arbitrary finite products of powers of even zeta values are transcendental over ℚ.**

    For nonempty finite families of positive indices `(f i)` and positive exponents `(g i)`, the
    monomial `∏_{i∈s} ζ(2 f i)^(g i)` is a nonzero rational multiple of a *positive* even power of π
    (`2 ∑ f i · g i ≥ 2`), hence transcendental over ℚ.  The common companion of
    `zeta_even_pow_transcendental` and `zeta_even_finset_prod_transcendental`: no finite monomial in
    the even zeta values can be algebraic.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_weighted_prod_transcendental {ι : Type*} (f g : ι → ℕ) (s : Finset ι)
    (hs : s.Nonempty) (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) :
    Transcendental ℚ (∏ i ∈ s, (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * f i)) ^ g i) := by
  obtain ⟨q, hq, heq⟩ := zeta_even_weighted_prod_eq_rat_mul_pi_pow f g s hf hg
  rw [heq]
  refine transcendental_ratCast_mul (pi_transcendental_over_rationals.pow ?_) hq
  have hpos : 0 < ∑ i ∈ s, f i * g i :=
    Finset.sum_pos (fun i hi => Nat.mul_pos (hf i hi) (hg i hi)) hs
  omega

open Polynomial in
/-- **Master transcendence engine: every nonconstant rational polynomial of π is transcendental.**

    If `f ∈ ℚ[X]` has `natDegree f ≠ 0` (i.e. `f` is nonconstant) then the value `f(π)` is
    transcendental over ℚ.  This single lemma *unifies* every transcendence result above: each of
    `zeta_even_transcendental` (`f = C qₙ · X^(2n)`), `zeta_even_product_transcendental`,
    `zeta_even_pow_transcendental`, and the ratio results is merely the special case of a *monomial*
    `f`.  Its genuinely new payoff is **additive**: a `ℚ`-linear combination of even zeta values —
    which leaves the multiplicative class `ℚ∖{0}·π^(even)` — is *still* transcendental, because it
    is a nonconstant polynomial in π (see `zeta_even_add_transcendental` below).

    Proof: `f` nonconstant ⟹ `f ≠ 0` ⟹ `leadingCoeff f ≠ 0`, which over the field ℚ lies in the
    non-zero-divisors; `Transcendental.aeval` then lifts `Transcendental ℚ π`
    (`pi_transcendental_over_rationals`) to `aeval π f`.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem transcendental_aeval_pi (f : ℚ[X]) (hf : f.natDegree ≠ 0) :
    Transcendental ℚ (Polynomial.aeval π f) := by
  have hfne : f ≠ 0 := fun h => hf (by rw [h, natDegree_zero])
  exact pi_transcendental_over_rationals.aeval f hf
    (mem_nonZeroDivisors_of_ne_zero (leadingCoeff_ne_zero.mpr hfne))

open Polynomial in
/-- **Sums of two distinct even zeta values are transcendental — the additive frontier.**

    For `n ≠ m` (both `≥ 1`), `ζ(2n) + ζ(2m)` is transcendental over ℚ.  This is a *new* kind of
    result: the multiplicative structure theorems above (`zeta_even_product_transcendental`,
    `zeta_even_pow_transcendental`, …) all stay inside the class `ℚ∖{0}·π^(even>0)`, but a sum of
    two *distinct* even zeta values leaves that class — `qₙ·π^(2n) + qₘ·π^(2m)` is a genuine
    *two-term* polynomial in π, not a single monomial `q·π^(2k)`.  Transcendence nevertheless
    survives, because this is a nonconstant polynomial in the transcendental π
    (`transcendental_aeval_pi`); the two exponents `2n ≠ 2m` cannot cancel and neither leading
    coefficient vanishes, so the polynomial `C qₙ·X^(2n) + C qₘ·X^(2m)` has degree `max(2n,2m) ≥ 2`.
    Concretely `ζ(2)+ζ(4) = π²/6 + π⁴/90` and `ζ(2)+ζ(6) = π²/6 + π⁶/945` are transcendental.

    **Assumption:** `hermite_lindemann` (transcendence of π). -/
theorem zeta_even_add_transcendental (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (hnm : n ≠ m) :
    Transcendental ℚ
      ((∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) + (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m))) := by
  obtain ⟨qn, hqn, hqn_eq⟩ := zeta_even_eq_rat_mul_pi_pow n hn
  obtain ⟨qm, hqm, hqm_eq⟩ := zeta_even_eq_rat_mul_pi_pow m hm
  -- Express the sum as a two-term polynomial in π.
  have hsum : (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * n)) + (∑' k : ℕ, 1 / (k : ℝ) ^ (2 * m))
      = Polynomial.aeval π (C qn * X ^ (2 * n) + C qm * X ^ (2 * m)) := by
    rw [hqn_eq, hqm_eq]
    simp [map_add, map_mul, aeval_C, map_pow, aeval_X]
  rw [hsum]
  -- The polynomial is nonconstant: distinct exponents 2n ≠ 2m, both coefficients nonzero.
  refine transcendental_aeval_pi _ ?_
  rcases Nat.lt_or_ge (2 * n) (2 * m) with h | h
  · rw [natDegree_add_eq_right_of_natDegree_lt
        (by rw [natDegree_C_mul_X_pow _ _ hqn, natDegree_C_mul_X_pow _ _ hqm]; exact h),
        natDegree_C_mul_X_pow _ _ hqm]
    omega
  · have h' : 2 * m < 2 * n := by omega
    rw [natDegree_add_eq_left_of_natDegree_lt
        (by rw [natDegree_C_mul_X_pow _ _ hqn, natDegree_C_mul_X_pow _ _ hqm]; exact h'),
        natDegree_C_mul_X_pow _ _ hqn]
    omega

/-- **ζ(2) + ζ(4) = π²/6 + π⁴/90 is transcendental over ℚ** — a concrete two-term sum leaving the
    multiplicative class `ℚ∖{0}·π^(even)` yet remaining transcendental. -/
theorem zeta_two_add_zeta_four_transcendental :
    Transcendental ℚ ((∑' k : ℕ, 1 / (k : ℝ) ^ 2) + (∑' k : ℕ, 1 / (k : ℝ) ^ 4)) := by
  have := zeta_even_add_transcendental 1 2 one_pos (by norm_num) (by norm_num)
  simpa using this

/-!
## The open odd case (documentation only)

We deliberately state **no** irrationality theorem for `ζ(2n+1)`: that is the
content of the parent open question and is beyond current mathematics for every
individual value past `ζ(3)`.  The even-case result above is exactly the sharp
boundary that is provable today.
-/

end BaselProblemOQ01OQ02
