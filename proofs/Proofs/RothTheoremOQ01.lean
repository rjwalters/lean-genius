import Mathlib.Combinatorics.Additive.Corner.Roth
import Mathlib.Combinatorics.Additive.AP.Three.Behrend
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Proofs.RothTheoremOQ02

/-!
# Roth's Theorem — Bourgain's 1999 Quantitative Bound (OQ-01)

## What This Provides

A typed Lean target for Bourgain's 1999 quantitative refinement of Roth's
theorem on three-term arithmetic progressions:

  ∃ C > 0, ∀ N ≥ 3, rothNumberNat N ≤ C · N · (log log N / log N)^(1/2)

The bound is named `rothNumberNat_bourgain`.  Unlike the sibling file
`RothTheoremOQ02.lean` — which *axiomatizes* the Bloom–Sisask bound — this file
**no longer declares a Bourgain axiom**: `rothNumberNat_bourgain` is now a
**theorem, derived from the Bloom–Sisask axiom** of OQ-02, because Bloom–Sisask
(`N / (log N)^{1+c}`) decays strictly faster than the Bourgain bound and so
implies it.  The earlier version of this file carried a separate
`axiom rothNumberNat_bourgain`; that axiom was redundant (its own docstring noted
"OQ-01 is implied by OQ-02"), and has been eliminated.  Supporting names —
`bourgainConst` (a choice of constant `C`), `bourgainConst_pos` (its positivity),
and `rothNumberNat_le_bourgain` (the bound at the chosen constant) — give
downstream consumers a stable API without having to call `Exists.choose` manually.

The distinguishing content is the explicit analytic reduction "Bloom–Sisask ⟹
Bourgain": the constant is read off the `N = 3` endpoint and the comparison is
closed by `Real.rpow` monotonicity (details below).  Also recorded: consistency
with Mathlib's qualitative `rothNumberNat_isLittleO_id`, with Behrend's
unconditional lower bound, and that `rothNumberNat N` is bounded by the *minimum*
of the Bourgain and Bloom–Sisask right-hand sides.  The Lean formalization of
Bourgain's proof itself (discrete Fourier analysis with Bohr-set density
increment) remains out of scope; here Bourgain rests only on the *single* gallery
assumption already present in OQ-02.

## The analytic core (Bloom–Sisask ⟹ Bourgain)

After cancelling the common factor `N > 0` and writing `L = log N`, `LL = log log N`:
`L^(1+c)` splits as `L^(1/2)·L^(1/2+c)` (`Real.rpow_add`) and `(LL/L)^(1/2)` splits
as `LL^(1/2)/L^(1/2)` (`Real.div_rpow`), reducing the goal to
`1 ≤ (LL^(1/2)·L^(1/2+c))/(B·E)` with `B = (log log 3)^(1/2)`, `E = (log 3)^(1/2+c)`.
Both `LL^(1/2) ≥ B` and `L^(1/2+c) ≥ E` hold by `Real.rpow` monotonicity in the base
(`log 3 ≤ log N`, `log log 3 ≤ log log N`, valid since `N ≥ 3 ⟹ log N ≥ log 3 > 1
⟹ log log N > 0`).  Choosing `C = 1/(B·E)` closes it.

## The Quantitative Landscape

| Author (year)        | Bound on `r₃(N)`                         |
|----------------------|------------------------------------------|
| Roth (1953)          | `≪ N / log log N`                        |
| **Bourgain (1999)**  | `≪ N (log log N / log N)^{1/2}`  ← OQ-01  |
| Bourgain (2008)      | `≪ N (log log N)² / log N`                |
| Sanders (2011)       | `≪ N (log log N)^{O(1)} / log N`         |
| Bloom (2016)         | `≪ N (log log N)⁴ / log N`               |
| Bloom–Sisask (2020)  | `≪ N / (log N)^{1+c}`            ← OQ-02  |
| Kelley–Meka (2023)   | `≪ N · exp(-c (log N)^β)`                 |

The Bourgain 1999 saving over Roth is a *power of log* (`(log N)^{1/2}` up
to a `log log` factor), not merely a `log log` saving. Because the later
Bloom–Sisask bound `N / (log N)^{1+c}` decays strictly faster than the
Bourgain bound, **OQ-01 is implied by OQ-02**; this file records that
implication directly through `rothNumberNat_le_min_bourgain_blasi`.

## Scope (researcher-10, 2026-06-25; axiom eliminated researcher-1, 2026-06-28)

- File status: **axiomatized** — the result rests on the imported
  `RothTheoremOQ02.rothNumberNat_bloom_sisask`, but this file declares **0 axioms
  of its own** (the former `axiom rothNumberNat_bourgain` is now a derived theorem),
  0 sorries.
- Imports `Mathlib.Combinatorics.Additive.Corner.Roth` (for `rothNumberNat`
  and `rothNumberNat_isLittleO_id`), `...AP.Three.Behrend` (for
  `Behrend.roth_lower_bound`), the real `log`/`rpow` API, `...ExponentialBounds`
  (for `Real.exp_one_lt_d9`), and the sibling `Proofs.RothTheoremOQ02` (for
  `rothNumberNat_bloom_sisask` / `rothNumberNat_le_blasi`).
- Works at the **Mathlib `rothNumberNat`** level (over `Finset (Fin N)` /
  `ℕ`), *not* the project-local `Szemeredi.Roth.rothNumber` over `ZMod N`
  used in `RothTheorem.lean`, matching OQ-02 and the qualitative
  `rothNumberNat_isLittleO_id`.

## References

- Bourgain, J. (1999). *On triples in arithmetic progression.* Geom. Funct.
  Anal. 9, 968–984.
- Bloom, T. F., Sisask, O. (2020). *Breaking the logarithmic barrier in
  Roth's theorem on arithmetic progressions.* arXiv:2007.03528.
- Mathlib v4.26.0 module docstring of
  `Mathlib.Combinatorics.Additive.AP.Three.Defs`.
- Sibling file: `proofs/Proofs/RothTheoremOQ02.lean`.
-/

namespace RothTheoremOQ01

open Asymptotics Filter Topology

/-- **Bourgain's 1999 quantitative bound on the Roth number — derived, not axiomatized.**

  ∃ C > 0, ∀ N ≥ 3, rothNumberNat N ≤ C · N · (log log N / log N)^(1/2)

Bourgain (Geom. Funct. Anal. 1999) proved this analytically via a Bohr-set density
increment; the full proof needs additive-combinatorics infrastructure not in Mathlib.
But the bound need not be assumed: the **Bloom–Sisask 2020 bound** `rothNumberNat N ≤
N / (log N)^(1+c)` (`RothTheoremOQ02.rothNumberNat_bloom_sisask`) decays strictly faster,
so it *implies* Bourgain.  We discharge the implication explicitly, eliminating the
formerly-separate `axiom rothNumberNat_bourgain`.

The lower bound `N ≥ 3` ensures `log N ≥ log 3 > 1 > 0`, hence `log (log N) > 0`, so the
base `log log N / log N` is positive and the bound is non-vacuous. -/
theorem rothNumberNat_bourgain :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 3 ≤ N →
      (rothNumberNat N : ℝ) ≤
        C * (N : ℝ) * (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2) := by
  obtain ⟨c, hc, hbs⟩ := RothTheoremOQ02.rothNumberNat_bloom_sisask
  -- endpoint constants at N = 3: `log 3 > 1` and `log log 3 > 0`.
  have h3R : (0 : ℝ) < 3 := by norm_num
  have h_e_lt_3 : Real.exp 1 < 3 :=
    Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)
  have h_one_lt_log3 : (1 : ℝ) < Real.log 3 := by
    have h := (Real.log_lt_log_iff (Real.exp_pos 1) h3R).mpr h_e_lt_3
    rwa [Real.log_exp] at h
  have h_log3_pos : (0 : ℝ) < Real.log 3 := lt_trans one_pos h_one_lt_log3
  have h_loglog3_pos : (0 : ℝ) < Real.log (Real.log 3) := Real.log_pos h_one_lt_log3
  set B : ℝ := Real.log (Real.log 3) ^ ((1 : ℝ) / 2) with hB
  set E : ℝ := Real.log 3 ^ ((1 : ℝ) / 2 + c) with hE
  have hB_pos : 0 < B := Real.rpow_pos_of_pos h_loglog3_pos _
  have hE_pos : 0 < E := Real.rpow_pos_of_pos h_log3_pos _
  refine ⟨1 / (B * E), by positivity, ?_⟩
  intro N hN
  -- per-`N` positivity facts.
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le h3R hNR
  have h_log3_le_logN : Real.log 3 ≤ Real.log N := Real.log_le_log h3R hNR
  have h_one_lt_logN : (1 : ℝ) < Real.log N := lt_of_lt_of_le h_one_lt_log3 h_log3_le_logN
  have h_logN_pos : (0 : ℝ) < Real.log N := lt_trans one_pos h_one_lt_logN
  have h_loglogN_pos : (0 : ℝ) < Real.log (Real.log N) := Real.log_pos h_one_lt_logN
  have h_loglog3_le : Real.log (Real.log 3) ≤ Real.log (Real.log N) :=
    Real.log_le_log h_log3_pos h_log3_le_logN
  -- the Bloom–Sisask bound at this `N`.
  have hbsN : (rothNumberNat N : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + c) := hbs N hN
  -- the analytic comparison: Bloom–Sisask RHS ≤ Bourgain RHS.
  have hkey : (N : ℝ) / Real.log N ^ (1 + c) ≤
      (1 / (B * E)) * (N : ℝ) * (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2) := by
    have hLpow_pos : (0 : ℝ) < Real.log N ^ (1 + c) := Real.rpow_pos_of_pos h_logN_pos _
    -- L^(1+c) = L^(1/2) · L^(1/2+c)
    have hLsplit : Real.log N ^ (1 + c)
        = Real.log N ^ ((1 : ℝ) / 2) * Real.log N ^ ((1 : ℝ) / 2 + c) := by
      rw [← Real.rpow_add h_logN_pos]; congr 1; ring
    -- (LL/L)^(1/2) = LL^(1/2) / L^(1/2)
    have hdiv : (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2)
        = Real.log (Real.log N) ^ ((1 : ℝ) / 2) / Real.log N ^ ((1 : ℝ) / 2) := by
      rw [Real.div_rpow h_loglogN_pos.le h_logN_pos.le]
    -- base-monotonicity of the two `rpow` factors.
    have hBmono : B ≤ Real.log (Real.log N) ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow h_loglog3_pos.le h_loglog3_le (by norm_num)
    have hEmono : E ≤ Real.log N ^ ((1 : ℝ) / 2 + c) :=
      Real.rpow_le_rpow h_log3_pos.le h_log3_le_logN (by positivity)
    rw [div_le_iff₀ hLpow_pos, hdiv, hLsplit]
    have heq : (1 / (B * E)) * (N : ℝ) *
        (Real.log (Real.log N) ^ ((1 : ℝ) / 2) / Real.log N ^ ((1 : ℝ) / 2)) *
          (Real.log N ^ ((1 : ℝ) / 2) * Real.log N ^ ((1 : ℝ) / 2 + c))
        = (Real.log (Real.log N) ^ ((1 : ℝ) / 2) * Real.log N ^ ((1 : ℝ) / 2 + c)) / (B * E)
            * (N : ℝ) := by
      have hsne : Real.log N ^ ((1 : ℝ) / 2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos h_logN_pos _)
      field_simp
      try ring
    rw [heq]
    have hat : B * E ≤ Real.log (Real.log N) ^ ((1 : ℝ) / 2) * Real.log N ^ ((1 : ℝ) / 2 + c) :=
      mul_le_mul hBmono hEmono hE_pos.le (le_trans hB_pos.le hBmono)
    have h1le : 1 ≤ (Real.log (Real.log N) ^ ((1 : ℝ) / 2) * Real.log N ^ ((1 : ℝ) / 2 + c))
        / (B * E) := (one_le_div (by positivity)).mpr hat
    exact le_mul_of_one_le_left hNpos.le h1le
  exact le_trans hbsN hkey

/-- A canonical choice of the Bourgain constant `C > 0` extracted from the
axiom via `Exists.choose`. Marked `noncomputable` because `Exists.choose`
is. -/
noncomputable def bourgainConst : ℝ :=
  rothNumberNat_bourgain.choose

/-- The Bourgain constant is positive. -/
theorem bourgainConst_pos : 0 < bourgainConst :=
  rothNumberNat_bourgain.choose_spec.1

/-- **Bourgain bound at the canonical constant.** For every `N ≥ 3`,
`rothNumberNat N ≤ bourgainConst · N · (log log N / log N)^(1/2)`. Stable
downstream API that hides the `Exists.choose`. -/
theorem rothNumberNat_le_bourgain (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤
      bourgainConst * (N : ℝ) * (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2) :=
  rothNumberNat_bourgain.choose_spec.2 N hN

/-- **Consistency with Mathlib's qualitative result.** Mathlib v4.26.0
records `rothNumberNat_isLittleO_id : (rothNumberNat N : ℝ) =o[atTop] (N : ℝ)`
unconditionally in `Mathlib.Combinatorics.Additive.Corner.Roth`. The Bourgain
axiom strengthens this with an *explicit* decay rate
`O(N · (log log N / log N)^{1/2})`, and is consistent with the qualitative
form in the sense that both assert `rothNumberNat N = o(N)`. We record the
qualitative form as a one-line export so OQ-01 consumers can pull it in via
this namespace without re-deriving it from the axiom. -/
theorem bourgain_consistent_with_isLittleO :
    IsLittleO atTop (fun N : ℕ => (rothNumberNat N : ℝ))
      (fun N : ℕ => (N : ℝ)) :=
  rothNumberNat_isLittleO_id

/-- **Consistency of the Bourgain upper bound with Behrend's lower bound.**
For every `N ≥ 3`, Behrend's explicit lower bound on `rothNumberNat N` does
not exceed the Bourgain upper bound:

  `N · exp(-4 · √(log N)) ≤ bourgainConst · N · (log log N / log N)^(1/2)`.

This sanity-checks the `rothNumberNat_bourgain` axiom against the
*unconditional* lower bound `Behrend.roth_lower_bound` proved in Mathlib
v4.26.0:

  `(N : ℝ) * exp (-4 * √(log N)) ≤ rothNumberNat N`.

The proof is purely transitive through `rothNumberNat N`: both bounds hold
simultaneously, so the lower bound is `≤` the upper bound. We do *not* prove
the underlying analytic inequality directly; the consistency follows
automatically from the existence of both bounds. -/
theorem bourgain_consistent_with_Behrend (N : ℕ) (hN : 3 ≤ N) :
    (N : ℝ) * Real.exp (-4 * Real.sqrt (Real.log N)) ≤
      bourgainConst * (N : ℝ) * (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2) :=
  (Behrend.roth_lower_bound).trans (rothNumberNat_le_bourgain N hN)

/-- **OQ-02 implies OQ-01: the Bloom–Sisask bound is at least as strong.**
Both the Bourgain (OQ-01) and the Bloom–Sisask (OQ-02,
`RothTheoremOQ02.rothNumberNat_le_blasi`) upper bounds hold simultaneously,
so `rothNumberNat N` is bounded by the *minimum* of the two right-hand sides:

  `rothNumberNat N ≤ min ( bourgainConst · N · (log log N / log N)^{1/2} )
                         ( N / (log N)^{1 + blasiConst} )`.

Because the Bloom–Sisask right-hand side `N / (log N)^{1+c}` decays strictly
faster than the Bourgain right-hand side, this `min` is (for large `N`) the
Bloom–Sisask term — the formal record that OQ-02 ⟹ OQ-01. The proof is a
one-line `le_min` of the two axiomatic bounds; we do not prove the analytic
domination of one right-hand side by the other (an unconditional comparison
would require tracking the unknown constants `bourgainConst` and
`RothTheoremOQ02.blasiConst`). -/
theorem rothNumberNat_le_min_bourgain_blasi (N : ℕ) (hN : 3 ≤ N) :
    (rothNumberNat N : ℝ) ≤
      min (bourgainConst * (N : ℝ) *
            (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2))
          ((N : ℝ) / Real.log N ^ (1 + RothTheoremOQ02.blasiConst)) :=
  le_min (rothNumberNat_le_bourgain N hN) (RothTheoremOQ02.rothNumberNat_le_blasi N hN)

/-- **The Bourgain density factor `(log log N / log N)^{1/2}` tends to `0`.**
This is the analytic heart of "explicit rate ⟹ `o(N)`": `log log N / log N → 0`
because `log =o[atTop] id` (so `log u / u → 0`, applied at `u = log N → ∞`), and the
continuous `·^{1/2}` map carries the limit `0 ↦ 0`.  Axiom-free (uses only Mathlib's
`Real.isLittleO_log_id_atTop`). -/
theorem bourgain_factor_tendsto_zero :
    Filter.Tendsto
      (fun N : ℕ => (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2))
      Filter.atTop (nhds 0) := by
  -- `log u / u → 0` as `u → ∞`, from `log =o[atTop] id`.
  have hbase : Filter.Tendsto (fun u : ℝ => Real.log u / u) Filter.atTop (nhds 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  -- `log N → ∞` as `N → ∞` (over ℕ).
  have hlogN : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- compose: `log (log N) / log N → 0`.
  have hratio : Filter.Tendsto
      (fun N : ℕ => Real.log (Real.log N) / Real.log N) Filter.atTop (nhds 0) :=
    hbase.comp hlogN
  -- `√·` is continuous and sends `0 ↦ 0`; `√x = x ^ (1/2)`.
  have hsqrt : Filter.Tendsto
      (fun N : ℕ => Real.sqrt (Real.log (Real.log N) / Real.log N))
      Filter.atTop (nhds 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hratio
    simpa [Real.sqrt_zero] using this
  exact hsqrt.congr (fun N => Real.sqrt_eq_rpow _)

/-- **Bourgain's explicit bound recovers the qualitative Roth theorem — derived, not
re-exported.**  From `rothNumberNat N ≤ C · N · (log log N / log N)^{1/2}` with the density
factor tending to `0`, we obtain `rothNumberNat N = o(N)` directly.  Unlike
`bourgain_consistent_with_isLittleO` (which merely re-exports Mathlib's independent
`rothNumberNat_isLittleO_id`), this theorem *proves* the little-o statement **from the
quantitative Bourgain bound**, so it certifies that the explicit rate is genuinely strong
enough to yield `o(N)`. -/
theorem rothNumberNat_isLittleO_of_bourgain :
    Asymptotics.IsLittleO Filter.atTop
      (fun N : ℕ => (rothNumberNat N : ℝ)) (fun N : ℕ => (N : ℝ)) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  -- `bourgainConst · (factor N) → 0`, so eventually it is `< ε`.
  have hfac : Filter.Tendsto
      (fun N : ℕ => bourgainConst *
        (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2))
      Filter.atTop (nhds 0) := by
    simpa using bourgain_factor_tendsto_zero.const_mul bourgainConst
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      bourgainConst * (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2) < ε := by
    have hmem : Set.Iio ε ∈ nhds (0 : ℝ) := Iio_mem_nhds hε
    simpa [Set.mem_Iio] using hfac.eventually hmem
  filter_upwards [hev, Filter.eventually_ge_atTop 3] with N hbound hN3
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Nat.abs_cast, Nat.abs_cast]
  calc (rothNumberNat N : ℝ)
      ≤ bourgainConst * (N : ℝ) *
          (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2) :=
        rothNumberNat_le_bourgain N hN3
    _ = (bourgainConst *
          (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2)) * (N : ℝ) := by ring
    _ ≤ ε * (N : ℝ) := mul_le_mul_of_nonneg_right hbound.le (Nat.cast_nonneg N)

/-- **Endpoint positivity.** For `N ≥ 3`, `log N > 1` (since `N ≥ 3 > e`). A small
reusable helper extracted from the endpoint reasoning in `rothNumberNat_bourgain`. -/
theorem one_lt_logN_of_three_le {N : ℕ} (hN : 3 ≤ N) : (1 : ℝ) < Real.log N := by
  have h3R : (0 : ℝ) < 3 := by norm_num
  have hNR : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have h_e_lt_3 : Real.exp 1 < 3 :=
    Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)
  have h_one_lt_log3 : (1 : ℝ) < Real.log 3 := by
    have h := (Real.log_lt_log_iff (Real.exp_pos 1) h3R).mpr h_e_lt_3
    rwa [Real.log_exp] at h
  exact lt_of_lt_of_le h_one_lt_log3 (Real.log_le_log h3R hNR)

/-- **Double-log positivity.** For `N ≥ 3`, `log (log N) > 0`, since `log N > 1`. -/
theorem loglog_pos_of_three_le {N : ℕ} (hN : 3 ≤ N) :
    0 < Real.log (Real.log N) :=
  Real.log_pos (one_lt_logN_of_three_le hN)

/-- **Polylog decay engine (axiom-free).** `(log log N)³ / log N → 0`.  This is the
quantitative core distinguishing Bourgain's `(log log N / log N)^{1/2}` saving from
Roth's original `1 / log log N` saving: setting `u = log N → ∞`, Mathlib's
`Real.tendsto_pow_log_div_mul_add_atTop` gives `(log u)³ / u → 0`, and `log N → ∞`
carries the limit through the composition.  Uses only Mathlib's log-growth API — no
axioms, no dependence on the Bloom–Sisask assumption. -/
theorem loglog_cubed_div_log_tendsto_zero :
    Filter.Tendsto
      (fun N : ℕ => Real.log (Real.log N) ^ 3 / Real.log N)
      Filter.atTop (nhds 0) := by
  -- `(log u)³ / u → 0` as `u → ∞`.
  have hpoly : Filter.Tendsto (fun u : ℝ => Real.log u ^ 3 / u) Filter.atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero
  -- `log N → ∞` as `N → ∞` (over ℕ).
  have hlogN : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- compose: `(log (log N))³ / log N → 0`.
  simpa [Function.comp] using hpoly.comp hlogN

/-- **Bourgain's saving is asymptotically strictly stronger than Roth's 1953 saving.**

The Bourgain 1999 density factor `(log log N / log N)^{1/2}` is `o` of Roth's original
1953 density factor `1 / log log N`:

  `(fun N => (log log N / log N)^{1/2}) =o[atTop] (fun N => 1 / log log N)`.

This formalizes the qualitative point emphasized throughout this file and its
references — that Bourgain's improvement is a *power-of-log* saving, genuinely
better than Roth's mere `log log` saving, not a rephrasing of it.  The ratio
squares to `(log log N)³ / log N → 0` (`loglog_cubed_div_log_tendsto_zero`), so the
ratio itself is `√((log log N)³ / log N) → 0`.  **Axiom-free** — this is a pure
statement about the two rate *shapes* and does not touch the Bloom–Sisask
assumption. -/
theorem bourgain_factor_isLittleO_roth_factor :
    Asymptotics.IsLittleO Filter.atTop
      (fun N : ℕ => (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2))
      (fun N : ℕ => 1 / Real.log (Real.log N)) := by
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
  · -- `g N = 0 → f N = 0` holds vacuously for `N ≥ 3` (there `1 / log log N ≠ 0`).
    filter_upwards [Filter.eventually_ge_atTop 3] with N hN h0
    exact absurd h0 (one_div_ne_zero (ne_of_gt (loglog_pos_of_three_le hN)))
  · -- the ratio `f N / g N = √((log log N)³ / log N) → 0`.
    have hratio : Filter.Tendsto
        (fun N : ℕ => Real.sqrt (Real.log (Real.log N) ^ 3 / Real.log N))
        Filter.atTop (nhds 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp loglog_cubed_div_log_tendsto_zero
      simpa [Real.sqrt_zero] using this
    refine hratio.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 3] with N hN
    have hLL : 0 < Real.log (Real.log N) := loglog_pos_of_three_le hN
    have hL : 0 < Real.log N := lt_trans one_pos (one_lt_logN_of_three_le hN)
    -- `(log log N)³ / log N = (log log N / log N) · (log log N)²` (field identity).
    have e1 : Real.log (Real.log N) ^ 3 / Real.log N
        = Real.log (Real.log N) / Real.log N * Real.log (Real.log N) ^ 2 := by ring
    rw [e1, Real.sqrt_mul (div_pos hLL hL).le, Real.sqrt_sq hLL.le,
        div_div_eq_mul_div, div_one, ← Real.sqrt_eq_rpow]

/-- **OQ-02's rate strictly dominates OQ-01's rate.** The Bloom–Sisask density factor
`1 / (log N)^{1 + blasiConst}` is `o` of the Bourgain density factor
`(log log N / log N)^{1/2}`:

  `(fun N => 1 / (log N)^{1+c}) =o[atTop] (fun N => (log log N / log N)^{1/2})`.

This supplies the *analytic domination* that `rothNumberNat_le_min_bourgain_blasi` explicitly
stops short of: there the two upper bounds are only combined through `min`, with the docstring
noting that the honest comparison of the two right-hand sides was **not** carried out (it would
"require tracking the unknown constants"). At the level of the density *shapes* — after
cancelling the common `N` — no constant-tracking is needed: the Bloom–Sisask saving beats the
Bourgain saving outright. The ratio equals `1 / ((log N)^{1/2+c} · (log log N)^{1/2})`, whose
denominator `→ ∞` (product of two `rpow`s of quantities tending to `∞`, since `1/2 + c > 0`).
Depends only on `blasiConst_pos`, not on the Bloom–Sisask bound itself. -/
theorem blasi_factor_isLittleO_bourgain_factor :
    Asymptotics.IsLittleO Filter.atTop
      (fun N : ℕ => 1 / Real.log N ^ (1 + RothTheoremOQ02.blasiConst))
      (fun N : ℕ => (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2)) := by
  set c := RothTheoremOQ02.blasiConst with hcdef
  have hc_pos : 0 < c := RothTheoremOQ02.blasiConst_pos
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr ?_
  · -- `g N = 0 → f N = 0` is vacuous for `N ≥ 3` (there `g N > 0`).
    filter_upwards [Filter.eventually_ge_atTop 3] with N hN h0
    have hL : 0 < Real.log N := lt_trans one_pos (one_lt_logN_of_three_le hN)
    have hLL : 0 < Real.log (Real.log N) := loglog_pos_of_three_le hN
    exact absurd h0 (ne_of_gt (Real.rpow_pos_of_pos (div_pos hLL hL) _))
  · -- The ratio `f N / g N = 1 / ((log N)^{1/2+c} · (log log N)^{1/2}) → 0`.
    have hlogN : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hloglogN : Filter.Tendsto (fun N : ℕ => Real.log (Real.log N))
        Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hlogN
    have hD : Filter.Tendsto
        (fun N : ℕ => Real.log N ^ ((1:ℝ)/2 + c) * Real.log (Real.log N) ^ ((1:ℝ)/2))
        Filter.atTop Filter.atTop := by
      have := ((tendsto_rpow_atTop (show (0:ℝ) < 1/2 + c by positivity)).comp hlogN).atTop_mul_atTop₀
        ((tendsto_rpow_atTop (show (0:ℝ) < 1/2 by norm_num)).comp hloglogN)
      simpa [Function.comp] using this
    refine (hD.inv_tendsto_atTop).congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 3] with N hN
    simp only [Pi.inv_apply]
    have hL : 0 < Real.log N := lt_trans one_pos (one_lt_logN_of_three_le hN)
    have hLL : 0 < Real.log (Real.log N) := loglog_pos_of_three_le hN
    have hLsplit : Real.log N ^ (1 + c)
        = Real.log N ^ ((1:ℝ)/2) * Real.log N ^ ((1:ℝ)/2 + c) := by
      rw [← Real.rpow_add hL]; congr 1; ring
    have hL12 : Real.log N ^ ((1:ℝ)/2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL _)
    have hL12c : Real.log N ^ ((1:ℝ)/2 + c) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL _)
    have hM12 : Real.log (Real.log N) ^ ((1:ℝ)/2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hLL _)
    rw [Real.div_rpow hLL.le hL.le, hLsplit]
    field_simp

/-- **Bloom–Sisask density bound for an arbitrary 3-AP-free set.**

Every three-term-AP-free finite set `s ⊆ [0, N)` (with `N ≥ 3`) has cardinality bounded by
the Bloom–Sisask rate:

  `#s ≤ N / (log N)^(1 + blasiConst)`.

All the other quantitative bounds in this file (`rothNumberNat_le_bourgain`,
`RothTheoremOQ02.rothNumberNat_le_blasi`, …) constrain only the *extremal* Roth number
`rothNumberNat N` — the size of a *largest* 3-AP-free subset of `range N`.  This theorem
lifts the bound to *every* 3-AP-free set via Mathlib's `ThreeAPFree.le_rothNumberNat`,
giving the universally-quantified interface form that applications consume (e.g. the
Erdős reciprocal-sum problem, where one needs the density bound for the specific set at
hand, not merely the extremal one).  Inherits the single imported Bloom–Sisask assumption
through `rothNumberNat_le_blasi`; adds no new axiom. -/
theorem threeAPFree_card_le_blasi
    {s : Finset ℕ} (hs : ThreeAPFree (s : Set ℕ)) {N : ℕ} (hN : 3 ≤ N)
    (hsub : ∀ x ∈ s, x < N) :
    (s.card : ℝ) ≤ (N : ℝ) / Real.log N ^ (1 + RothTheoremOQ02.blasiConst) := by
  have hcard : s.card ≤ rothNumberNat N := ThreeAPFree.le_rothNumberNat s hs hsub rfl
  calc (s.card : ℝ) ≤ (rothNumberNat N : ℝ) := by exact_mod_cast hcard
    _ ≤ (N : ℝ) / Real.log N ^ (1 + RothTheoremOQ02.blasiConst) :=
        RothTheoremOQ02.rothNumberNat_le_blasi N hN

/-- **Bourgain density bound for an arbitrary 3-AP-free set.**

The Bourgain-strength companion of `threeAPFree_card_le_blasi`: every 3-AP-free finite set
`s ⊆ [0, N)` (`N ≥ 3`) satisfies

  `#s ≤ bourgainConst · N · (log log N / log N)^(1/2)`.

Same lifting via `ThreeAPFree.le_rothNumberNat`, this time composed with the Bourgain
extremal bound `rothNumberNat_le_bourgain`.  No new axiom. -/
theorem threeAPFree_card_le_bourgain
    {s : Finset ℕ} (hs : ThreeAPFree (s : Set ℕ)) {N : ℕ} (hN : 3 ≤ N)
    (hsub : ∀ x ∈ s, x < N) :
    (s.card : ℝ) ≤
      bourgainConst * (N : ℝ) * (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2) := by
  have hcard : s.card ≤ rothNumberNat N := ThreeAPFree.le_rothNumberNat s hs hsub rfl
  calc (s.card : ℝ) ≤ (rothNumberNat N : ℝ) := by exact_mod_cast hcard
    _ ≤ bourgainConst * (N : ℝ) *
          (Real.log (Real.log N) / Real.log N) ^ ((1 : ℝ) / 2) :=
        rothNumberNat_le_bourgain N hN

#check rothNumberNat_bourgain
#check bourgainConst
#check bourgainConst_pos
#check rothNumberNat_le_bourgain
#check bourgain_consistent_with_isLittleO
#check bourgain_consistent_with_Behrend
#check rothNumberNat_le_min_bourgain_blasi
#check bourgain_factor_tendsto_zero
#check rothNumberNat_isLittleO_of_bourgain
#check one_lt_logN_of_three_le
#check loglog_pos_of_three_le
#check loglog_cubed_div_log_tendsto_zero
#check bourgain_factor_isLittleO_roth_factor
#check blasi_factor_isLittleO_bourgain_factor
#check threeAPFree_card_le_blasi
#check threeAPFree_card_le_bourgain

-- Axiom audit: `rothNumberNat_bourgain` is now a THEOREM.  Its only non-foundational
-- dependency is the imported `RothTheoremOQ02.rothNumberNat_bloom_sisask` — there is NO
-- separate Bourgain axiom, and no `sorryAx` / `Lean.ofReduceBool`.
#print axioms rothNumberNat_bourgain

-- The rate-shape comparison and its polylog engine are fully AXIOM-FREE (they depend on
-- neither the Bourgain nor the Bloom–Sisask assumption — only Mathlib's log-growth API).
#print axioms loglog_cubed_div_log_tendsto_zero
#print axioms bourgain_factor_isLittleO_roth_factor

-- The universal (arbitrary 3-AP-free set) forms inherit exactly the one Bloom–Sisask
-- assumption via the extremal bounds; they add no new axiom of their own.
#print axioms threeAPFree_card_le_blasi
#print axioms threeAPFree_card_le_bourgain

end RothTheoremOQ01
