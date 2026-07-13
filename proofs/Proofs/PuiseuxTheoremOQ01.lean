/-
# Why Puiseux's Theorem Fails in Positive Characteristic: the Artin–Schreier Obstruction

Open question: puiseux-theorem-oq-01
("What is the correct analogue of Puiseux's theorem in positive characteristic?")

## Background

Over an algebraically closed field `K` of characteristic `0`, the field of
**Puiseux series** — Hahn series over `ℚ` whose support has a *bounded
denominator* (lies in `(1/n)·ℤ` for some fixed `n`) — is algebraically closed;
it is the algebraic closure of the Laurent series `K((x))`. This is the gallery
entry `puiseux-theorem`, whose `IsPuiseuxSeries` predicate we reproduce verbatim
below (its source file is a work-in-progress and does not yet compile against the
current Mathlib, so we keep this development self-contained).

In **positive characteristic `p`** the theorem is *false*: the Puiseux series are
**not** algebraically closed. The canonical witness is the **Artin–Schreier**
equation
    yᵖ − y = x⁻¹,
which is separable of degree `p` over `𝔽_p((x))` and whose (unique) Hahn-series
solution is
    y = ∑_{k ≥ 1} x^{−1/pᵏ}   =   x^{−1/p} + x^{−1/p²} + x^{−1/p³} + ⋯
(indeed `yᵖ = ∑_{k ≥ 1} x^{−1/p^{k−1}} = x⁻¹ + y` by the Frobenius/Freshman's
dream). This `y` is algebraic over the Laurent series, yet its exponents
`{−1/pᵏ}` have **unbounded ramification**: no single `n` clears all the
denominators `pᵏ`. So `y` is *not* a Puiseux series — the obstruction to
Puiseux's theorem in characteristic `p`.

## What this file proves (fully verified, 0 axioms)

The mathematical heart of "Puiseux fails in characteristic `p`" is exactly this
unbounded-ramification phenomenon, which we isolate and verify:

- `artinSchreierExp p k = −1/p^{k+1}` — the Artin–Schreier exponent sequence.
- `artinSchreierExp_strictAnti` / `_injective` — the exponents are distinct
  (strictly decreasing toward `0`), so there are genuinely infinitely many
  ramification levels.
- `artinSchreierExp_denominators_unbounded` — the exponent set lies in **no**
  `(1/n)·ℤ`: for every `n` some exponent `−1/p^{k+1}` has denominator `p^{k+1} > n`.
- `artinSchreier_support_not_puiseux` — **the obstruction**: any Hahn series
  `f : HahnSeries ℚ K` whose support contains every `artinSchreierExp p k` is
  **not** a Puiseux series. Applied to the Artin–Schreier root `y` (whose support
  is exactly `{−1/pᵏ}`), this is the formal statement that `y` witnesses the
  failure of Puiseux's theorem in characteristic `p`.
- `artinSchreierExp_range_isPWO` / `artinSchreierSeries` / `exists_hahnSeries_not_puiseux`
  — **non-vacuity**: the exponent set is partially well-ordered, so it is a legitimate
  Hahn-series support, and there genuinely *exists* a Hahn series over any field carrying
  those exponents that is not Puiseux. The obstruction is realised by an actual element of
  the Hahn field, not a hypothetical one.

## Scope / honesty

This is the *negative* half of the open question: a verified, precise obstruction
showing the **classical** Puiseux statement cannot hold in characteristic `p`.
The *positive* analogue — identifying the actual algebraic closure of `𝔽_p((x))`
inside the Hahn series (Kedlaya's theorem: the "additive" / automatic Hahn
series, via Artin–Schreier–Witt theory) — is a deep result not formalised here
and remains the open follow-up. We do not construct the *actual* Artin–Schreier root
(that needs a Frobenius computation in characteristic `p`, i.e. the coefficients solving
`yᵖ − y = x⁻¹`); but we *do* establish the well-ordering of its support and build an
explicit Hahn series with exactly that support (`artinSchreierSeries`, all coefficients
`1`), so the obstruction is non-vacuous — witnessed by a genuine element of the Hahn field
rather than only stated for a hypothetical one.
-/
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.Tactic

namespace PuiseuxTheoremOQ01

/-- A Hahn series over `ℚ` is a **Puiseux series** when its exponents share a
common denominator: all of them lie in `(1/n)·ℤ` for some positive integer `n`.
(Reproduced verbatim from the gallery `puiseux-theorem` entry.) -/
def IsPuiseuxSeries {K : Type*} [Zero K] (f : HahnSeries ℚ K) : Prop :=
  ∃ n : ℕ+, ∀ q ∈ f.support, ∃ k : ℤ, q = k / n

/-- The Artin–Schreier exponent sequence `−1/p^{k+1}`, i.e. the exponents
appearing in the Hahn-series root of `yᵖ − y = x⁻¹`. -/
def artinSchreierExp (p : ℕ) (k : ℕ) : ℚ := -(1 / (p : ℚ) ^ (k + 1))

/-- The Artin–Schreier exponents are strictly increasing: as `k` grows,
`−1/p^{k+1}` rises toward `0` from below (`−1/p < −1/p² < −1/p³ < ⋯`, an
increasing chain converging to `0`). So `artinSchreierExp` is strictly monotone. -/
theorem artinSchreierExp_strictMono (p : ℕ) (hp : 2 ≤ p) :
    StrictMono (artinSchreierExp p) := by
  intro a b hab
  have hp1 : (1 : ℚ) < (p : ℚ) := by exact_mod_cast hp
  have hp0 : (0 : ℚ) < (p : ℚ) := by linarith
  simp only [artinSchreierExp, neg_lt_neg_iff]
  exact one_div_lt_one_div_of_lt (pow_pos hp0 _) (pow_lt_pow_right₀ hp1 (by omega))

/-- In particular the Artin–Schreier exponents are pairwise distinct: there are
infinitely many distinct ramification levels. -/
theorem artinSchreierExp_injective (p : ℕ) (hp : 2 ≤ p) :
    Function.Injective (artinSchreierExp p) :=
  (artinSchreierExp_strictMono p hp).injective

/-- **Unbounded ramification.** The Artin–Schreier exponent set lies in no
`(1/n)·ℤ`: for every candidate common denominator `n`, some exponent
`−1/p^{k+1}` has denominator `p^{k+1} > n` and so is not of the form `j/n`.
This is the precise reason the Artin–Schreier root fails to be a Puiseux series. -/
theorem artinSchreierExp_denominators_unbounded (p : ℕ) (hp : 2 ≤ p) :
    ¬ ∃ n : ℕ+, ∀ k : ℕ, ∃ j : ℤ, artinSchreierExp p k = (j : ℚ) / n := by
  rintro ⟨n, hn⟩
  -- pick a level whose denominator exceeds n
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (n : ℕ) < p ^ (k + 1) := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (n : ℕ) (by omega : 1 < p)
    exact ⟨k, by calc (n : ℕ) < p ^ k := hk
                   _ ≤ p ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)⟩
  obtain ⟨j, hj⟩ := hn k
  simp only [artinSchreierExp] at hj
  have hn0 : (0 : ℚ) < (n : ℚ) := by exact_mod_cast n.pos
  -- clear denominators: n = -j · p^{k+1}
  have key : (n : ℚ) = ((-j : ℤ) : ℚ) * (p : ℚ) ^ (k + 1) := by
    field_simp at hj; push_cast; linarith [hj]
  have keyZ : (n : ℤ) = (-j) * (p : ℤ) ^ (k + 1) := by exact_mod_cast key
  -- so p^{k+1} divides n, forcing p^{k+1} ≤ n, contradicting the choice of k
  have hdvd : (p : ℤ) ^ (k + 1) ∣ (n : ℤ) := ⟨-j, by rw [keyZ]; ring⟩
  have hle : (p : ℤ) ^ (k + 1) ≤ (n : ℤ) := Int.le_of_dvd (by exact_mod_cast n.pos) hdvd
  have hcast : (p ^ (k + 1) : ℕ) ≤ (n : ℕ) := by exact_mod_cast hle
  omega

/-- **The Artin–Schreier obstruction to Puiseux's theorem in characteristic `p`.**

Any Hahn series whose support contains all the Artin–Schreier exponents
`{−1/p^{k+1}}` is *not* a Puiseux series. The Artin–Schreier root `y` of
`yᵖ − y = x⁻¹` over `𝔽_p((x))` has exactly this support, so `y` is algebraic over
the Laurent series yet not a Puiseux series — Puiseux's theorem fails in
characteristic `p`. -/
theorem artinSchreier_support_not_puiseux {K : Type*} [Zero K]
    (f : HahnSeries ℚ K) (p : ℕ) (hp : 2 ≤ p)
    (hsupp : ∀ k : ℕ, artinSchreierExp p k ∈ f.support) :
    ¬ IsPuiseuxSeries f := by
  rintro ⟨n, hn⟩
  exact artinSchreierExp_denominators_unbounded p hp ⟨n, fun k => hn _ (hsupp k)⟩

/-! ## The obstruction is not vacuous: an explicit Hahn-series witness

The theorem `artinSchreier_support_not_puiseux` is stated for *any* Hahn series
carrying the Artin–Schreier exponents. To know the obstruction is non-vacuous — that
such a series genuinely exists as a bona-fide element of the Hahn field `K⦃⦃x⦄⦄` — one
must exhibit one, and a Hahn series is only well-defined when its support is
**partially well-ordered**. The Artin–Schreier exponent set `{−1/p^{k+1}}` is a strictly
increasing sequence bounded above by `0`, hence order-isomorphic to `ℕ` and so well-ordered;
we record this and build the witness. (Its coefficients are `1` rather than the specific
values of the true characteristic-`p` root — we only need *a* Hahn series with this
support, not one satisfying `yᵖ − y = x⁻¹`, which needs `char K = p`.) -/

/-- The Artin–Schreier exponent set is partially well-ordered: as the strictly monotone
image of `ℕ` (well-ordered), `{−1/p^{k+1}}` inherits `IsPWO`, so it is a legitimate
support for a Hahn series over `ℚ`. -/
theorem artinSchreierExp_range_isPWO (p : ℕ) (hp : 2 ≤ p) :
    (Set.range (artinSchreierExp p)).IsPWO := by
  rw [← Set.image_univ]
  have huniv : (Set.univ : Set ℕ).IsPWO := Set.isPWO_of_wellQuasiOrderedLE _
  exact huniv.image_of_monotone (artinSchreierExp_strictMono p hp).monotone

/-- An explicit Hahn series over any field `K` whose support is exactly the
Artin–Schreier exponent set `{−1/p^{k+1}}` (all coefficients `1`). Well-defined because
`artinSchreierExp_range_isPWO` certifies the support is partially well-ordered. -/
noncomputable def artinSchreierSeries (p : ℕ) (hp : 2 ≤ p) (K : Type*) [Field K] :
    HahnSeries ℚ K where
  coeff := Set.indicator (Set.range (artinSchreierExp p)) (fun _ => 1)
  isPWO_support' := by
    apply (artinSchreierExp_range_isPWO p hp).mono
    intro q hq
    simp only [Function.mem_support] at hq
    by_contra hnot
    exact hq (Set.indicator_of_notMem hnot _)

/-- The witness series carries every Artin–Schreier exponent in its support. -/
theorem artinSchreierSeries_carries (p : ℕ) (hp : 2 ≤ p) (K : Type*) [Field K] (k : ℕ) :
    artinSchreierExp p k ∈ (artinSchreierSeries p hp K).support := by
  simp only [HahnSeries.mem_support, artinSchreierSeries]
  rw [Set.indicator_of_mem (Set.mem_range_self k)]
  exact one_ne_zero

/-- The explicit witness is not a Puiseux series — a concrete element of `K⦃⦃x⦄⦄`
realising the Artin–Schreier obstruction. -/
theorem artinSchreierSeries_not_puiseux (p : ℕ) (hp : 2 ≤ p) (K : Type*) [Field K] :
    ¬ IsPuiseuxSeries (artinSchreierSeries p hp K) :=
  artinSchreier_support_not_puiseux _ p hp (artinSchreierSeries_carries p hp K)

/-- **The Artin–Schreier obstruction is non-vacuous.** Over every field `K` and every
`p ≥ 2` there genuinely exists a Hahn series carrying the Artin–Schreier exponents that is
not a Puiseux series. So the hypothesis of `artinSchreier_support_not_puiseux` is
satisfiable: the failure of Puiseux's theorem is witnessed by an actual element of the
Hahn field, not merely a hypothetical one. -/
theorem exists_hahnSeries_not_puiseux (p : ℕ) (hp : 2 ≤ p) (K : Type*) [Field K] :
    ∃ f : HahnSeries ℚ K, (∀ k : ℕ, artinSchreierExp p k ∈ f.support) ∧ ¬ IsPuiseuxSeries f :=
  ⟨artinSchreierSeries p hp K, artinSchreierSeries_carries p hp K,
    artinSchreierSeries_not_puiseux p hp K⟩

end PuiseuxTheoremOQ01
