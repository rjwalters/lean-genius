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

## Scope / honesty

This is the *negative* half of the open question: a verified, precise obstruction
showing the **classical** Puiseux statement cannot hold in characteristic `p`.
The *positive* analogue — identifying the actual algebraic closure of `𝔽_p((x))`
inside the Hahn series (Kedlaya's theorem: the "additive" / automatic Hahn
series, via Artin–Schreier–Witt theory) — is a deep result not formalised here
and remains the open follow-up. We do not construct the Hahn series `y` itself
(that needs the well-ordering of its support and a Frobenius computation in
characteristic `p`); the theorem is stated for *any* series carrying the
Artin–Schreier exponents, with the existence of such a series — the
Artin–Schreier root — recorded as the classical input.
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

end PuiseuxTheoremOQ01
