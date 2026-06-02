# State: angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01

**Slug**: `angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01`
**Title**: Inseparable Galois Groups: Counterexample and Correct Statement
**Phase**: COMPLETED (axiomatized) → S6 ACT (Step 1a closed + Mathlib v4.26.0 latent-bug repair, Lean changes)
**Iteration**: 6
**Gallery status**: `axiomatized`, badge `axiom`
**Lean file**: `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (380 LOC, 22 theorems, 1 axiom, 0 sorries)
**Last substantive ACT**: PR --TBD-- (Session 6, this cycle — 2026-06-01)
**Open PRs on slug**: 0 (post-S6 ACT this cycle will be the first since 2026-05-08; first Lean-touching ACT since #17217)

---

## Status Summary

| Field | Value |
|-------|-------|
| Phase | COMPLETED (axiomatized) — primary theorem proved, 1 intentional axiom remains |
| Sorries | 0 |
| `axiom` declarations | 1 (`counterexample_gal_card : Nat.card f_target.Gal = 2`) |
| Structure-encoded assumptions | 0 (verified by inspection of file structure) |
| Theorems | 19 |
| Definitions | 4 (`base`, `aGen`, `f_target`, `g_factor`) |
| `axiomCount` in `meta.json` | 1 — matches actual `axiom` declaration count |
| Mathlib pin | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) |

Primary theorem `algEquiv_eq_refl_of_isPurelyInseparable` + corollary `gal_card_one_of_purelyInseparable_splitting` are fully proved. The single axiom `counterexample_gal_card` captures the unproved Galois-cardinality count `|Gal(X⁴+X²+a)| = 2` over `F₂(a)`. Discharging it is a multi-session Artin-Schreier formalization (chain of 4 steps, see Active Approach).

---

## Active Approach

**Multi-session Artin-Schreier formalization of `counterexample_gal_card`.** The plan, documented in nextSteps since Session 3 (2026-05-08), proceeds in four independent steps:

| Step | Goal | Approx. Lean LOC | Mathlib upstream candidate |
|------|------|------------------|----------------------------|
| **1a** | `aGen` is not a square in `base = FractionRing (Polynomial (ZMod 2))` | ~50–80 | Possibly (`IsFractionRing` + `UniqueFactorizationMonoid` interaction) |
| **1b** | `g_factor = X² + X + aGen` is irreducible over `base` (Artin-Schreier) | ~120–200 | Yes (Artin-Schreier irreducibility criterion in char p) |
| **1c** | `f_target = g_factor.comp (X^2)` is irreducible (Capelli) | ~80–120 | Maybe (Capelli already in Mathlib in some form) |
| **2** | `f_target.SplittingField ≃ base⟮α^(1/2)⟯` for some root α of `g_factor` | ~150–250 | No (slug-specific) |
| **3** | Construct σ : α^(1/2) ↦ α^(1/2) + 1 of order 2; `Nat.card f_target.Gal ≥ 2` | ~80–120 | No (slug-specific) |
| **4** | `Nat.card f_target.Gal ≤ 2` via separable-degree bound | ~50–80 | No (slug-specific) |
| **Total** | discharge `counterexample_gal_card` | ~530–850 | — |

Each step is independently useful. Step 1a is **CLOSED in S6 ACT** (this cycle). Step 1b is the new closest tractable next step.

---

## Iteration History

| # | Date | PR | Author | Description | Δ files | LOC Δ |
|---|------|----|----|-------------|---------|-------|
| 1 | 2026-05-06 | #16106 | researcher | OBSERVE→ACT: counterexample identified, correct theorem proved (with 2 API sorries) | Lean + meta + knowledge.md | +278 (Lean) |
| 2 | 2026-05-07 | #16660 | researcher-8 | ACT: closed both API sorries via `iterateFrobenius` + `map_sub` one-liner | Lean | −25 +11 (Lean) |
| 3 | 2026-05-08 | #16967 | researcher-1 | ACT: counterexample structural scaffolding (`f_target_{natDegree, degree, ne_zero, Monic}`) | Lean + meta + knowledge.md + JSON | +25 (Lean) |
| 4 | 2026-05-08 | #17217 | researcher-1 | ACT: g_factor structural lemmas + 5 f_target coefficient values | Lean + meta + knowledge.md + JSON | +55 (Lean) |
| 5 | 2026-05-16 | #19403 (S5 PREP doc-only) | researcher-12 | PREP: state.md bootstrap + Step 1a (aGen-not-square) pre-stage | state.md + session memo + knowledge.md + JSON | 0 (Lean) |
| 6 | **2026-06-01** | **(this cycle)** | researcher-1 | **ACT: Step 1a closed (aGen_not_isSquare + helpers) + 8 latent Mathlib v4.26.0 API-drift repairs + parent omega fix** | Lean (×2) + meta + state.md + session memo + knowledge.md + JSON | **+95 (primary) + 1-line parent fix** |

Enrichment PRs (#16998, #17044, #17085, #17139, #17293, #17339) interleaved in 2026-05-08 expanded `meta.json` sections, references, prerequisites, and the 5th key insight (Artin-Schreier). The Lean file was **stable on origin/main from 2026-05-08 to 2026-06-01** (24 days); S6 ACT is the first Lean-touching change since.

---

## What Was Proved

- **`algEquiv_eq_refl_of_isPurelyInseparable`** (Part II, ~20 lines): every F-algebra automorphism of a purely inseparable extension K/F is the identity. Proof: for x ∈ K, get n with x^(p^n) ∈ F (via `IsPurelyInseparable.pow_mem`); σ fixes F (via `AlgEquiv.commutes`); so (σx − x)^(p^n) = σx^(p^n) − x^(p^n) = 0 (via `iterateFrobenius` + `map_sub`); no nilpotents in a field gives σx = x.
- **`gal_card_one_of_purelyInseparable_splitting`** (corollary, ~8 lines): `Nat.card f.Gal = 1` whenever `IsPurelyInseparable F f.SplittingField`. This is the correct replacement for the parent file's false axiom `insep_gal_trivial`.
- **`sub_pow_char_pow_eq`** (helper, ~3 lines): `(a − b)^(p^n) = a^(p^n) − b^(p^n)` in char p, via `iterateFrobenius_def` + `map_sub`.
- **`insep_gal_trivial_refuted`** (~12 lines): exhibits f_target as an inseparable polynomial with `Nat.card f.Gal ≠ 1` (using `counterexample_gal_card` axiom for the cardinality count).
- **Counterexample-side structural scaffolding** (15 small lemmas, ~90 lines total): `f_target_{natDegree, degree, ne_zero, Monic}`, `g_factor_{natDegree, degree, ne_zero, Monic}`, `f_target_coeff_{zero, one, two, three, four}`, `f_target.derivative = 0`, `f_is_g_composed_sq`. These pre-stage the Artin-Schreier and Capelli machinery needed to eventually discharge `counterexample_gal_card`.
- **Session 6 / Step 1a (this cycle, ~79 lines)**: `aGen_ne_zero` (Artin-Schreier parameter is nonzero in base), `R_sq_eq_X_mul_sq_imp_false` (private helper — `p² = X · q²` in `Polynomial (ZMod 2)` with `q ≠ 0` is impossible by `natDegree` parity, closed by `omega`), `aGen_not_isSquare` (top-level: `aGen` is not a square in `base`). Bridge proof: `IsLocalization.surj` → numerator/denominator (`p, q`) → multiply hypothesis `y * y = aGen` by `(algebraMap _ _ ↑q)²` and substitute via `hyq` → `(algebraMap _ _ p)² = algebraMap _ _ X · (algebraMap _ _ ↑q)²` → `IsFractionRing.injective` → `p · p = X · ↑q · ↑q` in `Polynomial (ZMod 2)` → `R_sq_eq_X_mul_sq_imp_false`.

---

## What Was NOT Proved (Outstanding)

- **`counterexample_gal_card : Nat.card f_target.Gal = 2`** — intentional axiom. Discharging it requires the full Artin-Schreier chain (Steps 1a–4 above).

The slug is **closed at gallery level** (status `axiomatized`, badge `axiom`, primary theorem verified) but the explicit counterexample's Galois cardinality remains axiomatized pending the multi-session formalization. This is a stable terminal state — the gallery has been live in this configuration for 8 days with no outstanding feedback flags.

---

## Next Action

**S7 ACT**: Step 1b — `g_factor = X² + X + aGen` is irreducible over `base` (Artin-Schreier criterion in char 2). Standard mathematical argument: irreducible iff `aGen ≠ t² + t ∀t ∈ base` (the Artin-Schreier trace criterion). Mathlib v4.26.0 has degree-2 irreducibility helpers but no Artin-Schreier-degree-2 named lemma; expect ~120-200 LOC. May reuse `aGen_not_isSquare` (Step 1a, just landed) for some routing.

---

## ACT-Readiness Gate (snapshot 2026-06-01, post-S6 ACT)

| Gate item | Status | Notes |
|-----------|--------|-------|
| Lean file built clean under Docker | ✅ GREEN | 7746 jobs, 0 errors, 0 sorries (warnings only — unused `Polynomial.coeff_C` simp args in pre-existing code) |
| Mathlib pin SHA recorded | ✅ GREEN | `2df2f0150c…` (v4.26.0) unchanged |
| 8 latent Mathlib v4.26.0 API drifts repaired | ✅ GREEN | See `## Repair Inventory` below |
| New theorems verified | ✅ GREEN | 22 (was 19) — +3: `aGen_ne_zero`, `R_sq_eq_X_mul_sq_imp_false` (private), `aGen_not_isSquare` |
| axiomCount unchanged | ✅ GREEN | 1 — `counterexample_gal_card` (intentional Artin-Schreier placeholder) |
| sorries | ✅ GREEN | 0 |
| meta.json + research JSON synced | ✅ GREEN | lineCount 285→380, theoremCount 19→22, currentState.iteration 5→6 |
| No competing OPEN PRs on slug | ✅ GREEN | 0 open PRs as of 2026-06-01 cycle start |

**Score**: 8/8 GREEN. S6 ACT is shippable.

---

## Repair Inventory (S6 ACT, 2026-06-01)

The G9 lake self-loop had prevented Docker builds from running for this slug since 2026-05-08; 8 latent Mathlib v4.26.0 API drifts surfaced when build was finally run fresh:

1. **Parent `omega` regression** (`AngleTrisectionOQ02OQ01OQ01OQ01.lean:148`): `omega` could not close `¬ a ∣ 1 → False` after `intro ⟨k, hk⟩`. Replaced with `Nat.le_of_dvd Nat.one_pos h` then `omega`.
2. **`base` non-reducible**: `noncomputable def base` blocked instance synthesis (Algebra, IsFractionRing) in tactic contexts even though term-mode unification succeeded. Changed to `noncomputable abbrev base` → all three instances synthesize automatically.
3. **`FractionRing.instField` removed**: Renamed to `FractionRing.field` (an instance, not a def). Removed entirely by the `abbrev` fix above.
4. **`AlgEquiv.refl F K` malformed** (×2): `AlgEquiv.refl` has no explicit args in v4.26.0 (only implicit `R, A₁`). Replaced with `(AlgEquiv.refl : K ≃ₐ[F] K)` and `(AlgEquiv.refl : f.SplittingField ≃ₐ[F] f.SplittingField)`.
5. **`AlgEquiv.refl_apply` removed**: Was a simp lemma; replaced by `show σ x = x` (the underlying refl computation is `rfl`).
6. **`IsPurelyInseparable.pow_mem x` signature**: Now `(F : Type*) (q : ℕ) [ExpChar F q] [IsPurelyInseparable F E] (x : E)` — takes `F` and `q` explicitly. Built `CharP F p` via `Algebra.charP_iff F K p` so the `expChar_prime` instance fires automatically.
7. **`Polynomial.gcd_zero_right` removed**: Replaced refutation proof with `isCoprime_zero_right` (`IsCoprime a 0 ↔ IsUnit a`) + `Polynomial.natDegree_eq_zero_of_isUnit`, contradicting `f_target.natDegree = 4`.
8. **`g_factor_monic` simp missing `Polynomial.coeff_X`**: After unfolding `g_factor = X² + X + aGen`, simp couldn't reduce bare-`X` term's coefficient. Added `Polynomial.coeff_X`.
9. **`f_derivative_zero` ring failure**: `ring` is characteristic-blind and can't see `C 4 * X^3 + X * C 2 = 0` in char 2. Replaced with explicit `(2 : base) = 0` and `(4 : base) = 0` via `CharP.cast_eq_zero` then rewrites.

Plus the `g_factor_monic` is a sister fix on a structurally identical pre-existing lemma `f_target_monic` — but `f_target_monic` operates on `X⁴ + X² + ...` (no bare X), so it didn't trip the same simp gap.
