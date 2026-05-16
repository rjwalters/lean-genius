# State: angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01

**Slug**: `angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01`
**Title**: Inseparable Galois Groups: Counterexample and Correct Statement
**Phase**: COMPLETED (axiomatized) → S5 PREP (Step 1a pre-stage, doc-only)
**Iteration**: 5
**Gallery status**: `axiomatized`, badge `axiom`
**Lean file**: `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (285 LOC, 19 theorems, 1 axiom, 0 sorries)
**Last substantive ACT**: PR #17217 (Session 4), MERGED 2026-05-08 — 8 days ago
**Open PRs on slug**: 0 (post-S5 PREP this cycle will be the first since 2026-05-08)

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

Each step is independently useful. Step 1a is the closest concrete next step and the focus of this S5 PREP.

---

## Iteration History

| # | Date | PR | Author | Description | Δ files | LOC Δ |
|---|------|----|----|-------------|---------|-------|
| 1 | 2026-05-06 | #16106 | researcher | OBSERVE→ACT: counterexample identified, correct theorem proved (with 2 API sorries) | Lean + meta + knowledge.md | +278 (Lean) |
| 2 | 2026-05-07 | #16660 | researcher-8 | ACT: closed both API sorries via `iterateFrobenius` + `map_sub` one-liner | Lean | −25 +11 (Lean) |
| 3 | 2026-05-08 | #16967 | researcher-1 | ACT: counterexample structural scaffolding (`f_target_{natDegree, degree, ne_zero, Monic}`) | Lean + meta + knowledge.md + JSON | +25 (Lean) |
| 4 | 2026-05-08 | #17217 | researcher-1 | ACT: g_factor structural lemmas + 5 f_target coefficient values | Lean + meta + knowledge.md + JSON | +55 (Lean) |
| 5 | **2026-05-16** | **(this cycle)** | researcher-12 | **PREP: state.md bootstrap + Step 1a (aGen-not-square) pre-stage (doc-only)** | state.md + session memo + knowledge.md + JSON | 0 (Lean) |

Enrichment PRs (#16998, #17044, #17085, #17139, #17293, #17339) interleaved in 2026-05-08 expanded `meta.json` sections, references, prerequisites, and the 5th key insight (Artin-Schreier). The Lean file has been **stable since 2026-05-08** (8 days).

---

## What Was Proved

- **`algEquiv_eq_refl_of_isPurelyInseparable`** (Part II, ~20 lines): every F-algebra automorphism of a purely inseparable extension K/F is the identity. Proof: for x ∈ K, get n with x^(p^n) ∈ F (via `IsPurelyInseparable.pow_mem`); σ fixes F (via `AlgEquiv.commutes`); so (σx − x)^(p^n) = σx^(p^n) − x^(p^n) = 0 (via `iterateFrobenius` + `map_sub`); no nilpotents in a field gives σx = x.
- **`gal_card_one_of_purelyInseparable_splitting`** (corollary, ~8 lines): `Nat.card f.Gal = 1` whenever `IsPurelyInseparable F f.SplittingField`. This is the correct replacement for the parent file's false axiom `insep_gal_trivial`.
- **`sub_pow_char_pow_eq`** (helper, ~3 lines): `(a − b)^(p^n) = a^(p^n) − b^(p^n)` in char p, via `iterateFrobenius_def` + `map_sub`.
- **`insep_gal_trivial_refuted`** (~12 lines): exhibits f_target as an inseparable polynomial with `Nat.card f.Gal ≠ 1` (using `counterexample_gal_card` axiom for the cardinality count).
- **Counterexample-side structural scaffolding** (15 small lemmas, ~90 lines total): `f_target_{natDegree, degree, ne_zero, Monic}`, `g_factor_{natDegree, degree, ne_zero, Monic}`, `f_target_coeff_{zero, one, two, three, four}`, `f_target.derivative = 0`, `f_is_g_composed_sq`. These pre-stage the Artin-Schreier and Capelli machinery needed to eventually discharge `counterexample_gal_card`.

---

## What Was NOT Proved (Outstanding)

- **`counterexample_gal_card : Nat.card f_target.Gal = 2`** — intentional axiom. Discharging it requires the full Artin-Schreier chain (Steps 1a–4 above).

The slug is **closed at gallery level** (status `axiomatized`, badge `axiom`, primary theorem verified) but the explicit counterexample's Galois cardinality remains axiomatized pending the multi-session formalization. This is a stable terminal state — the gallery has been live in this configuration for 8 days with no outstanding feedback flags.

---

## Next Action

**S6 ACT (when host healthy)**: Run paste-ready Step 1a (aGen-not-square degree-parity argument). See `sessions/2026-05-16-s05.md` §4 for the paste-ready ~60-LOC sketch and §5 for the bearer table.

**S6 deferred if**: Docker daemon hung, or disk free space < 8 Gi, or any open competing PR on this slug. Today's S5 PREP cycle launched with Docker hung (`docker info` exit 124 at 10s, no server section) and disk 71% used / 6.5 Gi avail — so this S5 PREP is correctly doc-only and S6 ACT is deferred to a future cycle.

---

## ACT-Readiness Gate (snapshot 2026-05-16, post-S5 PREP)

| Gate item | Status | Notes |
|-----------|--------|-------|
| Lean file stable on origin/main since last ACT | ✅ GREEN | unchanged since 2026-05-08 (8 days), no enrichment churn since 2026-05-08 |
| Mathlib pin SHA known and recorded | ✅ GREEN | `2df2f0150c…` (v4.26.0) — same as Session 4 |
| Bearer APIs spot-checked at pin | ✅ GREEN | Step 1a bearer table in §5 of S5 session memo: 8 entries, 0 drift, 1 candidate-API gap noted (see §6 R3) |
| Paste-ready sketch produced | ✅ GREEN | ~60 LOC w/ 1 SORRY (R3) at the `IsFractionRing.div_surjective`-style application; recoverable in ACT |
| JSON `currentState.iteration` synced w/ state.md head | ✅ GREEN (post-this-PR) | bumped 4 → 5 |
| meta.json `lineCount`/`theoremCount` post-S4 | ✅ GREEN | 285 / 19, matches Lean file |
| No competing OPEN PRs on slug | ✅ GREEN | 0 open PRs as of 2026-05-16T10:50Z |
| Docker daemon responsive (`docker info` ≤10s) | 🔴 RED (INFRA) | exit 124, no Server section — blocks any Lean build |
| Disk free ≥ 8 Gi | 🟠 AMBER (INFRA) | 6.5 Gi avail; close to the 8 Gi trigger from `MEMORY.md`, but still allows doc-only PRs |

**Score**: 7/9 GREEN substantive, 1/9 RED INFRA, 1/9 AMBER INFRA. Doc-only PREP is the correct cycle move; ACT deferred until Docker + disk recover.
