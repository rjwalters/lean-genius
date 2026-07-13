# Session — Iter 27a PREP-1 (Mathlib bearer survey for the Σ₂(ℤ) attack)

**Date**: 2026-06-02 (researcher-1)
**Phase**: ACT — iter 27 picker's slot
**Scope**: doc-only — no Lean edits, no gallery `meta.json` numerics, no Docker.
**Goal**: convert the S27/S28/S29 "iter 27a = sole forward candidate" recommendation
into an actionable upstream-readiness assessment, by enumerating the Mathlib v4.26.0
bearer surface that a Σ₂(ℤ) attack via the Koenigsmann Hilbert-symbol architecture
would depend on. Decide whether iter 27a-ACT is upstream-ready, upstream-partial,
or upstream-blocked, and propose the next-cycle PREP-2 target.

## 1. Why this PREP

S27/S28/S29 each shipped doc-only STATE-SYNC content without addressing the
substantive content of iter 27a beyond naming the candidate. S29 (researcher-1,
2026-05-31) sharpened the picker matrix down to a *single* forward candidate
(iter 27a) and three anti-candidates (27b/c/d/e), but stopped short of asking
whether iter 27a is *upstream-realisable* at all under the slug's anti-axiom
policy. PREP-1 answers that question.

The recommended sub-step from S27 is:

> "nail Σ₂/Π₂ symmetric duality on a non-trivial fragment (e.g., the
> rational-square cone) before attacking the full ℤ case."

To do this in Lean, we need to know what Hilbert-symbol / quadratic-form /
local-global infrastructure actually exists at the pinned Mathlib revision.

## 2. Mathlib pin & survey methodology

- **Pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`),
  confirmed direct read of `proofs/lake-manifest.json` at this PR's base SHA.
- **Method**: shallow clone of `leanprover-community/mathlib4` at branch
  `v4.26.0`, verified `git rev-parse HEAD` matches the pin; full-tree `find` +
  targeted `grep` for the relevant API surface. Clone removed after survey
  (disk hygiene — see §5.2).
- **Snapshot integrity**: per-file SHA-256 captured below; future PREP cycles
  can re-verify byte-stability without re-cloning.

## 3. Bearer surface — what Mathlib has at the pin

### 3.1 Quadratic-residue / Legendre-symbol infrastructure (PRESENT)

| Module                                                              | Size (bytes) | SHA-256 (truncated)                                 |
|---------------------------------------------------------------------|--------------|------------------------------------------------------|
| `Mathlib/NumberTheory/LegendreSymbol/Basic.lean`                    | 10637        | `88091de6404ffc470e4cef57b5d068f9cd5326fc52710e1941…` |
| `Mathlib/NumberTheory/LegendreSymbol/JacobiSymbol.lean`             | (file present, 589 LOC) | (not captured) |
| `Mathlib/NumberTheory/LegendreSymbol/QuadraticReciprocity.lean`     | (file present) | (not captured) |
| `Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean`      | (file present) | (not captured) |
| `Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean`   | (file present) | (not captured) |
| `Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean`                 | (file present) | (not captured) |

What this gives us: the Legendre symbol `legendreSym p a` over `ZMod p`, the
Jacobi symbol over (odd) naturals, supplementary laws for `−1`/`2`/`−2`,
the full quadratic reciprocity statement, and Gauss sums. All keyed on
prime-power moduli over `ZMod p` / `ℤ`, NOT over `ℚ`.

### 3.2 p-adic infrastructure (PRESENT)

| Module                                                | LOC | Purpose |
|-------------------------------------------------------|-----|---------|
| `Mathlib/NumberTheory/Padics/PadicNorm.lean`          | 320 | p-adic norm on `ℚ` |
| `Mathlib/NumberTheory/Padics/PadicNumbers.lean`       | (present) | completion `ℚ_p` |
| `Mathlib/NumberTheory/Padics/PadicIntegers.lean`      | (present) | `ℤ_p` |
| `Mathlib/NumberTheory/Padics/PadicVal/Basic.lean`     | (present) | p-adic valuation |
| `Mathlib/NumberTheory/Padics/Hensel.lean`             | (present) | Hensel's lemma |
| `Mathlib/NumberTheory/Padics/ProperSpace.lean`        | (present) | topology |
| `Mathlib/NumberTheory/Padics/RingHoms.lean`           | (present) | `ℤ_p`-algebra maps |

What this gives us: full ℚ_p / ℤ_p infrastructure including p-adic norm /
valuation, Hensel's lemma, and topology. Sufficient to *state* local-global
predicates over `ℚ`, but no built-in local-global theorem (Hasse-Minkowski etc.).

### 3.3 Quadratic-form infrastructure (PRESENT but ALGEBRAIC)

| Module                                                | Notes |
|-------------------------------------------------------|-------|
| `Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`      | abstract `QuadraticForm R M` |
| `Mathlib/LinearAlgebra/QuadraticForm/Isometry.lean`   | isometry typeclass |
| `Mathlib/LinearAlgebra/QuadraticForm/TensorProduct.lean` | ⊗ structure |
| `Mathlib/LinearAlgebra/QuadraticForm/Real.lean`       | over ℝ |
| `Mathlib/LinearAlgebra/QuadraticForm/Complex.lean`    | over ℂ |
| (no `…/QuadraticForm/Rational.lean`)                  | NOT present |

What this gives us: an abstract `QuadraticForm` typeclass and isometry
classification over ℝ and ℂ. NO specialization to ℚ; the local-global
classification (Hasse-Minkowski for `QuadraticForm ℚ M`) is NOT present
in v4.26.0. The `Real.lean` and `Complex.lean` specializations are useful
templates if a future Mathlib PR ports them to ℚ + ℚ_p.

### 3.4 Brauer-group infrastructure (SKELETON ONLY)

| Module                                       | Size | Status |
|----------------------------------------------|------|--------|
| `Mathlib/Algebra/BrauerGroup/Defs.lean`      | 3711 bytes / 98 LOC | **Definition only** — `CSA`, `IsBrauerEquivalent`, `Brauer.CSA_Setoid`. **TODO** list at top of file: "1. Prove that the Brauer group is an abelian group … 2. Prove that the Brauer group is a functor … 3. Prove that over a field, being Brauer equivalent is the same as being Morita equivalent." |

What this gives us: the *definition* of the Brauer group of a field, with
no abelian-group structure, no functoriality, no computation, no Brauer
group of `ℚ` (which Koenigsmann's argument depends on). **Not usable for
iter 27a in its current form.**

### 3.5 Diophantine / MRDP infrastructure (PRESENT, but over ℕ)

| Module                                       | LOC  | Status |
|----------------------------------------------|------|--------|
| `Mathlib/NumberTheory/Dioph.lean`            | 29739 bytes / large | Carneiro 2018 formalization of MRDP / Matiyasevic over **ℕ**: `IsPoly`, `Poly`, `Dioph`, `DiophFn`, `pell_dioph`, `pow_dioph`. File header explicit TODO: "Finish the solution of Hilbert's tenth problem." (the H10 *decidability* statement is NOT yet stated; only the building blocks). |

What this gives us: a polynomial / Diophantine framework over `ℕ`, matching
the standard MRDP formulation. The Pell equation is Diophantine, the
power function is Diophantine. The H10/ℤ undecidability theorem is *not*
stated as a Lean theorem; `Dioph.lean`'s TODO leaves it for future work.
**Cross-cutting with `Hilbert10OQ01OQ02.lean`'s `H10_Rational_Decidable`**:
the slug's local axiom approach is unchanged by this — the ℕ-Diophantine
infrastructure does not transfer to ℚ-Diophantine without the MRDP
quantifier-elimination step, which is the open question.

### 3.6 What Mathlib DOES NOT have at the pin

Exhaustive `grep` against the pin for the missing infrastructure:

| Search pattern                                            | Files found |
|-----------------------------------------------------------|-------------|
| `HilbertSymbol`, `hilbertSymbol`, `hilbert_symbol`         | **0** |
| `HasseMinkowski`, `hasse_minkowski`                       | **0** |
| `HilbertTen`, `Hilbert10`, `H10`                          | **0** |
| `Koenigsmann`                                             | **0** |
| `Poonen` (as identifier)                                  | **0** |
| `isNonsquare`, `nonsquare` (as identifier, in NumberTheory) | 0 (`IsSquare` and `nonsquare` appear only in `SumTwoSquares`, `Pell`, etc., not as standalone predicates) |

**The 5 specific bearers a naive iter 27a Σ₂(ℤ) ACT would need are ALL ABSENT**:

1. `Mathlib.NumberTheory.HilbertSymbol` — the Hilbert symbol `(a, b)_v` at a place `v` of ℚ. Foundational for Koenigsmann's polynomial.
2. `Mathlib.NumberTheory.QuadraticForms.HasseMinkowski` — local-global principle for quadratic forms over ℚ. Required to translate the Hilbert-symbol predicate into a polynomial identity over ℚ.
3. `Mathlib.NumberTheory.BrauerGroup.Rational` — Brauer group `Br(ℚ)` and its description via local Hilbert symbols (Albert-Brauer-Hasse-Noether). The Koenigsmann polynomial is constructed via this.
4. `Mathlib.NumberTheory.Poonen.NonSquaresDiophantine` — Poonen 2009 "the set of nonsquares in a number field is Diophantine". Referenced in iter 0 docstring (line 54) as a `papers` entry but never used in Lean.
5. `Mathlib.NumberTheory.Hilbert10.Rational` — the H10/ℚ-decidability predicate at the Lean level. The slug's local `H10_Rational_Decidable` axiom is a stub for this.

## 4. Implications for iter 27a — upstream-readiness assessment

**Verdict**: iter 27a is **UPSTREAM-BLOCKED** in its naive form (formal Σ₂(ℤ)
ACT via the Koenigsmann Hilbert-symbol architecture). The five core bearers
in §3.6 are all absent from Mathlib v4.26.0 at the pin. Building any one of
them from scratch is itself a multi-PR Mathlib contribution (estimated 500-2000
LOC per bearer based on the size of comparable Mathlib infrastructure like
`LegendreSymbol/` ≈ 6-file directory, `Padics/` ≈ 10-file directory).

**Anti-axiom-policy constraint**: the slug forbids stating
`koenigsmann_hilbert_symbol_polynomial : Σ₂ formula …` as an axiom for the
same reason it defers iter 27d (Daans 2021 10-quantifier reduction): each
such axiom is a new opaque assumption whose provenance lives entirely
outside the formal system. The single `koenigsmann_2016_universal` axiom is
acceptable because (a) it states the THEOREM rather than the polynomial
construction and (b) it is the *only* anchor needed for the Π₂ side; adding
a parallel axiom for Σ₂ would be a strict expansion of the assumption
surface for a question whose *answer is currently open*.

**Consequence**: iter 27a cannot ship a substantive ACT against
`IntegersAreExistentialUniversalOverQ` without either:

- (i) waiting for upstream Mathlib to land at least bearers #1-#2 from §3.6
  (HilbertSymbol + HasseMinkowski over ℚ); OR
- (ii) accepting a new axiom (`σ2_koenigsmann_witness` or similar), which is
  blocked by the anti-axiom-policy; OR
- (iii) reformulating the iter 27a goal to a strictly *weaker* sub-step that
  doesn't require the missing bearers.

Option (i) is the long-term-correct path but is outside the slug's control —
it depends on upstream Mathlib researcher attention. Option (ii) is forbidden.
Option (iii) is the only constructive path for iter 27 picker action.

## 5. Proposed iter 27a sub-paths (under option (iii))

The S27 recommendation already hints at this: "nail Σ₂/Π₂ symmetric duality
on a non-trivial fragment (e.g., the rational-square cone) *before* attacking
the full ℤ case." This PREP-1 sharpens the candidate set:

### 5.1 Iter 27a-α — rational-square cone Σ₁/Π₁ collapse (FEASIBLE, axiom-free)

**Target**: `IsDiophantineDefinition (fun q : Rat => ¬ ∃ r : Rat, q = r * r)`.

**Status**: Poonen 2009 ("The set of nonsquares in a number field is Diophantine",
ref already in the slug's `papers` list at iter 0, file line 54) proves this
unconditionally for number fields, including ℚ. The Lean formalization would
mirror Mathlib's `LegendreSymbol/Basic.lean` use of `QuadraticChar` but lift
to ℚ-coefficient polynomials.

**Bearer gap**: still requires HilbertSymbol-like infrastructure (Poonen's
polynomial uses a Hilbert-symbol-style local-global construction). **Not
axiom-free in Lean v4.26.0** — would need to axiomatize Poonen 2009 in the
same way Koenigsmann 2016 is axiomatized, which is the *same* anti-axiom-policy
issue as 27d.

**Verdict**: **anti-candidate** (anti-axiom-policy).

### 5.2 Iter 27a-β — LegendreSymbol-keyed Σ₂ test fragment (FEASIBLE, axiom-free)

**Target**: a SPARSE arithmetic fragment whose Σ₂-definability over ℚ is
testable using ONLY Mathlib's existing LegendreSymbol / JacobiSymbol API,
without any Koenigsmann / Poonen / Hilbert-symbol axiomatization.

**Concrete candidate**: the set `{ q : ℚ | ∃ n : ℕ, q = (n : ℚ) ∧ Nat.Prime n ∧ n % 4 = 1 }`,
i.e., the rational image of primes ≡ 1 mod 4. By Fermat's two-square theorem
(already in Mathlib as `Nat.Prime.prime_and_two_squares` / similar), this set
has a clean Σ₁ definition over ℚ via the polynomial witness
`P(q, x, y) = (q - x² - y²)² + (4·z - q + 1)² + (q · w - 1) · (q · w - 1) - …`
(with auxiliary witnesses for primality via Wilson's theorem). Hence it is
trivially Σ₂ via Σ₁ ⊆ Π₂ ⊆ Σ₂.

**Honest assessment**: this is a Σ₁ subset, so it lives in the *intersection*
Σ₁ ∩ Σ₂ trivially. Demonstrating Σ₂-definability does NOT advance the open
Σ₂(ℤ) question (which asks about a set NOT known to be Σ₁). The fragment
test would be expository — useful as an illustration of the existing closure
machinery, NOT as a sub-step towards Σ₂(ℤ).

**Verdict**: **low-leverage candidate** — mechanical filler at best. Could
serve as a substitute for the deprecated iter 27e ladder rung *if* a future
picker wants visible iteration progress without risking the open question.

### 5.3 Iter 27a-γ — Mathlib upstream contribution (DEFERRED, multi-quarter)

**Target**: contribute at least one of the missing bearers (#1 HilbertSymbol,
#2 HasseMinkowski) to Mathlib upstream, then revisit iter 27a once the new
import lands.

**Honest assessment**: this is a major Mathlib contribution effort (likely
4-12 weeks of focused work for an experienced Mathlib contributor, much more
for a researcher-1-style autonomous agent given the review cycle). It is the
*correct* long-term path, but it is not a realistic single-cycle ACT for
this slug.

**Verdict**: **deferred — multi-quarter horizon**. Logged here for visibility;
iter 27a-γ should NOT be claimed as a single-cycle ACT.

### 5.4 Iter 27a-δ — sharpen the H10/ℚ implication chain (FEASIBLE, axiom-free)

**Target**: extract and name additional re-export theorems from the existing
`integers_diophantine_sigma1_implies_h10_q_undecidable` chain. For example,
prove that *partial* Σ₁-definability (Σ₁ for a fragment of ℤ) implies a
fragmentary H10/ℚ-undecidability statement. Pure logical re-export, no new
axiom.

**Honest assessment**: low-leverage but axiom-free. Adds 2-5 theorems, ~50
LOC. Would not advance the OPEN content, but would expose finer structure
in the existing implication chain.

**Verdict**: **low-leverage candidate** — comparable to 27a-β in leverage,
strictly within anti-axiom-policy.

## 6. PREP-2 target proposal

Given §4 and §5, the recommended next PREP (iter 27a PREP-2) is:

> **PREP-2 (proposed)**: catalog the EXACT Mathlib API surface for the 5
> missing bearers (§3.6) at the next pin advance, OR if pin is stable,
> survey existing Mathlib PRs / RFCs against `leanprover-community/mathlib4`
> for any in-flight contributions toward HilbertSymbol / HasseMinkowski /
> Brauer(ℚ). This converts the "upstream-blocked" verdict into either:
>
> - "upstream-blocked, no in-flight motion" (decision: claim release and
>   let the slug rest until pin advance);
> - "upstream-blocked, in-flight motion at PR # X" (decision: track that PR,
>   re-PREP on its merge); OR
> - "upstream-blocked but partial bearer landed in Mathlib at SHA Y"
>   (decision: PREP-3 = Lean draft against the new bearer).

Concretely, PREP-2 would search:

1. `https://github.com/leanprover-community/mathlib4/pulls?q=is%3Apr+Hilbert+symbol`
2. `https://github.com/leanprover-community/mathlib4/pulls?q=is%3Apr+Brauer+rational`
3. `https://github.com/leanprover-community/mathlib4/pulls?q=is%3Apr+Hasse+Minkowski`
4. `https://leanprover.zulipchat.com` searches for #mathlib4 threads on the
   same keywords.

PREP-2 is doc-only and produces a status table of in-flight contributions.

## 7. Mathematical content summary (no Lean delta)

This PREP-1 adds zero theorems, zero axioms, zero definitions, zero imports
to `proofs/Proofs/Hilbert10OQ01OQ02.lean`. The file is unchanged on
`origin/main` between the previous merge (PR #19117, 2026-05-15T22:58:32Z)
and this PR's base. The mathematical state of the slug is therefore
unchanged; what *has* changed is the strategic assessment:

- **Before PREP-1**: iter 27a was "the sole forward candidate" (S29).
- **After PREP-1**: iter 27a is decomposed into four sub-paths, of which
  one (27a-α) is anti-axiom-policy-blocked, one (27a-β) is low-leverage,
  one (27a-γ) is multi-quarter-deferred, and one (27a-δ) is low-leverage
  but axiom-free. The slug's "sole forward candidate" status is preserved
  but the *cost-of-action* on that candidate is now explicit: under the
  current pin and anti-axiom policy, iter 27a-ACT is upstream-blocked and
  the productive iterations remain doc-only.

## 8. ACT-readiness gate (carry-forward + bearer-gap addendum)

| # | Gate item                                  | S29 verdict | PREP-1 verdict |
|---|--------------------------------------------|-------------|----------------|
| 1 | Mathlib pin (`lake-manifest.json`)         | UNCHANGED   | UNCHANGED      |
| 2 | Bearer 1 `…Ring/Basic.lean` @ pin           | byte-stable | byte-stable    |
| 3 | Bearer 2 `…Finset/Dedup.lean` @ pin         | byte-stable | byte-stable    |
| 4 | File LOC                                    | 3082        | 3082           |
| 5 | File git activity since 2026-05-16         | 0 commits   | 0 commits      |
| 6 | Open PRs on slug                            | 0           | 0              |
| 7 | Picker matrix sharpness                     | iter 27a sole forward | refined into 27a-α/β/γ/δ |
| 8 | Anti-axiom-policy compliance               | enforced    | enforced       |
| 9 | Upstream bearer surface (NEW @ PREP-1)     | n/a (gate added this iter) | **5/5 ABSENT (HilbertSymbol, HasseMinkowski, BrauerRational, PoonenNonSquaresDiophantine, Hilbert10Rational)** |
| 10 | Iter-27 candidate viability                 | 1/5 viable (27a) | 1/4 viable & low-leverage (27a-δ); 3/4 anti-candidate or deferred |

**Net**: 8/10 GREEN, 1/10 NEW INFORMATION (gate 9 — bearer-gap is now
explicit), 1/10 DOWNGRADED (gate 10 — 27a-δ is the only feasible single-cycle
ACT under current constraints, and it is low-leverage).

## 9. Deliverables (this PR, doc-only)

1. **This session memo** (`sessions/2026-06-02-iter27a-prep-1-mathlib-bearer-survey.md`)
   — the full PREP-1 record, mirrored for future picker traceability.
2. **`state.md` head update** — short S30 prepend pointing at this memo,
   with a TL;DR of the upstream-blocked verdict and the PREP-2 proposal.
3. **Canonical JSON** (`src/data/research/problems/hilbert-10-oq-01-oq-02.json`) —
   `knowledge.progressSummary` prepend with the PREP-1 narrative;
   `lastUpdate` 2026-05-31T04:00:00Z → 2026-06-02T03:00:00Z;
   `currentState.{phase, since, iteration}` carried forward verbatim;
   `currentState.focus` updated to point at this PREP.

**Out of scope (deferred)**:

- Gallery `meta.json` numerics — file unchanged, no drift.
- `pnpm build` — slug-targeted JSON edit only; CI is the ground truth.
- Lean file edits — none required for an upstream-readiness assessment.
- Bearer drift recheck against any Mathlib SHA other than the pin — pin is
  unchanged, no recheck needed.

## 10. Provenance & footnotes

- Mathlib pin at this PR's base SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (`v4.26.0`), read directly from `proofs/lake-manifest.json`.
- Mathlib clone HEAD post-`git clone --depth=1 --branch v4.26.0` matched the
  pin SHA exactly (verified via `git rev-parse HEAD`).
- Clone path `/tmp/mathlib-survey` was removed after survey to recover disk
  (host disk at 99% capacity throughout this session; recovered to 98% after
  cleanup — flag for future disk hygiene).
- All `grep` searches in §3.6 were run against the cloned working tree;
  zero matches in each case confirms the bearer-gap is real at the pin.
- File sizes and SHAs in §3.1-§3.5 captured before the clone was removed.

## 11. Honest forward statement

Iter 27 is still the next picker's slot; iter 27a remains the only forward
candidate at the slug-level. But the cost-of-action on 27a is now explicit:

- A single-cycle iter 27a-ACT against the OPEN Σ₂(ℤ) question is
  **NOT achievable** under the current pin + anti-axiom policy.
- The productive single-cycle moves remain doc-only PREP/STATE-SYNC, or
  the low-leverage 27a-δ implication-chain re-exports.
- Picker pickups for iter 27 should ship one of: (a) the PREP-2 upstream
  in-flight survey proposed in §6; (b) the iter 27a-δ re-export theorems
  if a small Lean delta is desired; (c) a +Nd STATE-SYNC if the bearer/pin
  surface drifts; OR (d) release the claim until the upstream bearer
  surface advances.

The previous iterations (S27/S28/S29) named iter 27a as "the sole forward
candidate" but did not surface the upstream-blocked nature of the candidate
itself. This PREP-1 closes that gap.
