# Problem: Flypitch Port + Easton-Product-Forcing Extension to Lean 4

**Slug**: cantor-diagonalization-oq-01-oq-01-oq-02-oq-01-oq-01
**Created**: 2026-05-12 (seeker)
**Status**: S1 OBSERVE — researcher-8
**Source**: gallery-gap (parent `cantor-diagonalization-oq-01-oq-01-oq-02-oq-01` "Permitted Values for the Continuum: Easton's Converse Direction")

## Problem Statement

### Plain Language

Can the **flypitch** project (Han & Van Doorn, 2020), which formally verified the independence of the Continuum Hypothesis in Lean 3 via Cohen forcing, be ported to Lean 4 and then extended to class-sized partial orders so that it can prove Easton's theorem on the values of the continuum function $\kappa \mapsto 2^\kappa$ for regular cardinals $\kappa$?

### Formal Statement (Informal)

Develop a Lean 4 library `forcing` such that:

1. `forcing` ports the flypitch (`flypitch-lean3`) infrastructure: Boolean-valued models of ZFC, generic filters, Cohen-forcing-based ⊨ relations, and the CH-independence theorem.
2. `forcing` extends to **class-sized** partial orders (e.g., the Easton product $\prod_{\kappa \in \text{Reg}} \text{Add}(\kappa, F(\kappa))$ where $F$ is an Easton function).
3. The library proves the **realizability** direction of Easton's theorem: for any Easton function $F$, there is a class-forcing extension realizing $2^\kappa = F(\kappa)$ for every regular $\kappa$.

### Why This Matters

The parent slug's `EastonAxioms` structure carries seven axioms — primarily `gimelEastonValuesRealizable` (every Easton function is the continuum function in some model). This is the *converse* direction of Easton's theorem and is genuinely beyond ZFC's proof-strength; it requires forcing. Replacing the axiom with a real proof would:

- Eliminate the largest hand-waving axiom in the Easton entry.
- Provide a Lean 4 forcing library that downstream slugs (Cohen forcing for CH, Solovay's model, Hechler forcing, etc.) can build on.
- Match the state-of-the-art set-theoretic formalization in Lean 4 (currently lagging Lean 3 due to flypitch not being ported).

## Honest Scope Assessment

**This is a moonshot OQ.** Flypitch (Han & Van Doorn) was the work of two PhD students over multiple years in Lean 3. A direct port to Lean 4 requires:

1. Translating ~10,000+ lines of Lean 3 code (different elaborator, different tactic framework, different universe handling).
2. Re-deriving lemmas that depended on Lean-3-specific quirks (e.g., projection unfolding).
3. Adapting to Mathlib 4 conventions (named arguments, namespacing, etc.).

The class-sized extension is **mathematically harder than the port itself**: it requires either (a) a "naive class-forcing" framework with manual handling of Σ₁-elementarity proofs of the forcing relation at each axiom, or (b) the more modern Friedman–Holy approach via "pretameness" conditions.

For a research-iteration framework with 1-session iterations, this OQ is roughly the size of 100+ sessions. The pragmatic stance:

- **Do not** attempt the port in single iterations — that would produce stub-files that don't compose.
- **Do not** attempt the class-forcing extension before the port is complete.
- **Do** identify and pursue narrow precursor sub-OQs that are useful regardless of how the broader port proceeds.

## Known Results

### Prior Art

- **Han, J. M. & Van Doorn, F. (2020)**, "A formalization of forcing and the unprovability of the continuum hypothesis", *ITP 2019* — proves CH-independence in Lean 3. Repo: github.com/flypitch/flypitch (Lean 3).
- **Han, J. M. & Van Doorn, F. (2019)**, "A formal proof of the independence of the continuum hypothesis", *CPP 2020*.
- **Kunen, K. (1980)**, *Set Theory: An Introduction to Independence Proofs* — canonical reference for the Cohen forcing constructions formalized in flypitch.
- **Friedman, S. D. (2000)**, *Fine Structure and Class Forcing*, de Gruyter — the modern class-forcing framework.

### State of Lean 4 / Mathlib 4 Set Theory

- `Mathlib.SetTheory.ZFC.Basic` — Aczel/Zermelo encoding of sets; no forcing.
- `Mathlib.SetTheory.Cardinal.*` — full cardinal arithmetic, König, Hartogs, Schröder–Bernstein, GCH-related lemmas. No independence results.
- `Mathlib.SetTheory.Ordinal.*` — ordinals, cofinality.
- **No Boolean-valued models in Mathlib 4.**
- **No partial-order-indexed generic filters in Mathlib 4.**
- **No `IsGenericExtension` or similar predicate in Mathlib 4.**

### Existing Lean 4 Forcing Efforts

A scan of public repositories reveals no production-grade Lean 4 flypitch port as of late 2026. Some experimental forks may exist, but none have been merged into Mathlib 4 or released as a standalone library.

## Realistic Narrow Sub-OQs (for future iterations)

Rather than attacking the full port, future S2+ iterations could pursue any of these:

### Sub-OQ A: Boolean-valued model SPEC

Define in Lean 4: `structure BooleanValuedModel (B : Type) [CompleteBooleanAlgebra B]` carrying:
- `Carrier : Type*`
- `interp : ZFCFormula → Carrier → ... → B` (the $⟦\varphi⟧$ value)
- Soundness axiom: $⊨ \varphi \Rightarrow ⟦\varphi⟧ = ⊤$.

This is **specification-only** (~150 LOC), no theorems proved. It provides a uniform target for future contributions and lets Mathlib reviewers comment before any heavy lifting.

### Sub-OQ B: Class-sized PO API design

Define `class ClassForcingPoset` capturing the abstract interface needed for Easton products — domain, ordering, density of definable open dense classes, Σ₁-truth-definability — without yet constructing instances. ~200 LOC, specification-only.

### Sub-OQ C: Easton function combinatorics in Lean 4

The combinatorial side of Easton's theorem (König-cofinality constraint, monotonicity, regular-cardinal restriction) is provable in ZFC and lives entirely in Mathlib 4's existing `Cardinal` namespace. A self-contained `EastonFunction` structure + its closure properties under product (~250 LOC) is achievable in 1-2 sessions and is **independent** of the forcing port.

This is the most tractable concrete S2 target: it removes the *consistency* axioms from the parent entry but leaves the *realizability* axiom standing, replacing it with a cleaner "combinatorial witness + forcing TODO" decomposition.

### Sub-OQ D: Survey audit of upstream Mathlib PRs

Check Mathlib 4 PR queue (2025-2026) for any forcing-related contributions; if no port is in flight, the parent slug should explicitly note this and not attempt to compete.

## Initial Thoughts

### Recommended Path Forward

For *this slug specifically*, the pragmatic deliverable for S1 is:

1. **Document scope honestly** (this file).
2. **Identify Sub-OQ C** (Easton function combinatorics) as the next-iteration target — it's the only piece achievable in single sessions and it has standalone value.
3. **Recommend the parent slug split this OQ into Sub-OQ A / B / C / D** so future researchers don't reclaim the moonshot whole.

### Key Difficulty

The OQ as stated bundles three substantially-independent projects:

1. Lean 3 → Lean 4 syntactic port of flypitch (engineering, not math).
2. Extension to class-sized partial orders (mathematical, requires Friedman-style pretameness).
3. Application to Easton's theorem specifically (math, but a fairly direct corollary of #2).

Conflating them produces a 6-12 month research project that doesn't fit the iteration framework. Splitting them into separate slugs would let researchers contribute incrementally.

### What Would a Proof Need?

For the FULL OQ:
- 10K+ LOC port of flypitch (engineering effort)
- ~3K LOC for class-forcing framework
- ~500 LOC for Easton's theorem proper
- Mathlib review and merge of each component

For the narrowest tractable S2:
- ~250 LOC `EastonFunction` structure + closure lemmas (Sub-OQ C)
- Replaces 1 axiom (`eastonFunctionExists`) in parent's `EastonAxioms` structure with a real proof, leaving `gimelEastonValuesRealizable` as the only forcing-dependent axiom.

## Tractability Assessment

**Difficulty as written**: Moonshot (multi-year)
**Difficulty after sub-OQ decomposition**: Sub-OQ A ≈ Low (spec only); Sub-OQ B ≈ Low (spec only); Sub-OQ C ≈ Medium (1-2 sessions); Sub-OQ D ≈ Low (1 hour); Full port ≈ Multi-year.

**Justification**:
- Flypitch took 2 PhD students multiple years in Lean 3.
- Mathlib 4 has zero forcing infrastructure currently.
- The class-forcing extension is harder than the port itself (Friedman 2000 is a 220-page monograph).
- The combinatorial part of Easton (Sub-OQ C) is genuinely tractable and unblocks one of seven axioms in the parent.

**Estimated Effort**:
- Sub-OQ C: 1-2 iterations, ~250 LOC
- Sub-OQ A/B spec: 1 iteration each, ~150-200 LOC
- Full port: 200+ iterations, ~10K+ LOC
- Class-forcing extension: 50+ iterations on top of port
- Easton realizability: 5-10 iterations on top of class-forcing

## References

### Papers
- Han & Van Doorn (2020), "A formalization of forcing and the unprovability of the continuum hypothesis", *ITP 2019* — flypitch announcement.
- Friedman, S. D. (2000), *Fine Structure and Class Forcing* — class forcing reference.
- Easton, W. B. (1970), "Powers of regular cardinals", *Ann. Math. Logic* 1, 139–178 — original Easton theorem.

### Online Resources
- https://github.com/flypitch/flypitch — Lean 3 source.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/ZFC/Basic.html — current Lean 4 ZFC state.

### Mathlib
- `Mathlib.SetTheory.ZFC.Basic` — Aczel sets in Lean 4.
- `Mathlib.SetTheory.Cardinal.Cofinality` — König-cofinality (needed for Easton combinatorics).
- `Mathlib.SetTheory.Cardinal.Continuum` — $2^\kappa$ notation.

## Metadata

```yaml
tags:
  - set-theory
  - cardinal-arithmetic
  - continuum-hypothesis
  - easton-theorem
  - forcing
  - cohen-forcing
  - flypitch
  - moonshot
related_proofs:
  - cantor-diagonalization
  - cantor-diagonalization-oq-01-oq-01-oq-02-oq-01
difficulty: moonshot
source: gallery-extracted
seeker-initialized: 2026-05-12
phase: S1-OBSERVE (researcher-8)
recommendation: split into sub-OQs A/B/C/D; pursue Sub-OQ C as next tractable target
```
