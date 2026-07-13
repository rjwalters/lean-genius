# Mathlib Prerequisites Scoping: Class Field Towers and Golod–Shafarevich

**Issue:** [#20577](https://github.com/rjwalters/lean-genius/issues/20577) (follow-up to [#20516](https://github.com/rjwalters/lean-genius/issues/20516); companion to [#20576](https://github.com/rjwalters/lean-genius/issues/20576))
**Mathlib version surveyed:** `v4.26.0` (rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, the pinned version in this repo's `proofs/lake-manifest.json`)
**Date:** 2026-06-08
**Author:** Loom Builder (automated scoping)

## Purpose

The OpenAI 2026-05-20 construction reportedly disproving Erdős's planar unit-distance conjecture relies on an infinite class field tower over an imaginary quadratic field, whose infinitude is guaranteed by the Golod–Shafarevich inequality applied to the ℓ-rank of the class group. Formalizing this construction in Lean 4 / Mathlib requires a tower of infrastructure ranging from elementary (number fields, rings of integers) to advanced (Artin reciprocity, pro-ℓ Golod–Shafarevich). This document audits the state of each prerequisite in the pinned Mathlib version and estimates the effort to close any gaps.

## Audit Methodology

For each of the seven items in the issue scope, this audit:

1. Queries the Mathlib4 v4.26.0 source tree via GitHub API (`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`) for the existence of files matching the standard naming convention.
2. Runs targeted code searches (`gh api search/code`) for key identifiers (`HilbertClassField`, `ArtinReciprocity`, `IdeleClassGroup`, `Golod`, `Shafarevich`, `ClassFieldTower`).
3. Cross-references the Mathlib `docs/1000.yaml` "1000 theorems" tracker for explicitly catalogued gaps.

Search results that returned zero hits in the `Mathlib/` source subtree (with hits only in `docs/1000.yaml` — the open-problems tracker) are treated as evidence of absence.

## State legend

- **complete**: definitions, key theorems, and standard API present and used elsewhere in Mathlib.
- **partial**: foundational definitions present; specific lemmas needed for the unit-distance construction are missing or require an adapter.
- **missing**: no recognizable infrastructure under any standard naming convention.
- **out-of-scope**: not strictly needed for the construction.

## Audit Table

| # | Topic | Mathlib path(s) | State | Missing lemmas / Notes | Effort estimate |
|---|-------|-----------------|-------|------------------------|-----------------|
| 1 | NumberField / RingOfIntegers | `Mathlib/NumberTheory/NumberField/Basic.lean`, `Mathlib/NumberTheory/NumberField/Ideal.lean`, `Mathlib/NumberTheory/NumberField/Norm.lean` | **complete** | `NumberField`, `RingOfIntegers`, the integral closure characterization, and the standard `IsIntegralClosure` API are all present. | n/a |
| 2 | Class group (incl. ℓ-torsion) | `Mathlib/RingTheory/ClassGroup.lean`, `Mathlib/RingTheory/ClassGroup/Basic.lean`, `Mathlib/RingTheory/ClassGroup/ExtendedHom.lean`, `Mathlib/NumberTheory/ClassNumber/{Finite,FunctionField,AdmissibleAbs,AdmissibleAbsoluteValue,AdmissibleCardPowDegree}.lean`, `Mathlib/NumberTheory/NumberField/ClassNumber.lean`, `Mathlib/RingTheory/UniqueFactorizationDomain/ClassGroup.lean`, `Mathlib/RingTheory/PicardGroup.lean` | **partial** | `ClassGroup K` exists; finiteness for `RingOfIntegers` of a `NumberField` is proved (`ClassGroup.fintype` via `ClassNumber.Finite`). ℓ-torsion subgroups exist generically (`AddCommGroup.torsionBy`, `Submonoid.torsion` in `Mathlib/GroupTheory/Torsion.lean`) but the ℓ-rank of `ClassGroup (𝓞 K)` as a `(ZMod ℓ)`-vector space and lemmas relating it to ramification (needed for explicit Golod–Shafarevich input) require a small adapter file. | 0.5 person-week for the ℓ-rank adapter and standard isomorphisms (`ClassGroup.torsionBy ℓ ≃ ...`). |
| 3 | Class field theory (Hilbert class fields, idele class groups, Artin reciprocity) | **(no `Mathlib/NumberTheory/ClassFieldTheory/*` directory).** Adele ring exists at `Mathlib/NumberTheory/NumberField/AdeleRing.lean`, `Mathlib/NumberTheory/NumberField/InfiniteAdeleRing.lean`, `Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean`. Local field foundations at `Mathlib/NumberTheory/LocalField/Basic.lean`. | **missing** (with partial adelic foundations) | Searches for `HilbertClassField`, `ArtinReciprocity`, `IdeleClassGroup` returned zero results in the Mathlib source. Golod–Shafarevich is listed in `docs/1000.yaml` as `Q17018210` (1000-theorems tracker entry — i.e., unformalized). The adele ring is present but the idele class group, its topology, and the Artin reciprocity map are not. A Lean-Together / FLT project may be working on subsets of this — see "Open Mathlib PRs" below. | **Large.** Full global Artin reciprocity is the standard Mathlib "moonshot" — order of **2–5 person-years** for a full formalization. For the unit-distance application, only the *existence* of the Hilbert class field with `Gal(H/K) ≅ ClassGroup K` is strictly required; a *black-box axiomatization* of this isomorphism (instead of a full proof) is a viable shortcut at **2–4 person-weeks**. |
| 4 | Class field towers (infinitude criteria) | **(absent)** | **missing** | No `ClassFieldTower` identifier in Mathlib. Depends on item 3 for the recursive construction `K ↦ HilbertClassField K`. The infinitude criterion (Golod–Shafarevich applied to ℓ-rank vs. discriminant) depends on item 5. | **1–2 person-weeks** once items 3 and 5 are available (the definition is a simple `Nat`-indexed iteration; infinitude follows from item 5). |
| 5 | Golod–Shafarevich theorem | **(absent)** | **missing** | Search for `Golod` and `Shafarevich` returned zero results in `Mathlib/`. Only hit was `docs/1000.yaml` (`Q17018210: title: Golod–Shafarevich theorem`) confirming Mathlib catalogues this as unformalized. Required infrastructure: (a) pro-ℓ groups (filtered colimits of finite ℓ-groups, generators-and-relations, Frattini quotient); (b) the inequality $r(G) \geq d(G)^2/4$ on a finitely presented pro-ℓ group; (c) the translation to number-theoretic terms ($\ell$-rank of class group vs. number of generators of the maximal pro-ℓ unramified extension). | **Large.** Pro-ℓ group theory: ~1500–2500 Lean lines, **3–6 person-months**. The Golod–Shafarevich inequality itself: ~500–1000 Lean lines, **1–2 person-months** on top of pro-ℓ foundations. Number-theoretic translation: **2–4 person-weeks**. Total: **6–10 person-months**. |
| 6 | Dirichlet's unit theorem | `Mathlib/NumberTheory/NumberField/Units/Basic.lean`, `Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.lean`, `Mathlib/NumberTheory/NumberField/Units/Regulator.lean` | **complete** | Dirichlet's unit theorem (rank formula `r₁ + r₂ - 1`), the regulator, and fundamental units are all present. `NumberField.Units.rank_modTorsion` (or equivalent) is the standard reference. | n/a |
| 7 | Embeddings / Minkowski | `Mathlib/NumberTheory/NumberField/Basic.lean`, `Mathlib/NumberTheory/NumberField/InfinitePlace/*`, `Mathlib/NumberTheory/NumberField/CanonicalEmbedding/{Basic,ConvexBody,FundamentalCone,NormLeOne,PolarCoord}.lean`, `Mathlib/NumberTheory/NumberField/Discriminant/{Basic,Defs,Different}.lean`, `Mathlib/MeasureTheory/Group/GeometryOfNumbers.lean` (Minkowski's convex body theorem) | **complete** | Complex and real embeddings, the canonical Minkowski embedding into ℝⁿ, convex-body machinery, the discriminant, and Minkowski's lattice-point theorem are all present and well-developed (the recent `NormLeOne` and `PolarCoord` additions show active work). | n/a |

## Summary by State

| State | Items | Total estimated effort |
|-------|-------|------------------------|
| **complete** | 1 (NumberField), 6 (Dirichlet units), 7 (Embeddings/Minkowski) | 0 |
| **partial** | 2 (Class group + ℓ-torsion adapter) | ~0.5 person-week |
| **missing** | 3 (class field theory), 4 (class field towers), 5 (Golod–Shafarevich) | ~6–11 person-months (full path); ~3–6 person-months (axiomatized class field theory + full Golod–Shafarevich); ~1–2 person-months (all-axiomatized "skeleton") |

## Two formalization strategies for #20576

### Strategy A: Full formalization (long-horizon)

Build the entire stack in Mathlib. Total effort: **~6–11 person-months** of concentrated number theory formalization, dominated by global Artin reciprocity (item 3) and Golod–Shafarevich (item 5). Suitable as a multi-year Mathlib contribution program. This would deliver Golod–Shafarevich (`Q17018210` in `docs/1000.yaml`) and significant chunks of global class field theory to Mathlib as side-effects.

### Strategy B: Axiomatized skeleton (recommended near-term)

Following this project's convention for Millennium/conjectural results (see `CLAUDE.md` "Axiom Integrity Policy"):

1. **Axiomatize** the existence of the Hilbert class field tower and the Artin isomorphism `Gal(H/K) ≅ ClassGroup K` as a `structure` (e.g., `ClassFieldTowerAxioms`).
2. **Axiomatize** Golod–Shafarevich as: *if the ℓ-rank of `ClassGroup (𝓞 K)` exceeds $2 + 2\sqrt{r_1 + r_2 + 1}$ (the discriminant-dependent bound), then the ℓ-class field tower is infinite.*
3. **Prove** the OpenAI construction *conditionally* on these axioms. This puts the proof at `status: "axiomatized"`, `badge: "axiom"` in gallery `meta.json`, with `axiomCount` reflecting all structure fields.

Estimated effort: **2–4 person-weeks** for the axiomatized skeleton plus the actual unit-distance combinatorial argument. The conditional theorem is mathematically meaningful (it formally verifies the planar-graph counting step assuming the deep number theory) and provides a target for incremental de-axiomatization as items 3–5 land in Mathlib.

## Open Mathlib PRs (to verify at formalization start time)

This audit could not exhaustively check the Mathlib PR queue because the GitHub search-code API rate-limited mid-audit. The following keyword searches should be re-run when starting work on #20576:

```bash
gh pr list --repo leanprover-community/mathlib4 --search "class field" --state all --limit 30
gh pr list --repo leanprover-community/mathlib4 --search "Hilbert class" --state all --limit 30
gh pr list --repo leanprover-community/mathlib4 --search "Artin reciprocity" --state all --limit 30
gh pr list --repo leanprover-community/mathlib4 --search "idele" --state all --limit 30
gh pr list --repo leanprover-community/mathlib4 --search "Golod" --state all --limit 30
gh pr list --repo leanprover-community/mathlib4 --search "Shafarevich" --state all --limit 30
gh pr list --repo leanprover-community/mathlib4 --search "pro-l group" --state all --limit 30
```

Known communities to monitor:
- **FLT (Fermat's Last Theorem) project** under `https://github.com/ImperialCollegeLondon/FLT` — likely upstreaming idele / Galois cohomology infrastructure that overlaps item 3.
- **Lean Together** workshop output — periodic batches of class field theory PRs.

## Recommended Formalization Order (for #20576)

If pursuing Strategy A or a hybrid:

1. **Item 2 ℓ-rank adapter** (0.5 pw) — small, self-contained, immediately reusable.
2. **Pro-ℓ group theory** (3–6 pm) — prerequisite for item 5 and reusable across number theory.
3. **Golod–Shafarevich inequality** in abstract pro-ℓ form (1–2 pm).
4. **Number-theoretic translation** of GS to class field towers (2–4 pw), using axiomatized item 3.
5. **Item 3 (class field theory)**: full formalization, possibly in coordination with FLT project; or remain axiomatized.

Items 1, 6, 7 require no new work.

## Caveats

- All effort estimates are order-of-magnitude figures based on comparable Mathlib formalizations (Dirichlet's theorem, the proof of Fermat's theorem on sums of two squares). Actual times depend heavily on the formalizer's familiarity with Mathlib's algebraic geometry / number theory APIs.
- The "axiomatized" Strategy B requires careful adherence to this project's axiom integrity policy (`CLAUDE.md`): all axioms (whether `axiom` declarations or structure fields) must be counted in `axiomCount`, and the gallery `status` must be `"axiomatized"`.
- The Golod–Shafarevich inequality has multiple variants. For the unit-distance application, the relevant version is the explicit bound on the ℓ-rank of the class group (e.g., $d_\ell(\mathrm{Cl}_K) > 2 + 2\sqrt{r_1 + r_2 + 1}$ implies the ℓ-class field tower is infinite). The audit estimates assume this variant.

## Conclusion

Mathlib v4.26.0 has **excellent foundations** for the elementary number theory (items 1, 2, 6, 7) but is **missing the deep infrastructure** (items 3, 4, 5) that the OpenAI 2026 unit-distance construction relies on. A near-term Lean formalization (#20576) is feasible via **Strategy B (axiomatized skeleton)** at **2–4 person-weeks**; a fully de-axiomatized formalization is a **multi-year Mathlib contribution program** dominated by global Artin reciprocity and Golod–Shafarevich. The audit recommends Strategy B as the path forward, with the axiomatization carefully delineated so that future Mathlib advances can incrementally remove individual axioms.
