# Problem: Discharge the Erdős–Szekeres existence axiom (pigeonhole over pairs)

**Slug**: erdos-szekeres-oq-01
**Created**: 2026-04-05T19:30:46-07:00
**Status**: Active — ACT in progress (Approach B, #22772); Approach A surveyed 2026-06-13
**Source**: user-request

## Problem Statement

### Formal Statement

The gallery parent `proofs/Proofs/ErdosSzekeres.lean` states the existence direction
as an **axiom**:

```lean
axiom erdos_szekeres_existence_axiom {α : Type*} [LinearOrder α] {n : ℕ}
    (f : Sequence α n) (hf : Injective f) (r s : ℕ) (hr : r ≥ 1) (hs : s ≥ 1)
    (hn : n ≥ (r - 1) * (s - 1) + 1) :
    (∃ sub : IncreasingSubseq f r, True) ∨ (∃ sub : DecreasingSubseq f s, True)
```

where `Sequence α n := Fin n → α` and `IncreasingSubseq f k` is a structure carrying
`positions : Fin k → Fin n` with `StrictMono positions` and `StrictMono (f ∘ positions)`
(`DecreasingSubseq` likewise with `StrictAnti (f ∘ positions)`).

**Goal**: replace `erdos_szekeres_existence_axiom` with a proved `theorem`, reducing
the parent's axiom count from 2 to 1.

### Plain Language

The parent gallery proof "Erdős–Szekeres Theorem" (Wiedijk #73) currently *assumes*
the core existence statement (any sequence of `(r-1)(s-1)+1` distinct elements has an
increasing subsequence of length `r` or a decreasing one of length `s`) as an axiom,
deferring the pigeonhole-over-pairs argument. This problem asks to actually prove it.

### Why This Matters

Removing an axiom from a Wiedijk-100 gallery entry upgrades it from `axiomatized`
toward `verified`. The existence direction is the mathematical heart of the theorem;
axiomatizing it is the weakest part of the current formalization.

## Known Results

### What's Already Proven

- **In this slug (origin/main, Approach B, #22772)**: `maxIncLen` / `maxDecLen` (via
  `Nat.findGreatest`), singleton witnesses `hasIncreasingEndingAt_one` /
  `hasDecreasingEndingAt_one`, and lower bounds `one_le_maxIncLen` / `one_le_maxDecLen`.
  Parent file 281 → 344 LOC, Docker-verified, axiom count still 2. The remaining burden
  is the position→pair injectivity (the `maxIncLen_lt_of_lt` extension lemma).
- **`Theorems100.erdos_szekeres`** — Mathlib **Archive**
  (`Archive/Wiedijk100Theorems/AscendingDescendingSequences.lean`). The full
  Erdős–Szekeres theorem, *proved* (no axioms), via the same pigeonhole-on-pairs argument:
  ```lean
  theorem erdos_szekeres {α : Type*} {β : Type*} [Fintype α]
      [LinearOrder α] [LinearOrder β] {r s : ℕ} {f : α → β}
      (hn : r * s < Fintype.card α) (hf : Function.Injective f) :
      (∃ t : Finset α, r < t.card ∧ StrictMonoOn f ↑t) ∨
      (∃ t : Finset α, s < t.card ∧ StrictAntiOn f ↑t)
  ```
- **The Archive is importable in this project**: `proofs/Proofs/BallotProblem.lean`
  already does `import Archive.Wiedijk100Theorems.BallotProblem`, so
  `import Archive.Wiedijk100Theorems.AscendingDescendingSequences` is available.
- `Finset.orderEmbOfCardLe (s : Finset α) (h : k ≤ s.card) : Fin k ↪o α` — order
  embedding whose image is contained in `s` (Mathlib `Data/Finset/Sort.lean`). Bridges
  Archive's `Finset` conclusion to the parent's `Fin k → Fin n` structure.

### What's Still Open

- **Approach B**: the position→pair injectivity (`maxIncLen_lt_of_lt`) + the final
  pigeonhole assembly.
- **Approach A**: the type/structure *adaptation* from `Theorems100.erdos_szekeres`
  (`f : α → β`, `Fintype α`, `Finset α` conclusion) to the parent's `Sequence α n` /
  `IncreasingSubseq` structure form. No new mathematics — pure Lean plumbing.

### Our Goal

Discharge `erdos_szekeres_existence_axiom` only. The second axiom
`erdos_szekeres_tight_axiom` (sharpness of the bound) is **out of scope** for this slug.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-szekeres` | Parent — the axiom we are discharging | pigeonhole, order theory |
| `ballot-problem` | Precedent for importing `Archive.Wiedijk100Theorems.*` | Archive reuse |
| `pigeonhole-principle` | Underlying technique of both approaches | Finset cardinality |

## Initial Thoughts

### Potential Approaches

1. **Approach B (ACTIVE, in progress #22772): bottom-up pair tracking.**
   Hand-build `maxIncLen`/`maxDecLen`, prove the extension lemma `maxIncLen_lt_of_lt`
   (the position→pair map is injective), then pigeonhole on the `(r-1)×(s-1)` grid.
   - Status: ACT-1 done (defs + singleton witnesses + lower bounds, Docker-verified).
   - Risk: ~150+ LOC total; the injectivity lemma is the main remaining effort.

2. **Approach A (SURVEYED 2026-06-13, candidate to supersede B): import the Archive.**
   - Instantiate `Theorems100.erdos_szekeres` with `α := Fin n`, `β := α`, and the
     **index shift** `r ↦ r-1`, `s ↦ s-1`. Then Archive's hypothesis becomes
     `(r-1)*(s-1) < Fintype.card (Fin n) = n`, i.e. exactly the parent's
     `n ≥ (r-1)*(s-1)+1`. Archive's conclusion becomes `t.card ≥ r`.
   - Convert each disjunct: from `t : Finset (Fin n)` with `r ≤ t.card` and
     `StrictMonoOn f ↑t`, build `positions := Finset.orderEmbOfCardLe t (h : r ≤ t.card)`.
     `positions` is `StrictMono` (order embedding) and lands in `↑t`, so
     `StrictMono (f ∘ positions)` follows from `StrictMonoOn.comp_strictMono` plus the
     range-⊆-`t` fact (`Finset.range_orderEmbOfCardLe` / membership lemma).
   - Why it may be better: reuses ~80 LOC of already-verified Mathlib; the only work is
     ~30–50 LOC of structure repackaging, vs Approach B's full bottom-up build.
   - Risk: the order-embedding range/membership lemma name needs build-time confirmation;
     minor `Fintype.card_fin` and `r-1 < c ↔ r ≤ c` bookkeeping.

   **Recommendation**: before investing further in Approach B's ACT-2, spend one ACT
   session prototyping Approach A — if the import resolves and the conversion typechecks,
   it discharges the axiom with far less code.

### Key Difficulties

- (Approach A) the index/off-by-one bridge between "subsequence length `r`" (parent) and
  "`r < card`, i.e. length `> r`" (Archive). Resolved cleanly by the `r ↦ r-1` shift.
- (Approach A) converting a `StrictMonoOn`-on-a-`Finset` witness into a
  `StrictMono (Fin r → Fin n)` witness — handled by `Finset.orderEmbOfCardLe`.
- (Approach B) the injectivity of the position→pair map.

### What Would a Proof Need?

- (A) `Theorems100.erdos_szekeres` (import the Archive) + `Finset.orderEmbOfCardLe`
  + `StrictMonoOn.comp_strictMono` + `Fintype.card_fin` + `omega`.
- (B) `maxIncLen_lt_of_lt` extension lemma + the existing `maxIncLen`/`maxDecLen` scaffold.

## Tractability Assessment

**Difficulty**: Low–Medium (Approach A); Medium (Approach B).

**Justification**:
- The hard mathematics is **already in Mathlib's Archive** and importable here — Approach A
  reduces the task to type/structure adaptation comparable to other
  `Archive.Wiedijk100Theorems.*` reuse PRs in this repo (e.g. ballot-problem).

**Estimated Effort**:
- Exploration: done (this ORIENT survey of Approach A).
- If tractable (Approach A): ~1 ACT session once Docker build infra is available.
- Blocker: discharge is build-gated; ACT should wait for Docker (blackout 2026-06-13).

## References

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/Archive/Wiedijk100Theorems/AscendingDescendingSequences.html — `Theorems100.erdos_szekeres`
- https://en.wikipedia.org/wiki/Erd%C5%91s%E2%80%93Szekeres_theorem — statement & history

### Mathlib
- `Archive.Wiedijk100Theorems.AscendingDescendingSequences` — proved Erdős–Szekeres
- `Mathlib.Data.Finset.Sort` — `Finset.orderEmbOfCardLe`
- `Mathlib.Order.Monotone.Basic` — `StrictMonoOn.comp_strictMono`

## Metadata

```yaml
tags:
  - combinatorics
  - order-theory
  - pigeonhole
related_proofs:
  - erdos-szekeres
  - ballot-problem
  - pigeonhole-principle
difficulty: low-medium
source: user-request
created: 2026-04-05T19:30:46-07:00
```

**Significance**: 6/10
**Tractability**: 8/10 (raised from 7 — Mathlib Archive already proves the core; importable here)
