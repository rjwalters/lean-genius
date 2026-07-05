# Knowledge Base: algebraic-numbers-countable-oq-02-oq-03-oq-02-oq-01

**Problem**: Dense Countable Sets are Fσ but not Gδ in Perfect Polish Spaces

**Goal**: State and prove `denseCountable_isFσ_not_isGδ` — in a nonempty perfect Polish (or
perfect + T1 + Baire) space, a countable dense set is `Fσ` and not `Gδ` — then recover `ℚ ⊆ ℝ`
and the algebraic reals as instances.

---

## Problem Understanding

The parent chain already contains the complete mathematics; this problem is a **consolidation /
abstraction** task, not new theory. Being honest about significance: the result is routine given
the two parents below. Its value is (a) one citable uniform lemma over *all* perfect Polish
spaces, (b) the previously-unstated `ℚ`-not-`Gδ` instance, (c) removing duplication.

---

## Insights

### The proof is a ~6-line assembly of already-compiling lemmas

Both engines were stated **abstractly** (for arbitrary `X`) by the parents, so the generalization
is nearly free:

- **Fσ side** — `AlgebraicRealsMeagerDenseGDeltaOQ01.isFσ_of_countable`
  `{X} [TopologicalSpace X] [T1Space X] {s} (hs : s.Countable) : IsFσ s`
  (`IsFσ` is a *local* def in that file: `∃ T : Set (Set X), (∀ t ∈ T, IsClosed t) ∧ T.Countable ∧ s = ⋃₀ T`.
  Mathlib v4.26.0 has **no** `IsFσ` predicate — only `IsGδ`. Confirmed by grep across the corpus.)
  Density is NOT needed for the Fσ half — countability + T1 suffice (union of closed singletons).

- **not-Gδ side** — two lemmas from `AlgebraicNumbersCountableOQ02OQ03OQ02`:
  - `compl_countable_isDenseGδ {X} [TopologicalSpace X] [T1Space X] [PerfectSpace X] [BaireSpace X] {s} (hs : s.Countable) : IsGδ sᶜ ∧ Dense sᶜ`
  - `not_isGδ_of_dense_of_disjoint_denseGδ {X} [TopologicalSpace X] [BaireSpace X] [Nonempty X] {s t} (hsd : Dense s) (hsg : IsGδ s) (htg : IsGδ t) (htd : Dense t) (hdisj : Disjoint s t) : False`

  Assemble with `s := D`, `t := Dᶜ`, `hdisj := disjoint_compl_right`. Perfectness enters only via
  `compl_countable_isDenseGδ` (singletons nowhere dense ⇒ `D` meagre ⇒ `Dᶜ` residual = dense).

### Minimal hypotheses

`[TopologicalSpace X] [T1Space X] [PerfectSpace X] [BaireSpace X] [Nonempty X]`. This is strictly
more general than "perfect Polish": a perfect Polish space (nonempty complete separable metric,
no isolated points) supplies all four instances (metric ⇒ T1; complete metric ⇒ BaireSpace;
perfect ⇒ PerfectSpace). Stating with the four typeclasses avoids depending on whether
`PolishSpace`'s `BaireSpace` instance fires and instantly covers `ℝ`, `ℝⁿ`, Cantor space `2^ℕ`,
Baire space `ℕ^ℕ`.

### The `ℚ`-not-Gδ corollary is new

The parents proved the algebraic-reals case but never `ℚ` itself. `Set.range ((↑):ℚ→ℝ)` is
countable (`Set.countable_range`, `ℚ` is `Countable`) and dense (`Rat.denseRange_cast`, whose
type `DenseRange` is defeq `Dense (range …)`), giving the classical "ℚ is not Gδ in ℝ" as the
`X := ℝ` instance.

---

## Proof (written, BUILD-UNVERIFIED)

Full file: `lean/DenseCountableFsigmaNotGdelta.lean`. Core:

```lean
theorem denseCountable_isFσ_not_isGδ {X : Type*} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] [BaireSpace X] [Nonempty X] {D : Set X}
    (hcount : D.Countable) (hdense : Dense D) : IsFσ D ∧ ¬ IsGδ D := by
  refine ⟨isFσ_of_countable hcount, fun hGδ => ?_⟩
  obtain ⟨hgδc, hdc⟩ := compl_countable_isDenseGδ hcount
  exact not_isGδ_of_dense_of_disjoint_denseGδ hdense hGδ hgδc hdc disjoint_compl_right
```

Plus `rat_not_isGδ` and `algebraicReals_not_isGδ` (the parent's headline) as corollaries.

---

## Dead Ends / Risks (build-unverified items to confirm on recovery)

1. `open Namespace (IsFσ isFσ_of_countable)` selective-open of a `def` + theorem — standard Lean 4,
   but confirm no name clash with any Mathlib `IsFσ` introduced after v4.26.0.
2. `Rat.denseRange_cast` passed where `Dense D` is expected relies on `DenseRange f = Dense (range f)`
   being definitional. If elaboration balks, replace with `(Rat.denseRange_cast (𝕜 := ℝ)).dense`
   or an explicit `by exact`.
3. Confirm `PerfectSpace ℝ` / `BaireSpace ℝ` instances resolve at the `ℝ` corollaries (they must —
   the parent `algebraicReals_isMeagre` already applied `countable_isMeagre` at `X := ℝ`, which
   needs `[PerfectSpace ℝ]`).

None of these is a mathematical gap; all are surface Lean-elaboration checks.

---

## Mathlib Gaps

- **No `IsFσ` predicate in Mathlib v4.26.0** (only `IsGδ`). The corpus works around it with a local
  `def IsFσ` + `isFσ_iff_isGδ_compl` duality (`AlgebraicRealsMeagerDenseGDeltaOQ01`). This is the
  natural home for an eventual upstream `IsFσ` contribution (def + De Morgan duality +
  `isFσ_of_countable`), which would generalize this whole gallery family.

---

## Next Steps

1. **On Docker/Aristotle recovery**: move `lean/DenseCountableFsigmaNotGdelta.lean` → `proofs/Proofs/`,
   add its import to `proofs/Proofs.lean`, run `./proofs/scripts/docker-build.sh
   Proofs.DenseCountableFsigmaNotGdelta`. Fix any of the 3 surface risks above if they surface.
2. Verify `#print axioms` shows only foundational axioms (expect `verified` / `original`).
3. Create gallery data `src/data/proofs/dense-countable-fsigma-not-gdelta/` (meta.json,
   annotations.json, index.ts); mark `status: verified`, cross-reference the two parents and the
   `algebraic-reals-meager` family.
4. Optional follow-up (only if strong): upstream an `IsFσ` predicate to Mathlib, or state the dual
   "dense-Gδ complement of a dense countable set is not Fσ" abstractly (parent has the concrete
   `transcendentalReals_not_isFσ`).

---

## Session 2026-07-04 (Session 1) — ORIENT/ACT (proof written, build blocked)

**Mode**: FRESH
**Outcome**: progress (complete proof written; build-unverified due to dual-tool blackout)

### What I Did
- Session preamble: confirmed Aristotle 404 ("Resource not found") and Docker containerd blob
  I/O error persist — no proof-checking path available this session.
- Surveyed the parent chain and found ALL ingredients already proven and compiling:
  parent `…OQ02OQ03OQ02` (the two abstract Baire engines) and sibling `…MeagerDenseGDeltaOQ01`
  (the `IsFσ` def + `isFσ_of_countable`).
- Wrote the complete abstraction `denseCountable_isFσ_not_isGδ` + `rat_not_isGδ` +
  `algebraicReals_not_isGδ` as `lean/DenseCountableFsigmaNotGdelta.lean` (scratch, not in
  `Proofs/` to avoid breaking the globbed build with an unverified file).

### Key Findings
- The generalization is a ~6-line mechanical assembly; the parents already stated both engines
  for arbitrary `X`. Honest significance: consolidation, not new mathematics.
- `ℚ`-not-`Gδ` in `ℝ` is a genuinely new instance the parents skipped.
- Mathlib still lacks an `IsFσ` predicate (v4.26.0) — the recurring gap in this family.

### Files Modified
- `research/problems/…/lean/DenseCountableFsigmaNotGdelta.lean` (created — scratch proof)
- `research/problems/…/knowledge.md` (this file)
- `research/problems/…/state.md` (phase → ACT)

### Next Steps
Drop the scratch file into `Proofs/`, build once on Docker recovery, ship gallery entry. See
"Next Steps" above.
