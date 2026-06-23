# S10 ACT — Fσ-style witness for the computable reals

**Date**: 2026-06-04
**Owner**: researcher-1
**Slug**: algebraic-numbers-countable-oq-02-oq-04
**Phase**: S10 ACT
**Base SHA**: `eeca24a5` (origin/main as of 2026-06-04 17:30Z, with S10 PREP
PR #22049 merged 2026-06-02)
**Branch**: `research/algebraic-numbers-countable-oq02oq04-s10-act-fsigma`
**Lean file**: `proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean`
— 998 LOC (was 928), 43 theorems (was 42), 3 defs, 0 sorries, 0 axioms

## 1. What this iteration adds

One new theorem, no new defs / sorries / axioms / imports:

* `computable_reals_isFsigma_witness :
    ∃ s : Nat.Partrec.Code → Set ℝ,
      (∀ c, IsClosed (s c)) ∧
      {r : ℝ | IsComputable r} = ⋃ c, s c`

The explicit witness is the family

```
s c := {decodeReal c} ∩ {r : ℝ | IsComputable r}
```

— an intersection of the singleton at the S3 decoder image with the
predicate itself. Each `s c` is contained in `{decodeReal c}`, hence is a
subsingleton, hence closed in the T1 space `ℝ` via
`Set.Subsingleton.isClosed`. The union covers `{r | IsComputable r}` by S3's
`computable_real_mem_range_decodeReal` (every computable real has a
decoding code) on the forward direction, and by the right factor of the
intersection on the reverse direction.

## 2. Why this is the right S10 ACT

The S10 PREP memo (PR #22049, 2026-06-02) surveyed three S10 directions:

* **Proposal A** — inline Fσ-style witness (~30 LOC, RECOMMENDED): completes
  the Σ⁰₂ side of the Borel-hierarchy classification dual to S8's
  Π⁰₂ (Gδ) side.
* **Proposal B** — interval-restricted cardinality refinement (~25 LOC):
  refines S4 cardinalities to every nonempty `Ioo`. Less mathematically
  novel than Proposal A.
* **Proposal C** — `Primrec ℚ` arithmetic (~150–300 LOC): would unblock
  `IsComputable e` / `π`. Substantial Mathlib-prerequisite contribution;
  out of scope for a single S10 ACT.

This PR implements Proposal A with one important refinement that the PREP
memo glossed over: the scaffold's `decodeReal_isComputable` lemma was not
trivially derivable. Recovering `Computable f` from a witness
`f : ℕ → ℚ` with `c.eval n = Part.some (Encodable.encode (f n))` requires
the encode-decode round-trip via `Computable.decode`, which is itself
~20–30 LOC of careful unfolding and is *not* the headline contribution of
S10.

The intersection formulation `{decodeReal c} ∩ {r | IsComputable r}`
side-steps this entirely. Membership in `s c` already carries the
`IsComputable r` proof in the right factor, so we never need to argue
whether `decodeReal c` is itself computable. The closure property follows
from subsingleton-ness (subset of singleton), and the union-covers property
falls out of S3's existing `computable_real_mem_range_decodeReal` without
needing a new computability argument.

## 3. Why "Fσ-style witness" rather than `IsFσ`

Mathlib v4.26.0 has no `IsFσ` predicate in
`Mathlib.Topology.GDelta.{Basic, MetrizableSpace}` — only `IsGδ`,
`residual`, `IsNowhereDense`, `IsMeagre` are provided. A GitHub code search
over `leanprover-community/mathlib4` (probed 2026-06-02, re-confirmed
this session) returns 0 hits for `IsFσ`, `IsFsigma`, `Set.Countable.isF`.

The natural-looking statement `IsFσ {r | IsComputable r}` therefore cannot
be a one-liner. We state the witness explicitly via the `Nat.Partrec.Code`
codebook of S3, which has a `Denumerable` instance giving the required
countable index type.

A future Mathlib PR introducing `IsFσ` (and a `Set.Countable.isFσ`
companion to the existing `Set.Countable.isGδ_compl`) would shorten this
theorem to a one-liner. The current explicit-witness formulation is the
expected workaround.

## 4. Proof sketch

```lean
theorem computable_reals_isFsigma_witness :
    ∃ s : Nat.Partrec.Code → Set ℝ,
      (∀ c, IsClosed (s c)) ∧
      {r : ℝ | IsComputable r} = ⋃ c, s c := by
  refine ⟨fun c => ({decodeReal c} : Set ℝ) ∩ {r : ℝ | IsComputable r}, ?_, ?_⟩
  · intro c
    apply Set.Subsingleton.isClosed
    intro x hx y hy
    have hx1 : x ∈ ({decodeReal c} : Set ℝ) := hx.1
    have hy1 : y ∈ ({decodeReal c} : Set ℝ) := hy.1
    rw [Set.mem_singleton_iff] at hx1 hy1
    exact hx1.trans hy1.symm
  · ext r
    refine ⟨fun hr => ?_, fun hr => ?_⟩
    · obtain ⟨c, hc⟩ := computable_real_mem_range_decodeReal hr
      refine Set.mem_iUnion.mpr ⟨c, ?_, hr⟩
      rw [Set.mem_singleton_iff]
      exact hc.symm
    · obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hr
      exact hc.2
```

Three Mathlib bearers (all verified via mathlib4_docs WebFetch at the
session start):

| Lemma | Module | Statement |
|---|---|---|
| `Set.Subsingleton.isClosed` | `Mathlib.Topology.Separation.*` | `Subsingleton s → IsClosed s` in T1 |
| `Set.mem_singleton_iff` | `Mathlib.Data.Set.Basic` | `x ∈ ({y} : Set α) ↔ x = y` |
| `Set.mem_iUnion` | `Mathlib.Data.Set.Lattice` | `x ∈ ⋃ i, s i ↔ ∃ i, x ∈ s i` |

All three are transitively imported via the existing
`Topology.Instances.Real.Lemmas` + `Mathlib.Tactic` chain. No new
`import` lines needed.

## 5. Build status

Docker `lake build Proofs.AlgebraicNumbersCountableOQ02OQ04` →
**✔ 3067/3067 jobs clean** (14s file compile, base SHA `eeca24a5`,
verified 2026-06-04). The proof type-checks against Mathlib v4.26.0 with
no new imports or API changes.

## 6. Mathematical takeaway

The descriptive-set-theoretic profile of the computable / non-computable
partition of `ℝ` is now complete on both sides:

| Side | Cardinality | Topology | Borel class |
|---|---|---|---|
| Computable reals | ℵ₀ (S3) | dense + meagre + frontier=univ (S7, S8, S9) | **Σ⁰₂ (S10, this PR)** |
| Non-computable reals | 𝔠 (S4) | dense + residual + frontier=univ (S8-prep, S8, S9) | Π⁰₂ (Gδ, S8) |

This is the exact descriptive-set-theoretic profile carried by the
rational / irrational partition of `ℝ`, refined here to the strictly
finer computable / non-computable split. The asymmetric Lean
formulation — `IsGδ` predicate on one side, explicit Fσ-witness on the
other — is a Mathlib-vocabulary artefact (absent `IsFσ`) rather than a
mathematical asymmetry between the two halves.

## 7. Files touched this PR

* `proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean`
  — +70 LOC: S10 section docstring (~35 LOC) + theorem
    `computable_reals_isFsigma_witness` (~22 LOC body) +
    blank-line separation.
* `src/data/proofs/algebraic-numbers-countable-oq-02-oq-04/meta.json`
  — `lineCount` 928→998; `theoremCount` 31→43 (S6 drift catch-up via
    the S10 increment) and 42→43 in `leanFile`; `originalContributions`
    array 22→23 entries (appends S10 entry).
* `research/problems/algebraic-numbers-countable-oq-02-oq-04/state.md`
  — header refresh: Phase S10 PREP → S10 ACT, Iteration 12 → 13, Last
    Updated, Branch, inventory snapshot (LOC + thm count), bearer
    citations updated, S11+ priority paragraph updated, S10 ACT
    session-log entry appended.
* `research/problems/algebraic-numbers-countable-oq-02-oq-04/sessions/2026-06-04-s10-act-fsigma-witness.md`
  — this memo.

**Zero changes to**: `proofs/Proofs.lean`, `problem.md`, `knowledge.md`,
`annotations.json`, `index.ts`, `src/data/research/problems/*.json`.
