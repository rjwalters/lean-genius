# State — fodor-pressing-down-oq-04

## Phase: S1 OBSERVE (complete)

## Session summary

**S1 OBSERVE (this session, 2026-05-12, researcher-4)** — doc-only survey of Solovay's splitting theorem in the context of `Proofs/FodorPressingDown.lean`.

Deliverables produced this session:

- `research/problems/fodor-pressing-down-oq-04/problem.md` — precise theorem statement, scope, anchor file/line references.
- `research/problems/fodor-pressing-down-oq-04/knowledge.md` — three-step classical proof breakdown (limit-reduction, regressive-auxiliary, diagonal κ-intersection), reusable-lemma table, Mathlib API survey, three S2 candidates ranked by tractability.
- Pool entry updated (status = `in-progress`, S1 OBSERVE completed).

No Lean code changes. No build performed.

## Proof structure at a glance

| Step | What | Existing infra | Difficulty |
|---|---|---|---|
| 1 | Reduce to limit ordinals | `IsStationaryBelow.of_subset` | Easy |
| 2 | Regressive auxiliary + Fodor | `fodor` (line 259) | Medium |
| 3 | Iterated κ-choice + counting | `diagInter_isClubBelow` (line 240) | Hard (Skolem) |

## Next action (S2 recommended)

**S2-α**: Prove `successor_ordinals_nonStationary` — the standalone reduction lemma that the set of successor ordinals below `κ.ord` is non-stationary (equivalently, limit ordinals form a club). Expected scope ~40–80 lines added to `FodorPressingDown.lean` or a companion file, 0 sorries, 0 new axioms.

Sketch:

```lean
theorem isLimitOrdinals_isClubBelow {κ : Cardinal.{0}}
    (hκ : κ.IsRegular) (hκ_unc : ℵ₀ < κ) :
    IsClubBelow {α : Ordinal | α < κ.ord ∧ IsSuccLimit α} κ.ord := by
  refine ⟨fun a ha => ha.1, ?_, ?_⟩
  -- closed: a limit of limit-ordinals is a limit-ordinal
  · intro β hβ hβacc
    sorry  -- standard: accumulation point of limits is a limit
  -- unbounded: for any α < κ.ord, the next limit is < κ.ord
  · intro α hα
    sorry  -- use Ordinal.add_omega or similar
```

The two `sorry`s are the only obligations and both have direct Mathlib counterparts.

## Open questions deferred to later sessions

1. **S2-β (S3 candidate):** Binary Solovay splitting — any stationary set splits into 2 disjoint stationary subsets. Requires one Fodor application, no κ-tuple machinery.

2. **S2-γ (S4+ candidate):** Full Solovay splitting (κ-many pairwise-disjoint stationary subsets). Requires `Classical.skolem` for the κ-indexed regressive choices and a careful counting argument.

3. **Connection to ω₁-combinatorics (S5+):** Once Solovay is proven, derive corollaries: club guessing, ◇_{ω₁}, Σ-products of ω₁ — all foundational forcing-theoretic results.

## Build / verification

S1 OBSERVE is doc-only — no build required. Line counts:

- `problem.md`: ~50 lines
- `knowledge.md`: ~145 lines
- `state.md` (this file): ~55 lines

## Blockers

None at S1 OBSERVE level. S2-α has no new Mathlib dependencies beyond the existing `Ordinal.IsSuccLimit` (already imported in `FodorPressingDown.lean`).
