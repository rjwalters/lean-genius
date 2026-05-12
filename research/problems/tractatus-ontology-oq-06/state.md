# State — tractatus-ontology-oq-06

## Phase: S1 OBSERVE (complete)

## Session summary

**S1 OBSERVE (this session, 2026-05-12, researcher-4)** — doc-only survey.

Deliverables produced this session:

- `.lean/research/tractatus-ontology-oq-06/problem.md` — precise statement of the OQ, scope of S1 vs S2+, anchor references to existing Lean file lines.
- `.lean/research/tractatus-ontology-oq-06/knowledge.md` — four-tier spectrum classification (free → predicate-constrained → Kripke → quotient), refinement preorder candidate, theorem-survival table, three concrete S2 candidates.
- Pool entry updated (status = `in-progress`, S1 OBSERVE completed).

No Lean code changes. No build performed.

## Spectrum at a glance

| Tier | Worlds | Independence | Example |
|---|---|---|---|
| T0 free | `S → Prop` | ✓ trivially | `freeModel` |
| T1a Horn | `{w // ⋀ Hᵢ → Bᵢ}` | ✗ when ≥ 1 implication | `weatherModel`, `ConstrainedWorld` |
| T1b equiv | `{w // ⋀ w aᵢ ↔ w bᵢ}` | ✗ when class > 1 | (none yet) |
| T2 Kripke | indexed + accessibility | model-dependent | (out of scope) |
| T3 quotient | `(S → Prop) /~` | depends on `~` | (out of scope) |

## Next action (S2 recommended)

**S2-α**: Define `Refines : WorldModel S → WorldModel S → Prop` and prove `freeModel S` is the maximum element of the refinement preorder.

Sketch:

```lean
def Refines (M M' : WorldModel S) : Prop :=
  ∃ f : M.W → M'.W, ∀ (w : M.W) (s : S), M.holds w s ↔ M'.holds (f w) s

theorem refines_freeModel (M : WorldModel S) : Refines M (freeModel S) :=
  ⟨fun w => fun s => M.holds w s, fun _ _ => Iff.rfl⟩
```

Expected scope: ~30–60 lines added to `Proofs/TractatusOntology.lean` (or a new companion file `Proofs/TractatusOntologySpectrum.lean`), 0 sorries, 0 new axioms.

## Open questions deferred to later sessions

1. **R1 (S3 candidate):** `M ≤ M'` implies `IsTautologyM M'` ⊆ `IsTautologyM M`. (Tautology preservation is downward.)
2. **R2 (S3 candidate):** Existence of a *generic Horn model constructor* `HornModel S (cs : List (S × S))` and equivalence with the existing `ConstrainedWorld`.
3. **R3 (S4+ candidate):** Uniqueness-up-to-refinement-iso of `freeModel` among inhabitants of `WorldModel S` satisfying full independence.

## Build / verification

S1 OBSERVE is doc-only — no build required. `wc -l` for the two markdown deliverables:

- `problem.md`: ~55 lines
- `knowledge.md`: ~120 lines
- `state.md` (this file): ~50 lines

## Blockers

None at S1 OBSERVE level. S2-α has no build dependencies beyond the existing `WorldModel` structure already in `TractatusOntology.lean`.
