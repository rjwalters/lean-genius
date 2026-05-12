# State — godel-second-incompleteness-oq02-oq-02

## Phase: S1 OBSERVE (complete)

## Session summary

**S1 OBSERVE (this session, 2026-05-12, researcher-4)** — doc-only survey of Solovay's arithmetical completeness theorem for the propositional modal logic GL.

Deliverables produced this session:

- `research/problems/godel-second-incompleteness-oq02-oq-02/problem.md` — precise statement, scope, anchor file/line references.
- `research/problems/godel-second-incompleteness-oq02-oq-02/knowledge.md` — GL axiomatization, arithmetical realization operation, gallery-correspondence table for soundness, Solovay's completeness construction sketch, Mathlib API gap analysis, three S2 candidates ranked by tractability.
- `research/problems/godel-second-incompleteness-oq02-oq-02/state.md` — session log and S2-α sketch.
- Pool entry updated (status = `in-progress`, S1 OBSERVE completed).

No Lean code changes. No build performed.

## Theorem statement at a glance

> `GL ⊢ φ ⟺ ∀ realizations * : PropAtom → Formula_PA, PA ⊢ φ*`
>
> where `□` is interpreted as `Prov(⌜·⌝)` and `*` distributes over `→` and `⊥`.

## Soundness vs completeness split

| Direction | Status in gallery | S2 difficulty |
|---|---|---|
| GL ⊢ φ ⇒ PA ⊢ φ* (soundness) | half-axiomatized (D1 + `con_implies_G`) | Medium (S2-β) |
| PA ⊢ φ* (∀ *) ⇒ GL ⊢ φ (completeness) | not in gallery framework | Very hard (S3+) |

## Architectural flag

**The opaque `Provable : Formula → Prop` axiom (from `GodelFirstIncompletenessOQ01`) is incompatible with Solovay's completeness construction**, which requires a concrete Σ_1-formalization of provability. This is a fundamental architectural mismatch that should be flagged before any completeness-direction S3 work begins. The S2-β soundness direction is achievable with the existing framework; the completeness direction is not.

## Next action (S2 recommended)

**S2-α**: Extend the `Formula` type with `impl : Formula → Formula → Formula` and add D2/D3 as honest object-level axioms. Implementation as a companion file (`GodelSecondIncompletenessOQ02Companion.lean`) isolates the new axioms from the parent.

Sketch:

```lean
namespace GodelSecondCompanion

def impl (φ ψ : Formula) : Formula := ⟨Nat.pair φ.code (Nat.pair ψ.code 1)⟩

axiom d2_modus_ponens : ∀ φ ψ : Formula,
    (⊢ Prov (godelNum (impl φ ψ))) → (⊢ Prov (godelNum φ)) → (⊢ Prov (godelNum ψ))

axiom d3_internal_necessitation : ∀ φ : Formula,
    (⊢ Prov (godelNum φ)) → (⊢ Prov (godelNum (Prov (godelNum φ))))

end GodelSecondCompanion
```

Expected scope: ~50–120 lines in a new companion file, **2 new axioms** (D2 and D3 cleanly factored out of `con_implies_G`). The parent's axiom count is unchanged; the companion's new axiom count is documented separately in its docstring.

## Open questions deferred to later sessions

1. **S2-β (S3 candidate, ~200–400 lines):** Soundness direction of Solovay — prove `GL_proves φ → ⊢ realization * φ` for any realization, by induction on `GL_proves`.

2. **S3+ (multi-session, multi-thousand lines):** Completeness direction. Requires (a) replacing the opaque `Provable` axiom with a concrete Σ_1-formalization of provability, (b) Segerberg completeness of GL over finite Kripke models, (c) Solovay's fixed-point `h` construction, (d) Σ_1-completeness of PA. Best done after a major restructuring of the parent file's axiomatization.

3. **S4+ alternative (Löb formalization, ~150 lines):** Even without full Solovay, *Löb's theorem* (`F ⊢ □A → A ⇒ F ⊢ A`) can be formalized once D2/D3 are stated as proper axioms. The parent file flags this at line 213 as desirable but currently informal. This would also resolve a Wiedijk-100-list adjacent gap.

## Build / verification

S1 OBSERVE is doc-only — no build required. Line counts:

- `problem.md`: ~50 lines
- `knowledge.md`: ~170 lines
- `state.md` (this file): ~70 lines

## Blockers

- **No code-level blocker for S2-α.** The companion file approach is well-localized.
- **Architectural blocker for S3+ completeness direction:** the opaque `Provable` axiom must be replaced with a concrete Σ_1-formalization. This is a major restructuring and should be a separate proposal (not a single session).
