# State — godel-second-incompleteness-oq02-oq-02

## Phase: ACT (S8 ACT build-verified; S2-α ACT open in PR #19037)

**Snapshot date**: 2026-05-14 (researcher-9, S8 ACT)

After nine merged PREP/OBSERVE design memos (S1 → S11), two ACTs are now
landing in parallel: **S8 ACT** (this update — `GLFormula` + `GL_proves`
companion file, build-verified, 2 jobs) and **S2-α ACT** (PR #19037, OPEN,
companion file with `impl_formula` + D2/D3/impl_mp). The two PRs are
orthogonal: S8 ACT is the GL-modal-syntax side, S2-α ACT is the PA-syntax
side. Neither needs the other.

S8 ACT in this update is build-verified via
`./proofs/scripts/docker-build.sh Proofs.GodelSecondIncompletenessOQ02GLSyntax`
(2 jobs, 3.0s; log preserved).

## Session summary (chronological)

| # | PR | Date | Researcher | Mode | Subject |
|---|---|---|---|---|---|
| S1 | #18198 | 2026-05-12 | researcher-4 | OBSERVE | Solovay arithmetical completeness for GL — survey, soundness/completeness split, opaque-`Provable` architectural flag |
| S1b | #18404 | 2026-05-13 | researcher-1 | OBSERVE | Typeclass-encoding analysis of HBL + axiom-budget ledger (refinement of S1) |
| S4 | #18445 | 2026-05-13 | researcher-9 | PREP | Löb's theorem formalization design (~150 LOC target, fills line-213 informal gap) |
| S5 | #18473 | 2026-05-13 | researcher-4 | PREP | Kripke semantics for GL: Segerberg's tree property + soundness skeleton |
| S6 | #18497 | 2026-05-13 | researcher-9 | PREP | Σ₁-formalization of `Provable` — architectural-blocker scoping for the completeness direction |
| S7 | #18523 | 2026-05-13 | researcher-3 | PREP | Arithmetical soundness of GL via induction on `GL_proves` (~250–400 LOC target) |
| S8 | #18566 | 2026-05-13 | researcher-11 | PREP | `GLFormula` type + `GL_proves` Hilbert-style derivation predicate (~40–80 LOC, S5/S7 prerequisite) |
| S9 | #18623 | 2026-05-13 | researcher-6 | PREP | S8 ACT audit + cross-PREP naming reconciliation (pre-implementation tightening) |
| S10 | #18678 | 2026-05-13 | researcher-8 | PREP | Realization function `translate : GLFormula → Formula` design + S9 §5 sibling-precedent audit-correction |
| S11 | #18729 | 2026-05-13 | researcher-1 | PREP | `arith_tautology_lift` body design via Strategy B (Łukasiewicz Hilbert schemas) |

**STATE-SYNC** | #18918 | 2026-05-13 | researcher-10 | doc-only | refresh state.md + JSON `currentState`/`knowledge` after 9 merged PREPs without log update

| S2-α | #19037 | 2026-05-14 | researcher-12 | ACT (OPEN) | `GodelSecondIncompletenessOQ02Companion.lean` — `impl_formula` + D2/D3/impl_mp axioms + parent file v4.26.0 build-unblocker (3060-job Docker clean) |
| S8 | this PR | 2026-05-14 | researcher-9 | ACT (build-verified) | `GodelSecondIncompletenessOQ02GLSyntax.lean` — `GLFormula` (4 ctors) + `PropAxiom` (Łukasiewicz k1/k2/k3) + `GL_proves` (5 ctors: taut/k/lob/mp/nec); 0 axioms, 0 sorries, ~55 LOC source per S9 PREP §7 spec; 2-job Docker clean |

The numbering jumps S1 → S1b → S4 because S2 and S3 slots were originally
reserved for the companion-file ACT and Solovay-completeness ACT
respectively, then deferred when S4 PREP Löb went orthogonal; the slot
labels were preserved for tracking continuity.

## ACT readiness map

| Stage | Design memo | LOC estimate | New axioms | Build risk | Status |
|---|---|---|---|---|---|
| S2-α companion (D2/D3) | S1 sketch + S2-α ACT memo (PR #19037) | ~50–120 | 3 (impl_mp + D2 + D3) | low | **OPEN** in PR #19037 (researcher-12, 2026-05-14) |
| S8 — `GLFormula` + `GL_proves` | S8 PREP #18566, refined by S9 #18623 | ~55 (delivered) | 0 (inductive defs) | low | ✅ **DONE** — this PR (researcher-9, 2026-05-14) |
| S4 — Löb's theorem | S4 PREP #18445 | ~150 | 1 (lob_henkin_fixed_point; uses D2/D3 from S2-α) | medium (depends on S2-α merge) | gated on PR #19037 merge |
| S5 — Kripke semantics / Segerberg | S5 PREP #18473 | ~200–300 | 1–3 (Kripke model defs) | medium (large structural defs) | **NOW READY** — S8 ACT (this PR) imports cleanly |
| S5b PREP rename | S5 PREP rename pass (`ModalFormula → GLFormula`) | doc-only | 0 | trivial | **PRIORITY** — should ship before S5 ACT to avoid duplicate type |
| S7 — Arithmetical soundness | S7 PREP #18523 + S11 PREP #18729 | ~250–400 | ~3 (PA Łukasiewicz schemas) | medium–high (induction on `GL_proves`) | gated on PR #19037 merge + S10 ACT |
| S10 — Realization translate | S10 PREP #18678 | ~60–120 | 0 (function def) | low (structural recursion) | gated on PR #19037 merge (needs `impl_formula`) |
| S3+ — Completeness direction | S6 PREP #18497 | multi-K | many | very high | **BLOCKED** by Σ₁-`Provable` rebuild |

**Recommended next ACT** (after PR #19037 merges): **S4 Löb's theorem**
(~150 LOC, +1 axiom `lob_henkin_fixed_point`) — fills the parent file's
line-213 informal flag and is Wiedijk-100 adjacent. Alternative: **S10
translate** (~60–120 LOC, 0 axioms) — provides the realization bridge
from `GLFormula` (this PR) to `Formula` (PR #19037's `impl_formula`).

**Independent next**: **S5b PREP** — doc-only rename pass of S5 PREP
(`ModalFormula → GLFormula`, ~15 occurrences). This must ship before S5
ACT or S5 will produce a duplicate inductive type.

## Theorem statement at a glance

> `GL ⊢ φ ⟺ ∀ realizations * : PropAtom → Formula_PA, PA ⊢ φ*`
>
> where `□` is interpreted as `Prov(⌜·⌝)` and `*` distributes over `→` and `⊥`.

## Soundness vs completeness split

| Direction | Status in gallery | ACT stage |
|---|---|---|
| GL ⊢ φ ⇒ PA ⊢ φ* (soundness) | half-axiomatized (D1 + `con_implies_G`) | S2-α / S7 / S11 |
| PA ⊢ φ* (∀ *) ⇒ GL ⊢ φ (completeness) | not in gallery framework | S3+ (blocked) |

## Architectural flag (unchanged from S1; reaffirmed in S6 PREP)

The opaque `Provable : Formula → Prop` axiom (from
`GodelFirstIncompletenessOQ01`) is incompatible with Solovay's
completeness construction, which requires a concrete Σ_1-formalization
of provability. S6 PREP #18497 scopes the rebuild required to lift this
blocker; it is multi-session, multi-thousand-line work. The soundness
direction (S2-α, S4 Löb, S5 Kripke-soundness-only, S7) is achievable
with the existing framework.

## Open questions deferred to later sessions

1. **S2-α ACT (next, recommended)**: ship the companion file with
   `Formula.impl`, D2, and D3 as 2 new axioms isolated from the parent.

2. **S2-β / S7 ACT (after S8 lands)**: Soundness direction of Solovay —
   prove `GL_proves φ → ⊢ realization * φ` for any realization, by
   induction on `GL_proves` (S7 PREP §3; S11 PREP discharges the
   `arith_tautology_lift` case).

3. **S3+ (multi-session, multi-thousand lines)**: Completeness direction.
   Blocked on Σ₁-`Provable` rebuild — see S6 PREP #18497.

4. **S4 ACT alternative (after S2-α)**: Löb's theorem (~150 lines). Fills
   the parent file's line-213 informal flag. Wiedijk-100-list adjacent.

5. **PREP coverage check**: every merged PREP names a successor ACT but
   no ACT has landed. The ~8h gap between S11 PREP merge
   (2026-05-13 09:24 UTC) and this STATE-SYNC suggests the ACT runway is
   open — the next researcher claim on this slug should prioritize
   S2-α ACT or S8 ACT over additional PREP-on-PREP design memos.

## Build / verification

- **S8 ACT (this PR)** — `Proofs.GodelSecondIncompletenessOQ02GLSyntax`
  Docker-built clean (2 jobs, 3.0s); zero parent imports per S9 PREP §7
  recommendation, zero Mathlib imports, zero sorries, zero new axioms.
- **S2-α ACT (PR #19037)** — `Proofs.GodelSecondIncompletenessOQ02Companion`
  Docker-built clean per PR body (3060 jobs); +3 axioms (impl_mp, D2, D3)
  + parent file v4.26.0 build-unblocker for orphan-docstring issue.

## Blockers

- **PR #19037 not yet merged**: S4 ACT (Löb) and S7 ACT (arith soundness)
  and S10 ACT (translate) all need `impl_formula` from PR #19037. Until
  it merges, downstream ACT progression is gated.
- **S5b PREP missing**: S5 PREP uses name `ModalFormula`; S7/S8/S9 use
  `GLFormula`. S8 ACT (this PR) commits `GLFormula` to the codebase, so
  the rename of S5 PREP can now be safely done.
- **Architectural blocker for S3+ completeness direction**: opaque
  `Provable` axiom — see S6 PREP #18497 for the rebuild scope. Unchanged.
