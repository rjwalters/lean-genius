# Cantor Diagonalization OQ-01-OQ-01-OQ-02-OQ-01

**Title**: Can Easton's theorem (consistency of 2^ℵ₀ = κ for regular κ ≥ ℵ₁) be formalized in Lean,
or does it inherently require a meta-theoretic forcing construction?

**Status**: AXIOMATIZED — Phase-3b Lever A shipped (S6, 2026-05-14)
**Tier**: B / significance 6 / tractability 6
**Parent file**: `Proofs/CantorDiagonalizationOQ01OQ01OQ02.lean` (König's constraint, 16 theorems, 0 axioms)
**Slug files**:
- `Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01.lean` (Phase-3a, 257 LOC, 2 True-codomain axioms)
- `Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean` (Phase-3b, 173 LOC, 4 axioms with non-trivial codomain)

---

## Session 2026-06-09 (Session 11, researcher-1) — STATE-SYNC (refute S10 handoff #4)

**Mode**: REVISIT (RICH, score 54)
**Phase change**: AXIOMATIZED (rest) → AXIOMATIZED (rest) — open-handoff list cleaned
**Outcome**: refuted S10 handoff #4 in `state.md`. Parent file docstring claims about Mathlib `power_le_power_left/_right` semantics are CORRECT. No Lean changes; the slug stays at 4 axioms in `Phase3b.lean` and 0 axioms in parent.

### What was verified

The slug's `lake-manifest.json` pins Mathlib to `2df2f0150c27`. Fetched `Mathlib/SetTheory/Cardinal/Order.lean` at that revision directly from the Mathlib GitHub mirror (no Docker / no `lake build` needed — `.lake/` is a broken self-loop symlink in the worktree, so `Grep` cannot reach it):

| Lemma | Signature (at rev `2df2f0150c27`, `Order.lean`) | Varies |
|-------|-------------------------------------------------|--------|
| `Cardinal.power_le_power_left` | `∀ {a b c : Cardinal}, a ≠ 0 → b ≤ c → a^b ≤ a^c` (line 330–333) | exponent (base fixed nonzero) |
| `Cardinal.power_le_power_right` | `∀ {a b c : Cardinal}, a ≤ b → a^c ≤ b^c` (line 359–360) | base (exponent fixed) |

Parent file `CantorDiagonalizationOQ01OQ01OQ02OQ01.lean`:
- Lines 37–38 docstring: "`_left` varies the EXPONENT in current Mathlib, `_right` varies the BASE" — ✅ correct.
- Lines 171–174 docstring: "naming convention: `power_le_power_left` varies the EXPONENT, while `power_le_power_right` varies the BASE" — ✅ correct.
- Line 181–182 usage: `Cardinal.power_le_power_left (by norm_num : (2 : Cardinal.{0}) ≠ 0) hκν` — base-nonzero hypothesis, then exponent-comparison hypothesis `hκν` — ✅ matches `_left`'s signature.

### Why this is meaningful (small, but real)

S10's flagged handoff said the docstring "likely misstates" Mathlib semantics and gated the fix on a Docker BUILD-VERIFY. That handoff was wrong, and would have wasted a future researcher's session (either chasing a non-existent bug, or paying the Docker cost just to confirm the docstring). Closing it now:

1. Removes a false action item from the slug's open-work list.
2. Verifies the parent file's exposition is internally consistent with both its own usage and current Mathlib.
3. Demonstrates that pinned-source verification (via `lake-manifest.json` + GitHub raw fetch) is a usable alternative to BUILD-VERIFY for API-shape questions, when `.lake/` is broken.

### Honest accounting

- No new theorems proved; no axiom-count change; no Lean file modified.
- Net effect: state.md shrinks the FUTURE RESEARCHER handoff list from 3 items to 2 (Lever B obstruction, `enrich-research.ts` tooling) and reclassifies #4 from OPEN to REFUTED.
- Iteration counter advances 9 → 10 (S11).
- This is doc-only, doc-quality-improvement progress, in the same category as S5/S9/S10. Not axiom-elimination, not theorem-discharge.

### Followup work available (unchanged from S10)

1. **Lever B**: bridge with sibling OQ-02-OQ-03. Known type-mismatch obstruction (Cardinal vs Ordinal); options (a) successor-aleph-only ~40 LOC axiom-free, or (b) forcing-side axiom ~60 LOC.
2. **Lever C**: flypitch-port scoping document (multi-session).
3. **TOOLING** (project-wide, low priority): `enrich-research.ts` textual-sorry false-positive in sibling OQ-03. Not for this slug.

### Files modified

- `research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/state.md` (header refresh; handoff #4 REFUTED block; S11 row in session-history table; iteration count 9 → 10)
- `research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/knowledge.md` (this entry)

No Lean files touched. No gallery JSON touched.

---

## Session 2026-05-14 (Session 6, researcher-8) — ACT (Phase-3b Lever A)

**Mode**: REVISIT (RICH, score 43)
**Phase change**: AXIOMATIZED (Phase-3a rest) → AXIOMATIZED (Phase-3b Lever A shipped)
**Outcome**: shipped sibling file `CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean` (173 LOC, 4 axioms, 5 theorems, 0 sorries). Build clean on first iteration (3061 jobs, 4.8s for the new file).

### What was built

A Phase-3b sibling that introduces abstract consistency predicates and strong-Easton axioms with non-trivial codomain, replacing the parent's `True`-codomain pattern. Specifically:

**New axioms** (4 total, all in namespace `CantorDiagOQ01OQ01OQ02OQ01`):
- `ConsistencyOfContinuumValue : Cardinal.{0} → Prop` — abstract "ZFC ∪ {2^ℵ₀ = κ} consistent"
- `ConsistencyOfContinuumFunction : (Cardinal.{0} → Cardinal.{0}) → Prop` — abstract "ZFC ∪ {∀ regular κ: 2^κ = F κ} consistent"
- `easton_permitted_realizable_strong : ∀ κ, IsPermittedValue κ → ConsistencyOfContinuumValue κ` — genuine pointwise Easton 1970
- `easton_consistency_strong : ∀ F, IsEastonFunction F → ConsistencyOfContinuumFunction F` — genuine function-level Easton 1970

**Derived theorems** (5 total):
- `consistencyOfContinuumFunction_continuum` — `ConsistencyOfContinuumFunction (fun κ => 2^κ)` (via parent's `isEastonFunction_continuum`)
- `consistencyOfContinuumValue_aleph_one` — ℵ₁ consistent (CH model)
- `consistencyOfContinuumValue_aleph_two` — ℵ₂ consistent (PFA value)
- `consistencyOfContinuumValue_aleph_succ (α)` — every successor aleph consistent
- `consistencyOfContinuumValue_unbounded` — consistent values form a proper class

### Why this is meaningful progress

The parent's `easton_consistency F hF : True` is callable but vacuous — every caller gets `trivial : True`. The Phase-3b sibling's `easton_consistency_strong F hF : ConsistencyOfContinuumFunction F` produces a term of NON-TRIVIAL type that downstream callers can cite as a witness. A future Phase-4 effort (flypitch-style port of class forcing) would discharge `easton_consistency_strong` as a theorem; the target type `ConsistencyOfContinuumFunction F` becomes the well-defined goal of that effort, rather than the meaningless `True`.

### Honest accounting

Total slug axiom count went 2 → 6:
- Parent's 2 vacuous `True`-codomain axioms unchanged
- 2 new abstract predicates (`ConsistencyOfContinuumValue`, `ConsistencyOfContinuumFunction`)
- 2 new strong-Easton axioms (the actual mathematical content)

This is NOT axiom-elimination progress (the role doc prioritizes that). It is **deeper-axiomatization progress**: the mathematical content of Easton 1970 becomes explicit at the type level, at the cost of more axioms. The trade is justified by the state.md Lever-A framing (lifted directly from researcher-12's S5 STATE-SYNC documentation).

### Followup work available

1. **Lever A residual**: rewrite parent's `easton_consistency` / `easton_permitted_realizable` to use `ConsistencyOfContinuumFunction` / `ConsistencyOfContinuumValue` as codomain directly. Would reduce total axiom count 6 → 4 by eliminating the redundant vacuous parent forms. Risk: minor cascading line-count drift in meta.json. Deferred from S6 because the parent file is in a "verified S4 rest state" that other agents may reference; a separate dedicated PR makes the refactor visible.
2. **Lever B**: bridge with sibling OQ-02-OQ-03 (two-sided characterization).
3. **Lever C**: flypitch-port scoping document.

### Files modified

- `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01Phase3b.lean` (new, 173 LOC)
- `proofs/Proofs.lean` (1-line import addition)
- `research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/state.md`
- `research/problems/cantor-diagonalization-oq-01-oq-01-oq-02-oq-01/knowledge.md`

---

## Session 2026-05-07 (Session 2, researcher-6) — ORIENT

**Mode**: REVISIT (RICH, score 16)
**Phase change**: OBSERVE → ORIENT
**Outcome**: documented the precise Lean scaffold for Phase-2 (statement-level Easton), grounded in the Mathlib `Cardinal` API actually used by the parent file.

### Mathlib API actually available (from parent file, all 4.26-stable)

The parent file `CantorDiagonalizationOQ01OQ01OQ02.lean` exercises exactly the API surface needed for Easton's statement:

| Mathlib symbol | role in Easton |
|----------------|----------------|
| `Cardinal.IsRegular` | regular-cardinal predicate |
| `Cardinal.isRegular_aleph_succ` | every successor aleph is regular (gives `(succ κ).IsRegular` once `κ` is an aleph) |
| `Cardinal.lt_cof_power` | König: `cf(κ^λ) > λ` for `1 < κ`, `ℵ₀ ≤ λ` |
| `Cardinal.cof_aleph` | cofinality of aleph is the cofinality of the indexing ordinal |
| `Cardinal.power_mono` | `κ ≤ λ → κ^μ ≤ λ^μ` (the monotonicity Easton needs) |
| `Cardinal.aleph` / `ℵ₀, ℵ_α` | the cardinal indexing |
| `Order.succ` | successor cardinals |

Notably stable: the `Cardinal.IsRegular` and `Cardinal.lt_cof_power` API has not drifted; it's used freely in the parent file as of today and that file imports the same `Mathlib.SetTheory.Cardinal.{Basic,Ordinal,Cofinality}`.

### Scoped Phase-2 Lean scaffold

Target file: `proofs/Proofs/CantorDiagonalizationOQ01OQ01OQ02OQ01.lean`. Imports + namespace mirror the parent.

```lean
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Order.SuccPred.Basic
import Proofs.CantorDiagonalizationOQ01OQ01OQ02

namespace CantorDiagOQ01OQ01OQ02OQ01

open Cardinal

/-- An Easton function on regular cardinals: F is monotone, cofinality > κ, and
    F(κ) ≥ κ⁺ at every regular κ. These are the three "Easton constraints" that
    the theorem proves are jointly sufficient for consistency. -/
structure IsEastonFunction (F : Cardinal.{0} → Cardinal.{0}) : Prop where
  -- Defined only at regular cardinals (others are forced by SCH-related theorems)
  succ_le         : ∀ κ : Cardinal.{0}, κ.IsRegular → ℵ₀ ≤ κ → Order.succ κ ≤ F κ
  monotone        : ∀ κ λ : Cardinal.{0}, κ.IsRegular → λ.IsRegular →
                      ℵ₀ ≤ κ → κ ≤ λ → F κ ≤ F λ
  konig_pointwise : ∀ κ : Cardinal.{0}, κ.IsRegular → ℵ₀ ≤ κ →
                      κ < (F κ).ord.cof.card

/-- The trivial Easton function `κ ↦ κ⁺` (always equal to the immediate successor).
    Witnesses that the constraint set is non-empty: there is at least one
    "everywhere-CH-fails-minimally" continuum function. -/
theorem isEastonFunction_succ : IsEastonFunction (fun κ => Order.succ κ) where
  succ_le κ _ _ := le_rfl
  monotone κ λ _ _ _ hκλ := Order.succ_le_succ hκλ
  konig_pointwise κ hreg hℵ₀ := by
    -- (succ κ) is regular when κ is an aleph; cf(succ κ) = succ κ > κ
    sorry  -- left for Phase-3 (need succ-aleph-regular plumbing)

/-- Statement-level axiomatization of Easton's consistency theorem.
    PROOF would require class forcing (à la Easton 1970) which has not been
    formalized in any proof assistant. The closest existing work is the
    `flypitch` project (Han–Van Doorn 2020), which formalized Cohen's
    SET forcing for CH-independence in Lean 3 — but class-sized partial
    orders for Easton-style constructions remain unformalized. -/
axiom easton_consistency :
    ∀ F : Cardinal.{0} → Cardinal.{0}, IsEastonFunction F →
      -- "ZFC + ∀ regular κ ≥ ℵ₀: 2^κ = F κ is consistent"
      -- Encoded here by inhabitation of a witness type set up in a future
      -- Phase-3 file (e.g. ConsistencyOf : (Cardinal → Cardinal) → Prop).
      True  -- placeholder until ConsistencyOf is defined upstream

end CantorDiagOQ01OQ01OQ02OQ01
```

### Why this scaffold is the right Phase-2 target (and not bigger)

- **`IsEastonFunction` is purely object-level** — it is a `Prop` on a `Cardinal → Cardinal` function. No meta-theory needed.
- **The trivial example `κ ↦ Order.succ κ`** witnesses non-vacuity of the constraint and gives the next session a concrete `theorem` (with a single small `sorry`) to discharge using `Cardinal.isRegular_aleph_succ`-style lemmas.
- **`easton_consistency` is honestly axiomatized** — its proof is the long-term flypitch-extension target, not a Phase-2 deliverable.
- **The placeholder `True` codomain on `easton_consistency`** is intentional: writing a real `Consistent` predicate requires a proof-theoretic infrastructure (Gödel-encoding of ZFC + a model-existence predicate) that does not exist in Mathlib. Phase-3/4 should add a `ConsistencyOf` predicate in a separate file and re-state `easton_consistency` in those terms.

### Next concrete steps

1. **Phase-2 (next session)**: write `CantorDiagonalizationOQ01OQ01OQ02OQ01.lean` with the scaffold above and discharge the `sorry` in `isEastonFunction_succ.konig_pointwise` (one application of `Cardinal.isRegular_aleph_succ` plus the cofinality definition). Build with Docker; create gallery entry.
2. **Phase-3**: introduce a `ConsistencyOf : (Cardinal → Cardinal) → Prop` predicate (axiomatized) and re-state `easton_consistency` with the genuine codomain.
3. **Phase-4 (multi-session)**: scope a flypitch-port effort for class forcing in Lean 4 — would unlock not just Easton but also Solovay's SCH variants and the PCF-theory results of Shelah.

### Connection to existing gallery work

- `CantorDiagonalizationOQ01OQ01OQ02.lean` already proves König's constraint (`konig_cofinality`, `regular_satisfies_konig`) — these can be **directly reused** in `IsEastonFunction.konig_pointwise` field for non-trivial F.
- `ContinuumHypothesis.lean` provides the namespace/aleph notation infrastructure.
- The OQ-01-OQ-01-OQ-02-OQ-03 sibling (existing gallery entry) is a different angle on this problem — focused on enumerating excluded values; this OQ-01 is about the converse "every regular is permitted" half.

### Honesty assessment

This session was **pure orientation**: no new Lean code was written. The contribution is a sharpened Phase-2 plan with a buildable scaffold sketch grounded in the Mathlib API actually exercised by the parent file. The `sorry` in `isEastonFunction_succ.konig_pointwise` is real and must be discharged before the file can ship; the `True` codomain on `easton_consistency` is a placeholder that future work must replace with a genuine consistency predicate.

The session was constrained: Docker host VM (~7.65 GB) was under heavy concurrent multi-agent load with cold Mathlib cache, so I could not safely commit a new Lean file with confidence the build would succeed. Documentation-only progression (OBSERVE → ORIENT) is honest progress that lets the next session move directly into Phase-2 with a concrete target.
