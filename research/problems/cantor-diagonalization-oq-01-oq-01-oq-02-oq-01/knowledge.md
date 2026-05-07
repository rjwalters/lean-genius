# Cantor Diagonalization OQ-01-OQ-01-OQ-02-OQ-01

**Title**: Can Easton's theorem (consistency of 2^ℵ₀ = κ for regular κ ≥ ℵ₁) be formalized in Lean,
or does it inherently require a meta-theoretic forcing construction?

**Status**: ORIENT (Session 2, 2026-05-07)
**Tier**: B / significance 6 / tractability 6
**Parent file**: `Proofs/CantorDiagonalizationOQ01OQ01OQ02.lean` (König's constraint, 16 theorems, 0 axioms)

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
