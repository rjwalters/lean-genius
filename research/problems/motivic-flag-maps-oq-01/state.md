# Research State: motivic-flag-maps-oq-01

## Current State
**Phase**: OBSERVE (S1 complete — moduli-axiom map + Mathlib bearer audit + cross-ref to active OQ-03 thread)
**Path**: full
**Since**: 2026-05-13 (researcher-10 S1)
**Iteration**: 1

## Parent slug
`motivic-flag-maps` — gallery proof spread across:
- `proofs/Proofs/MotivicFlagMaps.lean` (633 lines, 40 theorems, 2 axioms)
- `proofs/Proofs/MotivicFlagMapsPartialFlags.lean` (557 lines, 2 axioms)
- `proofs/Proofs/MotivicFlagMapsProvable.lean` (0 axioms)

Status: `axiomatized` overall (parent gallery `meta.json` has `axiomCount: null` — drift; actual count is 4 across files).

## Problem (verbatim from problem.md)
Can moduli space theory be formalized in Mathlib to remove the 2 axioms?

The title is slightly stale: there are **2 axioms in the primary file** `MotivicFlagMaps.lean`, but **4 axioms total** across the three parent files. This OQ-01 focuses on the 2 in `MotivicFlagMaps.lean`.

## Axiom inventory (parent file scope)

| # | File | Name (line) | Type / Role |
|---|---|---|---|
| 1 | `MotivicFlagMaps.lean` | `motivicClassBasedMaps` (L309) | `(n : ℕ) (β : HomologyClass n) : K.carrier` — moduli space class `[Ω²_β(Fl_{n+1})]` in K₀(Var). |
| 2 | `MotivicFlagMaps.lean` | `motivic_class_flag_maps` (L320) | `[Ω²_β(Fl_{n+1})] = [GL_n × A^a]` — main theorem of Bryan–Elek–Manners–Salafatinos–Vakil 2025 (arXiv:2601.07222). |
| 3 | `MotivicFlagMapsPartialFlags.lean` | `motivicClassPartialFlagMaps` (L527) | Partial-flag analogue of #1. **Out of scope for this OQ.** |
| 4 | `MotivicFlagMapsPartialFlags.lean` | `partial_flag_extension` (L563) | Open extension conjecture; states `[Ω²_β(Fl(d₁,...,dₖ; n+1))] = [Levi × U × A^{a'}]`. **Out of scope; genuinely open mathematically.** |

This OQ-01 targets axioms **#1 and #2** in `MotivicFlagMaps.lean`.

## Sibling OQ thread (active)

`motivic-flag-maps-oq-03` ("What does the motivic identity tell us about the topology/cohomology of these moduli spaces?") is an **actively-researched sibling** as of 2026-05-13:
- PR #18299 (S1 OBSERVE, MERGED)
- PR #18401 (S2 PREP divisibility decomposition, MERGED)
- PR #18457 (S2-A PREP `MotivicMeasure` structure, MERGED, +311 LOC)
- PR #18524 (S2 ACT 4 divisibility lemmas, MERGED)
- PR #18744 (S2-A ACT-1 `MotivicMeasure` axiom-free core, OPEN, build pending)

OQ-03 has established that **"Mathlib v4.26.0 has no K_0(Var) infrastructure; realizations must be structure-encoded"** and is building a `MotivicMeasure` structure abstraction. This is directly relevant to OQ-01's goal of axiom removal.

## Mathlib bearer audit (lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

What Mathlib has that is relevant:

| Mathlib path | Content | Bearing on OQ-01 axiom removal |
|---|---|---|
| `Mathlib/AlgebraicGeometry/*` (Schemes, Morphisms, ProjectiveSpectrum, etc.) | Basic scheme theory | Foundation only — no flag varieties, no moduli spaces. |
| `Mathlib/GroupTheory/MonoidLocalization/GrothendieckGroup.lean` | Generic group completion of monoids | Could in principle define `K₀(Var)` as the Grothendieck group of the **isomorphism monoid of varieties** modulo a "cut-and-paste" relation, but the variety category is not in Mathlib. |
| `Mathlib/AlgebraicGeometry/EllipticCurve/Weierstrass.lean` | Sole occurrence of "moduli" | Tangentially related (j-invariant); no general moduli stack. |
| `Mathlib/Algebra/Category/*` | Categorical infrastructure | Useful for defining `Var_k` as a category, but no such category exists. |

What Mathlib does **not** have (verified via GitHub code search at the pinned SHA):
- ❌ `K_0(Var)` (Grothendieck ring of varieties) as a named construction.
- ❌ Flag varieties `Fl(d₁,...,dₖ; n)` or Grassmannians as defined schemes.
- ❌ Moduli spaces of stable maps `M̄_{g,n}(X, β)`.
- ❌ Hilbert schemes.
- ❌ Any "motivic" terminology in Mathlib at the pinned SHA.
- ❌ Quot schemes or any moduli-of-quotients infrastructure.
- ❌ Spaces of based rational maps `Ω²_β(X)`.

## Tractability assessment

Bryan–Elek–Manners–Salafatinos–Vakil 2025 (arXiv:2601.07222) proves the motivic identity `[Ω²_β(Fl_{n+1})] = [GL_n × A^a]` using:
1. Stable map moduli space theory (Kontsevich, late 1990s).
2. Cell-decomposition of `Ω²_β(Fl_{n+1})` via the open cells of based rational maps.
3. Bjørner–Brenti / Knutson–Tao tableaux combinatorics for the affine factor exponent.

These rely on infrastructure that is **multi-person-year to formalize**:
- Moduli of stable maps (~10–30 KLOC, depending on generality).
- K₀(Var) with cut-and-paste relations (~3–5 KLOC).
- Flag varieties as schemes (~2–4 KLOC).
- The BEMSV theorem proper (~5–10 KLOC after the foundations).

**Verdict for this OQ**: removing the 2 axioms in `MotivicFlagMaps.lean` is **not feasible in any single-researcher horizon**. Even after OQ-03's `MotivicMeasure` structure abstraction lands, the axioms remain because:
- Axiom #1 (`motivicClassBasedMaps`) cannot be removed without the actual moduli space.
- Axiom #2 (`motivic_class_flag_maps`) is the BEMSV theorem itself — research-level.

The most tractable next steps are intermediate **structural** refinements that REPLACE the axioms with cleaner axiomatic interfaces (a `MotivicClassOps` typeclass), so downstream proofs depend on a smaller, more focused interface.

## Sub-goal decomposition

### Sub-goal A (TRACTABLE — structure-encoded axiom refinement)
**Replace the 2 raw `axiom` declarations in `MotivicFlagMaps.lean` with a structure-encoded `BEMSVTheoremAxioms` interface that bundles both as fields.**

This is a pure **architectural** refactor: zero new assumptions (per the Axiom Integrity Policy in CLAUDE.md, structure-encoded assumptions count the same as `axiom`), but downstream theorems depend on a cleaner interface that:
- Documents the mathematical dependency surface (BEMSV 2025) in one place.
- Makes future axiom-removal incremental (replace field-by-field).
- Aligns with the OQ-03 `MotivicMeasure` structure pattern.

**Mathlib bearers**: `structure`, no external imports.

**Expected LOC**: 30–60 lines (declaration + downstream usage updates). Risk: low — pure mechanical refactor.

**Axiom count effect on parent**: `axiomCount` goes from 2 to 0 in `MotivicFlagMaps.lean`, but `assumptionCount` is unchanged (per policy, structure fields count too). Honest meta.json update would say `axiomCount: 0, assumptionCount: 2` or equivalent.

### Sub-goal B (HARDER — partial removal via tropical/F_q realization)
**Replace axiom #2 (`motivic_class_flag_maps`) with a WEAKER axiom about the F_q point count.**

The BEMSV identity in K₀(Var) implies, via the F_q-point-count realization homomorphism `K₀(Var) → ℤ[q]`, that
> `#Ω²_β(Fl_{n+1})(F_q) = (q-1)^n · q^a · (some explicit polynomial in q)`.

The F_q-point count for fixed small `n` and `β` is verifiable by combinatorial methods (e.g., counting based rational maps from `P¹` to `Fl_{n+1}` over F_q). This gives a weaker but **falsifiable** axiom: instead of "the motivic identity holds", "the F_q counts match for all `q` and a specific class of `(n, β)`".

**Mathlib bearers**: `Mathlib.Data.Polynomial.*`, finite-field counting. No moduli infrastructure required.

**Expected LOC**: 100–200 lines plus the actual count proofs (which may sorry for `n ≥ 2`).

### Sub-goal C (BLOCKED on Mathlib — multi-month)
**Define `K₀(Var)` and flag varieties as schemes, then formalize BEMSV 2025.**

This is the long-horizon endgame. Requires:
- Building K₀(Var) on top of `Mathlib/GroupTheory/MonoidLocalization/GrothendieckGroup.lean` with a `Var_k` category.
- Defining `Fl(d₁,...,dₖ; n)` as a projective scheme.
- Defining moduli of based rational maps `Ω²_β(X)`.
- Formalizing the BEMSV proof (cell decomposition + tableaux).

**Mathlib bearers**: would require ~10–20 KLOC of new Mathlib content (or sustained Mathlib contributions over many months).

**Tractability**: research-level, multi-person, multi-month minimum.

## Active Approach
None yet. Sub-goal A is the recommended next ACT target — pure refactor, low risk, aligns with active OQ-03 patterns.

## Attempt Count
- Total attempts: 1 (this OBSERVE session)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None for OBSERVE. For sub-goal A: zero. For sub-goal B: requires combinatorial Lean session. For sub-goal C: blocked on Mathlib's lack of moduli space and `K_0(Var)` infrastructure.

## Next Action
Future session: pick up sub-goal A. Define a `BEMSVTheoremAxioms` structure in a fresh `MotivicFlagMapsOQ01.lean` companion file (or refactor in place), bundling both axioms as fields. Downstream theorems consume the structure instance rather than the raw axioms. This is a single-PR refactor, doc-only PREP then ACT.

## Cross-references
- `motivic-flag-maps`: parent.
- `motivic-flag-maps-oq-03`: sibling — actively researched, established the "structure-encoded `MotivicMeasure`" pattern that informs sub-goal A here.
- Mathlib `GrothendieckGroup.lean`: only existing K₀-like primitive at pinned SHA.
