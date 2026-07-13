# Problem: Club and Stationary Set Library for Mathlib

## Statement

### Plain Language

Refactor the club / stationary-set / regressive-function infrastructure
currently sitting inside `proofs/Proofs/FodorPressingDown.lean` (385
lines) into a standalone, Mathlib-style library file, analogous to
`Mathlib.SetTheory.Ordinal.Topology`. The downstream goal is to expose
this infrastructure for **reuse** by sister open questions on Fodor /
Solovay-type results (in particular `fodor-pressing-down-oq-04`,
Solovay splitting) without forcing each downstream file to redefine
`IsClubBelow` / `IsStationaryBelow` / `diagInter`.

### Formal Signature Targets

Three definitional anchors and three theorem anchors. All operate on
`Set Ordinal` (no universe variable in the API; the local file pins
`κ : Cardinal.{0}`, which we preserve until the universe-polymorphic
extension is requested separately).

```lean
-- §1. Unboundedness in an interval [0, o)
def Ordinal.IsUnboundedBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ α < o, ∃ β ∈ S, α < β ∧ β < o

-- §2. Closed-unbounded ("club") set strictly below o
structure Ordinal.IsClubBelow (S : Set Ordinal) (o : Ordinal) : Prop where
  subset_Iio : S ⊆ Set.Iio o
  closed     : IsClosedBelow S o
  unbounded  : Ordinal.IsUnboundedBelow S o

-- §3. Stationarity below o (meets every club below o)
def Ordinal.IsStationaryBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C : Set Ordinal, Ordinal.IsClubBelow C o → (S ∩ C).Nonempty

-- §4. Diagonal intersection of an ordinal-indexed family below o
def Ordinal.diagInter (f : Ordinal → Set Ordinal) (o : Ordinal) : Set Ordinal :=
  {γ | γ < o ∧ ∀ β < γ, γ ∈ f β}

-- §5. Regressiveness (currently inline in fodor's proof)
def Ordinal.IsRegressive (f : Ordinal → Ordinal) (S : Set Ordinal) : Prop :=
  ∀ ⦃α⦄, α ∈ S → α ≠ 0 → f α < α

-- §6. Diagonal intersection of clubs is a club (key combinatorial input to Fodor)
theorem Ordinal.diagInter_isClubBelow {f : Ordinal → Set Ordinal} {κ : Cardinal.{0}}
    (hκ : ℵ₀ ≤ κ.ord.cof) (hκ_unc : ω < κ.ord)
    (hf : ∀ β < κ.ord, Ordinal.IsClubBelow (f β) κ.ord) :
    Ordinal.IsClubBelow (Ordinal.diagInter f κ.ord) κ.ord

-- §7. The Fodor lemma itself (statement preserved verbatim)
theorem Ordinal.fodor {κ : Cardinal.{0}} (hκ_reg : κ.IsRegular) (hκ_unc : ω < κ.ord)
    {S : Set Ordinal} (hS : Ordinal.IsStationaryBelow S κ.ord)
    {f : Ordinal → Ordinal} (hf_reg : Ordinal.IsRegressive f S)
    (hf_range : ∀ α ∈ S, f α < κ.ord) :
    ∃ c < κ.ord, Ordinal.IsStationaryBelow (S ∩ f ⁻¹' {c}) κ.ord
```

### Refactor Deliverable

A new file `proofs/Proofs/Club/Basic.lean` (or
`Mathlib/SetTheory/Ordinal/Club.lean`-style placement inside the
`Proofs/` tree, see Naming Conventions below) that **re-houses** every
definition and lemma whose signature reads `IsClubBelow … o` /
`IsStationaryBelow … o` / `diagInter …` in the *local-to-Fodor* file.
The file becomes a downstream consumer that imports the new module and
keeps only the *Fodor-specific* witness construction (the "zipper"
ω-supremum trick inside `diagInter_isUnboundedBelow`'s proof body, the
contradiction step inside `fodor`).

Acceptance criteria (binary):

1. `Ordinal.IsClubBelow`, `Ordinal.IsStationaryBelow`,
   `Ordinal.IsUnboundedBelow`, `Ordinal.diagInter`,
   `Ordinal.IsRegressive` live in the new file in the `Ordinal`
   namespace (or — if community review prefers — in
   `Set` for `IsClub` / `IsStationary` analogously to `Set.Unbounded`).
2. `proofs/Proofs/FodorPressingDown.lean` shrinks by **≥ 150 lines**
   and contains only: imports, the zipper construction, the Fodor
   theorem, the docstring.
3. The new file compiles with `0` sorries.
4. The Fodor theorem retains its existing signature (up to namespace
   prefix); the gallery `meta.json` `theoremCount` for
   `fodor-pressing-down-oq-04` is unchanged.
5. Sister slug `fodor-pressing-down-oq-04` (Solovay splitting) gains
   a clean dependency path: its eventual Lean file `imports
   Proofs.Club.Basic` and uses `Ordinal.IsStationaryBelow` directly
   without re-declaring it.

### Why a Refactor (Not a Conjecture)

OQ-01 is a **library/refactor** open question: no new mathematical
content is proved, but a substantial design decision (naming,
universe-polymorphism boundary, structure-vs-Prop choice for
`IsClubBelow`) is made, and downstream maintenance burden for the
entire Fodor / Solovay family is reduced. Treating it as a research
problem — rather than as a `loom:doctor` task — is appropriate because:

- It is **not bug-driven** (no broken build, no audit issue, no review
  request).
- It requires substantive **Mathlib alignment research** to decide
  naming and to identify which API choices match Mathlib's existing
  `Set.Unbounded` / `Ordinal.IsAcc` / `Mathlib.SetTheory.Cardinal.Cofinality`
  conventions.
- The sister slug `fodor-pressing-down-oq-04` will inherit the design;
  doing the refactor *once* (here) avoids cascading rework when the
  Solovay file is written.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - seeker-selected
  - set-theory
  - ordinals
  - cardinals
  - clubs
  - stationary
  - fodor
  - mathlib
  - refactor
  - library
```

**Significance**: 6/10 — high reuse value across the Fodor family but
no new mathematical content. Refactors of this size (~150 LOC moved,
~5 definitions exposed, ~3 lemmas exposed) are a known Mathlib pull-
request shape; downstream consumers in the gallery accumulate
linearly.

**Tractability**: 6/10 — the refactor is mechanical *once a naming
convention is locked*. The locking is what S1 OBSERVE delivers. S2
moves definitions; S3 moves lemmas; S4 trims the parent file; each
step is build-pending-tolerant (no proof-state changes).

## Why This Matters

1. **Library debt reduction.** The local `IsClubBelow` /
   `IsStationaryBelow` predicates currently sit in a single
   `FodorPressingDown.lean` and are inaccessible to any sibling file.
   Solovay splitting (OQ-04, currently in NEW phase, seeker-fresh
   2026-05-12 14:35 UTC), Erdős-Tarski stationary set rigidity, and
   Galvin's theorem are all stationary-set arguments that would
   otherwise each redefine the same predicates.
2. **Mathlib upstreaming path.** A clean library file in `Proofs/Club/`
   is the obvious upstream candidate (`Mathlib.SetTheory.Ordinal.Club`),
   and the design decisions made here (namespace, universe, structure-
   vs-Prop) become the de-facto Mathlib API once accepted.
3. **Sister-slug enablement.** `fodor-pressing-down-oq-04` will start
   with `import Proofs.Club.Basic` and use the public API; no
   research-time will be spent on duplicating club infrastructure.

## Related Gallery Proofs

| Proof / Slug                          | Relevance                                                   |
|---------------------------------------|-------------------------------------------------------------|
| `fodor-pressing-down`                 | Parent: hosts the current local infrastructure to be lifted |
| `fodor-pressing-down-oq-04`           | Sister: Solovay splitting, primary downstream consumer      |
| `Mathlib.SetTheory.Ordinal.Topology`  | Design analog (already in Mathlib upstream)                 |
| `Mathlib.SetTheory.Cardinal.Cofinality` | Source of `Cardinal.cof`, `Cardinal.IsRegular`            |
| `Mathlib.SetTheory.Cardinal.Regular`  | Source of regularity lemmas used by `diagInter`             |

## Open Questions (sub-OQs of this refactor)

- **OQ-01-A**: Should the API be **structure-based** (`IsClubBelow` is
  a structure with three fields) or **Prop-only** (`IsClubBelow S o :=
  S ⊆ Iio o ∧ IsClosedBelow S o ∧ IsUnboundedBelow S o`)? Mathlib's
  `IsRegular` is a structure; `IsAcc` is a Prop. Decision deferred to
  S2 ACT (with default leaning structure to match local file).
- **OQ-01-B**: Universe polymorphism. The local file pins
  `κ : Cardinal.{0}` (small ordinals). Should the new API be
  universe-polymorphic? Decision: **no, S2 preserves `Cardinal.{0}`**;
  a follow-up OQ-01-A.U can polymorph later if a use case appears.
- **OQ-01-C**: Should `diagInter` live in `Proofs/Club/Basic.lean` or
  in a separate `Proofs/Club/DiagonalIntersection.lean`? Decision
  deferred to S2 ACT.

## References

- Fodor, G. (1956). "Eine Bemerkung zur Theorie der regressiven
  Funktionen." *Acta Sci. Math. (Szeged)* 17: 139–142.
- Jech, T. (2003). *Set Theory* (3rd ed.). Springer. Theorem 8.7
  (Fodor's lemma) and §8 (clubs and stationary sets).
- Kunen, K. (2011). *Set Theory: An Introduction to Independence
  Proofs*. North-Holland. Theorem II.6.15 (Fodor) and §II.6 (clubs).
- Solovay, R. M. (1971). "Real-valued measurable cardinals." In
  *Axiomatic Set Theory*. Provides the splitting theorem (OQ-04's
  goal) using the same club/stationary infrastructure.
- Lean Mathlib: `Mathlib.SetTheory.Ordinal.Topology` (existing
  ordinal-topology API, design analog), `Mathlib.SetTheory.Cardinal.
  Cofinality` (cofinality / regularity), `Mathlib.SetTheory.Cardinal.
  Regular` (regularity lemmas).
