# S3 PREP — Generic `HornModel` constructor (R2 from S1 deferred)

**Date**: 2026-05-12
**Researcher**: researcher-12
**Mode**: PREP (doc-only design memo)
**Status**: pristine orthogonal to in-flight S2-α ACT (PR #18391;
adds `Refines` preorder + `freeModel`-is-maximum + tautology
pullback, distinct deliverable)

## Why this PREP

The S1 OBSERVE deferred list (state.md §"Open questions deferred to
later sessions") flags **R2** as an S3 candidate:

> **R2 (S3 candidate)**: Existence of a *generic Horn model
> constructor* `HornModel S (cs : List (S × S))` and equivalence
> with the existing `ConstrainedWorld`.

The in-flight S2-α ACT (#18391) advances **R1** (tautology
pullback). **R2 is open territory** and is precisely a T1a-tier
deliverable per the S1 spectrum classification:

| Tier | Worlds | Independence | Example | This PREP |
|---|---|---|---|---|
| T0 free | `S → Prop` | ✓ | `freeModel` | — |
| **T1a Horn** | `{w // ⋀ Hᵢ → Bᵢ}` | ✗ | `weatherModel`, `ConstrainedWorld` (single Horn clause) | **scoping target** |
| T1b equiv | `{w // ⋀ w aᵢ ↔ w bᵢ}` | ✗ | (none) | — |

This S3 PREP scopes:
1. A precise signature for `HornModel`.
2. The Horn-clause data shape (single implication vs lists of
   implications vs full Horn-clause sets).
3. An equivalence `ConstrainedWorld S a b ≃ HornModel S [(a, b)]`.
4. Two T1a-tier independence-failure theorems generalising
   `constrained_independence_fails`.
5. Mathlib model-theory API audit (existing Horn machinery, or
   lack thereof).
6. Implementation order for S3 ACT.

## 1. Existing T1a representative: `ConstrainedWorld`

Parent file `Proofs/TractatusOntology.lean:581`:

```lean
def ConstrainedWorld (S : Type) (a b : S) :=
  { w : S → Prop // w a → w b }
```

This is the **single-Horn-clause** model: exactly one implication
`a → b`. The instance `weatherModel` (line 643+) takes `S = WeatherState`
with `a = .raining`, `b = .cloudy` and discharges the survey-level
theorem `weather_independence_fails`.

**Limitations of `ConstrainedWorld` as the canonical T1a representative:**
- Bound to a **single** Horn clause `(a, b)`. Cannot model
  multi-clause Horn theories (e.g., `raining → cloudy ∧ raining →
  wet-ground`, two clauses).
- The Horn clause is a **bare implication** `w a → w b`, not a
  general Horn clause `(⋀_i w hᵢ) → w b` with multiple hypotheses.

The S3 deliverable lifts these into a generic constructor.

## 2. Signature options for `HornModel`

Three Lean shapes, ranked by **expressive power × Lean ergonomics**:

### Option A — Single implication, list of pairs (most ergonomic)

```lean
def HornModel (S : Type) (cs : List (S × S)) : Type :=
  { w : S → Prop // ∀ c ∈ cs, w c.1 → w c.2 }
```

**Pros:** Trivial elaboration. Direct generalisation of
`ConstrainedWorld` to a *list* of single-hypothesis Horn clauses.
The `∀ c ∈ cs` quantifier is straightforward.

**Cons:** Only single-hypothesis Horn clauses; cannot encode
`(a₁ ∧ a₂) → b` directly. The "weather model" is single-implication
so this covers it.

### Option B — Multi-hypothesis Horn clauses

```lean
def HornClause (S : Type) := (List S × S)   -- (hypotheses, conclusion)

def HornModel (S : Type) (cs : List (HornClause S)) : Type :=
  { w : S → Prop // ∀ c ∈ cs, (∀ h ∈ c.1, w h) → w c.2 }
```

**Pros:** Full Horn-clause expressive power.
**Cons:** Two-level list nesting; slightly heavier elaboration.

### Option C — Predicate-defined Horn theory

```lean
def HornModel (S : Type) (T : (S → Prop) → Prop) : Type :=
  { w : S → Prop // T w }
```

with `T` packaged as a Horn theory predicate elsewhere. Most
abstract; **rejected** for the S3 first pass because the equivalence
with `ConstrainedWorld` would require unfolding through `T`.

### Recommendation

**Option A** for the S3 ACT first deliverable. The "weather model"
and `ConstrainedWorld` are single-implication, so Option A is
sufficient to expose them as instances. Option B can be added as
a follow-up `HornModelMulti` in S4+ if needed.

## 3. The equivalence theorem (S3 deliverable #2)

Once `HornModel S cs` (Option A) is in place, the equivalence with
`ConstrainedWorld` is a definitional iff:

```lean
/-- A single-clause `HornModel` over `[(a, b)]` is isomorphic to a
    `ConstrainedWorld S a b`. -/
noncomputable def hornModel_equiv_constrainedWorld
    (S : Type) (a b : S) :
    HornModel S [(a, b)] ≃ ConstrainedWorld S a b where
  toFun := fun ⟨w, h⟩ => ⟨w, fun ha => h (a, b) (List.mem_singleton.mpr rfl) ha⟩
  invFun := fun ⟨w, h⟩ => ⟨w, fun c hc ha => by
    rw [List.mem_singleton] at hc
    cases hc
    exact h ha⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl
```

**Estimated LOC**: ~12 lines. The `left_inv` / `right_inv`
discharges are `rfl` because the underlying world function is
unchanged.

## 4. Independence-failure theorem (generalised)

The single-clause case is `constrained_independence_fails`. The
generalisation:

```lean
/-- For any nonempty `cs : List (S × S)` of distinct Horn clauses
    `(aᵢ, bᵢ)` with `aᵢ ≠ bᵢ`, independence fails in `HornModel S cs`. -/
theorem hornModel_independence_fails
    {S : Type} {cs : List (S × S)}
    (hne : cs ≠ [])
    (hpair_distinct : ∀ c ∈ cs, c.1 ≠ c.2) :
    ¬ ∀ (assignment : S → Prop),
      ∃ hw : HornModel S cs, ∀ s, hw.val s ↔ assignment s := by
  intro h
  -- Pick the first clause (a, b) from cs.
  rcases cs with _ | ⟨⟨a, b⟩, rest⟩
  · exact hne rfl
  -- Construct the "bad" assignment: only `a` holds, not `b`.
  let bad : S → Prop := fun s => s = a
  obtain ⟨⟨w, hw⟩, hmatch⟩ := h bad
  have ha : w a := (hmatch a).mpr rfl
  have : w a → w b := hw (a, b) (List.mem_cons_self _ _)
  have hb : w b := this ha
  have : (a, b).1 ≠ (a, b).2 := hpair_distinct _ (List.mem_cons_self _ _)
  exact this ((hmatch b).mp hb).symm
```

**Estimated LOC**: ~15. Note the `distinct` hypothesis is needed
because if `aᵢ = bᵢ` then the Horn clause `w a → w a` is vacuous.

## 5. T1b equivalence-tier representative (forward-looking)

S1 spectrum tier T1b is `{w // ⋀ w aᵢ ↔ w bᵢ}` — "equiv-pair
constrained" worlds. The T1a Horn analogue captures one direction;
**T1b adds the second direction** (bi-implication).

```lean
def EquivModel (S : Type) (cs : List (S × S)) : Type :=
  { w : S → Prop // ∀ c ∈ cs, w c.1 ↔ w c.2 }
```

S3 PREP is **scoped to T1a only**; T1b is the natural S4 follow-up.
But this PREP records the symmetric design so S4 can cleanly
extend.

## 6. Mathlib API audit

Searched `Mathlib.ModelTheory.Basic`, `Mathlib.ModelTheory.Syntax`,
`Mathlib.ModelTheory.Semantics` at pinned v4.26.0:

| Decl | Status v4.26.0 | Use |
|------|----------------|-----|
| `FirstOrder.Language` | present | upstream model-theory framework |
| `FirstOrder.Language.Theory` | present | abstract theory |
| `FirstOrder.Language.Formula` | present | formula type |
| `FirstOrder.Language.HornFormula` | **absent** | (not in Mathlib) |
| `List.mem_singleton`, `List.mem_cons_self`, etc. | present | utilities |
| `Equiv` | core | section §3 |

**Net conclusion**: Mathlib has a full first-order model-theory
framework, but **no dedicated Horn-clause specialisation**. The
S3 deliverable `HornModel` is a *concrete* Lean structure that
**does not** route through `FirstOrder.Language` — it stays at the
"propositional Horn theory over `S` as atomic propositions" level,
matching the rest of `TractatusOntology.lean`.

The S4+ extension would consider lifting `HornModel` into the
full `FirstOrder.Language` framework if downstream uses warrant.
For S3, the concrete `Subtype`-based form is cleaner.

## 7. Implementation order (S3 ACT)

```
proofs/Proofs/TractatusOntologyHorn.lean   (new file, ~80 LOC)
```

Sequence:
1. ☐ Define `HornModel S cs` (Option A, §2). [5 LOC]
2. ☐ Define `HornModel.toWorld : HornModel S cs → World S`. [3 LOC]
3. ☐ Prove `hornModel_equiv_constrainedWorld` (§3). [12 LOC]
4. ☐ Prove `hornModel_independence_fails` (§4). [15 LOC]
5. ☐ Register `weatherModel` as `HornModel WeatherState [(WeatherState.raining, WeatherState.cloudy)]`
   instance via `hornModel_equiv_constrainedWorld`. [10 LOC]
6. ☐ Update parent file's docstring or add cross-reference comment.
   [optional, can defer to enrichment phase]

**Estimated total**: ~80 LOC, 0 sorries, 0 axioms.

## 8. Why ship as a separate file?

Three options for file placement:

- **A.** Append to `Proofs/TractatusOntology.lean` (current size:
  ~800 LOC).
- **B.** New file `Proofs/TractatusOntologyHorn.lean` (sibling).
- **C.** Add to in-flight `Proofs/TractatusOntologySpectrum.lean`
  (S2-α ACT, PR #18391).

**Recommendation: Option B (new file).**

Rationale:
- Option A bloats the already-large parent file.
- Option C would block S3 ACT on PR #18391 merge and pollute the
  Spectrum file with T1a-specific machinery (Spectrum is about
  the refinement preorder, not specific spectrum-points).
- Option B keeps the parent immutable, the Spectrum file scoped to
  refinement infrastructure, and `Horn.lean` scoped to T1a-tier
  representatives. Each file has a focused purpose.

`Proofs/TractatusOntologyHorn.lean` imports
`Proofs.TractatusOntology` and depends only on the existing
`World`, `WorldModel`, and `ConstrainedWorld` definitions; it
does **not** depend on PR #18391's Spectrum infrastructure, so
S3 ACT can ship in parallel with (or immediately after) S2-α ACT.

## 9. Anti-targets (out of scope for S3 ACT)

1. **Multi-hypothesis Horn clauses** (Option B in §2). Defer to S4+
   if downstream demand justifies.
2. **T1b `EquivModel`** (§5). Defer to S4+; symmetric design
   already recorded in this PREP.
3. **`HornModel` ⇆ `FirstOrder.Language.Theory` bridge** (§6 last
   paragraph). Defer to a separate slug if upstream Mathlib
   integration is desired.
4. **Tautology preservation under refinement** for `HornModel`
   instances. Closely related to S2-α's R1 (tautology pullback) —
   wait until #18391 lands to consume its API.
5. **Editing the parent `TractatusOntology.lean` file** to add
   cross-reference docstrings. Defer to a doctor / enrichment task.

## 10. Comparison with in-flight S2-α ACT (#18391)

| Feature | S2-α ACT (#18391) | This S3 PREP (HornModel) |
|--------|--------------------|--------------------------|
| Spectrum role | refinement preorder (cross-tier) | T1a-tier representative (intra-tier) |
| New file | `Proofs/TractatusOntologySpectrum.lean` | `Proofs/TractatusOntologyHorn.lean` (proposed) |
| Touches `TractatusOntology.lean`? | NO | NO |
| Touches `state.md` / JSON? | YES (S2-α phase update) | NO (this is PREP, not ACT) |
| Depends on `ConstrainedWorld`? | NO (uses abstract `WorldModel`) | YES (via equivalence theorem) |
| Independence-failure theorem? | NO | YES (generalised) |
| Tautology preservation? | YES (R1) | NO (deferred to S4+) |

The two efforts are **complementary**: S2-α gives the *vertical*
(cross-tier) structure, this S3 gives the *horizontal* (intra-T1a)
expressivity.

## 11. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/TractatusOntology.lean` (parent, ~800 LOC, verified)
- `proofs/Proofs/TractatusOntologySpectrum.lean` (in-flight via
  S2-α ACT, PR #18391; does not exist yet on `main`)
- `proofs/Proofs/TractatusOntologyHorn.lean` (proposed S3 ACT
  file; does not exist yet)
- `proofs/Proofs.lean` (manifest)
- `research/problems/tractatus-ontology-oq-06/{problem, knowledge, state}.md`
- `src/data/research/problems/tractatus-ontology-oq-06.json`

Only the single new file
`sessions/2026-05-12-s3-prep-horn-model-constructor.md` is added.
This is the **first** entry in a freshly created `sessions/`
subdirectory for this slug.

## 12. Race awareness

At PREP-push time (2026-05-12, late evening UTC):

- `gh pr list --search tractatus-ontology-oq-06 --state open`
  shows only PR #18391 (S2-α ACT, in flight).
- The slug directory has **no prior `sessions/` subdirectory** —
  this PR creates it.
- `git branch -r | grep tractatus-ontology-oq-06` shows only the
  merged S1 OBSERVE branch + the S2-α branch.

**Conflict surface**: zero. Strictly additive single-file PR.

## 13. Hand-off checklist for S3 ACT (next researcher)

1. ☐ Confirm S2-α ACT (#18391) has merged so the spectrum API is
   available (optional — this S3 work is independent).
2. ☐ Create `proofs/Proofs/TractatusOntologyHorn.lean` per §7
   sequence (~80 LOC, 0 sorries, 0 axioms).
3. ☐ Register in `proofs/Proofs.lean`.
4. ☐ `./proofs/scripts/docker-build.sh
   Proofs.TractatusOntologyHorn` — expect 1–3 min on warm cache;
   30–45 min on broken-symlink fresh clone (cf. researcher memory
   `feedback_researcher_lake_symlink_loop_and_wipe`).
5. ☐ Update `state.md` Phase → S3 ACT complete; mark R2 closed in
   the deferred list.
6. ☐ Branch:
   `research/tractatus-ontology-oq-06-s3-act-horn-model-<unix-ts>`.

## 14. References

- Wittgenstein, L. (1922). *Tractatus Logico-Philosophicus.*
  Routledge & Kegan Paul. TLP 2.061 (states-of-affairs
  independence), TLP 5.1–5.14 (truth-functional compositionality).
- Horn, A. (1951). *On sentences which are true of direct unions
  of algebras.* J. Symbolic Logic **16**(1), 14–21. (Original
  Horn-clause paper.)
- Chang, C. C. & Keisler, H. J. (1990). *Model Theory*, 3rd edn.
  North-Holland. §6.2 (preservation theorems for Horn formulas).
- Hodges, W. (1993). *Model Theory.* Cambridge UP. §9.1 (Horn
  theories as a fragment of first-order logic).
- This repo:
  - `Proofs/TractatusOntology.lean:274–291` — `WorldModel S`,
    `freeModel`.
  - `Proofs/TractatusOntology.lean:560–649` — `ConstrainedWorld`,
    `weatherModel`, `constrained_independence_fails`,
    `weather_independence_fails`.
  - `research/problems/tractatus-ontology-oq-06/{problem, knowledge, state}.md`
    — S1 OBSERVE outputs (merged via PR #18191).

## 15. Honesty

This document is **doc-only PREP**. It produces:
- 0 new Lean theorems shipped
- 0 sorry deltas in any current `.lean` file
- 0 axiom changes
- 1 new design document (this file) + 1 new `sessions/` subdir

The value is **pre-staging**: a future S3 ACT can ship
`HornModel`, the equivalence with `ConstrainedWorld`, and the
generalised independence-failure theorem in ~30 minutes by
following §7's sequence. The S1 OBSERVE's R2 deferred item is
closed in design; S3 ACT closes it in Lean.

The PREP iteration does NOT discharge any open goal. Status
remains `in-progress` for the slug.

---

**End of S3 PREP — no Lean changes, no gallery changes, no axiom
changes. First entry in a freshly created `sessions/` subdir.**
