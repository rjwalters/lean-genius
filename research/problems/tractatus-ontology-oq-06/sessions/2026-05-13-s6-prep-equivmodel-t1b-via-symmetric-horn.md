# S6 PREP — `EquivModel` / T1b spectrum-tier via symmetric Horn closure

**Date**: 2026-05-13
**Researcher**: researcher-3
**Mode**: PREP (doc-only design memo)
**Phase target**: S6 ACT (Lean realisation), ~50–80 LOC append to a
new `TractatusOntologyEquiv.lean` (or sibling location after S3 ACT
lands `TractatusOntologyHorn.lean`).
**Status**: pristine orthogonal to merged S2-α ACT (#18391), merged
S3 PREP (#18417), merged S4 PREP (#18470), and merged S5 PREP
(#18478). 0 open PRs on this slug at PREP push time.

## Why this PREP

S3 PREP §5 (`2026-05-12-s3-prep-horn-model-constructor.md` lines
167–180) introduced the T1b tier signature

```lean
def EquivModel (S : Type) (cs : List (S × S)) : Type :=
  { w : S → Prop // ∀ c ∈ cs, w c.1 ↔ w c.2 }
```

then deferred it as "the natural S4 follow-up". S4 PREP §13.1
(`2026-05-13-s4-prep-refines-lattice-via-image-profiles.md` lines
418–419) re-acknowledged the deferral: "Implement `EquivModel` /
T1b. That's S2-β / S3+ territory (R2 covers Horn / T1a; T1b
symmetric equivalence is for after Horn)."

S5 PREP (`freeModel` uniqueness via `HasIndependentProfiles`) does
not touch T1b at all.

Hence T1b is the **explicitly-deferred next architectural angle**
with no PREP in flight. This PREP fills the gap.

**Key architectural observation** (not yet recorded in any prior
session note): T1b is **not** a genuinely independent spectrum
tier. The biconditional `w a ↔ w b` is the conjunction of two
implications `(w a → w b) ∧ (w b → w a)`. Hence:

> **EquivModel S cs ≃ HornModel S (cs ++ cs.map Prod.swap)**

T1b is the **symmetric-closure subclass** of T1a, not a sibling
tier. This memo scopes the precise statement, gives the
~10-LOC equivalence proof, and discusses whether the four-tier
spectrum should be revised to a three-tier one (T0 / T1-Horn /
T2 Kripke / T3 quotient, with T1b folded into T1-Horn-symmetric).

## 1. The right signature

S3 PREP §5 already locked the signature (lines 173–176). For
self-containment of S6 ACT:

```lean
/-- Tier T1b: equivalence-constrained world model.
    Each pair `(a, b) ∈ cs` constrains worlds to satisfy
    `w a ↔ w b`, i.e., `a` and `b` are in the same "truth
    block". This is the T1b spectrum-tier sister to T1a (`HornModel`). -/
def EquivModel (S : Type) (cs : List (S × S)) : Type :=
  { w : S → Prop // ∀ c ∈ cs, w c.1 ↔ w c.2 }
```

**Constructor**: there is always at least one world — the
constantly-true and constantly-false functions both satisfy every
biconditional, so `EquivModel S cs` is non-empty for every `S`
and every `cs`. (S3 PREP §3 noted the analogous fact for
`HornModel`.)

## 2. The S6 ACT main result: T1b ⊆ T1a-symmetric

The architectural observation:

```lean
/-- Every T1b model is a T1a model under symmetric-pair closure of
    the constraint list. -/
def equivModel_iso_hornModel_symm (cs : List (S × S)) :
    EquivModel S cs ≃ HornModel S (cs ++ cs.map Prod.swap) where
  toFun := fun ⟨w, hw⟩ => ⟨w, by
    intro c hc
    rcases List.mem_append.mp hc with h | h
    · exact (hw c h).mp
    · rcases List.mem_map.mp h with ⟨⟨a, b⟩, hab, rfl⟩
      exact (hw (a, b) hab).mpr⟩
  invFun := fun ⟨w, hw⟩ => ⟨w, by
    intro c hc
    constructor
    · exact hw c (List.mem_append.mpr (Or.inl hc))
    · have : (c.2, c.1) ∈ cs.map Prod.swap :=
        List.mem_map.mpr ⟨c, hc, rfl⟩
      exact hw (c.2, c.1) (List.mem_append.mpr (Or.inr this))⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
```

Estimated body: ~20 LOC inline. **No new axioms; no sorries.**

The `left_inv` / `right_inv` `rfl`-closures hold because the
underlying `World S` is the same — only the `Subtype` predicate
list changes, and the predicate values agree pointwise.

## 3. Refinement preorder: T1b refines into T1a

A T1b model is **strictly more constrained** than the T1a model
sharing its (asymmetric) constraint list:

```lean
/-- An equivalence-constrained model refines into the
    corresponding Horn-constrained model. -/
theorem refines_equivModel_hornModel (cs : List (S × S)) :
    Refines (equivModel_to_worldModel cs) (hornModel_to_worldModel cs) := by
  refine ⟨Subtype.map id ?_, ?_⟩
  · -- every EquivModel world satisfies the asymmetric constraints
    intro w hw c hc
    exact (hw c hc).mp
  · intro w s
    exact Iff.rfl  -- holds is the same; only the predicate differs
```

Estimated body: ~6 LOC. The map `Subtype.map id` lifts to the
underlying world without rewriting; only the `Subtype` predicate
filtering loosens.

**Symmetry observation**: the converse direction
`Refines (hornModel cs) (equivModel cs)` is **false in general** —
e.g., for `cs = [(a, b)]`, the HornModel admits the world
`w a = true, w b = true, w c = false`, but the EquivModel forces
biconditional constraints that the asymmetric Horn does not
demand. Concretely, the witness world `(a ↦ false, b ↦ true)` is
in `HornModel S [(a, b)]` (since `false → b` is vacuously true)
but **not** in `EquivModel S [(a, b)]` (since `false ↔ true` is
false). So Refines is strict in this direction.

## 4. Independence-failure for T1b

Generalisation of S3 PREP §4's `hornModel_independence_fails`:

```lean
theorem equivModel_independence_fails (cs : List (S × S))
    (hcs : cs ≠ []) (hpair_distinct : ∀ c ∈ cs, c.1 ≠ c.2) :
    ¬ HasIndependentProfiles (equivModel_to_worldModel cs) := by
  intro habs
  rcases cs with _ | ⟨⟨a, b⟩, rest⟩
  · exact hcs rfl
  -- target the assignment a := True, b := False
  rcases habs (fun s => s = a) with ⟨⟨w, hw⟩, hmatch⟩
  have ha : w a := (hmatch a).mpr rfl
  have hb : ¬ w b := by
    intro h
    have : b = a := (hmatch b).mp h
    exact hpair_distinct (a, b) (List.mem_cons_self _ _) this.symm
  exact hb ((hw (a, b) (List.mem_cons_self _ _)).mp ha)
```

Estimated body: ~10 LOC. **Same shape as
`hornModel_independence_fails` but uses `.mp` directly because the
EquivModel's biconditional is symmetric in both directions.**

Note: the distinct-elements hypothesis `c.1 ≠ c.2` is needed for
the same reason as the Horn case — a self-pair `(a, a)` makes the
biconditional `w a ↔ w a` vacuous and the model degenerates to
T0.

## 5. Cardinality counting (optional S6+ extension)

`EquivModel S cs` partitions `S` into equivalence classes under the
transitive-symmetric closure `≈_cs`. Each class is "all-true or
all-false" in a given world; different classes choose independently.

```
|EquivModel S cs| = 2^(number of ≈_cs-equivalence classes on S)
```

This is the **principal counting theorem** for T1b. For `cs = []`
it gives `|S → Prop|` (the freeModel). For each constraint `(a, b)`
that connects two distinct classes, the count halves.

S6 ACT can defer the cardinality theorem to S7+; it's not needed
for the spectrum architecture but is a natural follow-up.

```lean
-- Sketch (deferred):
theorem equivModel_card (S : Type) [Fintype S] (cs : List (S × S)) :
    Fintype.card (EquivModel S cs) =
      2 ^ (Quotient (equivClasses cs)).card := sorry
```

(Uses `Quotient` from Mathlib core; the `equivClasses cs` definition
constructs the setoid generated by `cs`. Both are standard.)

## 6. Spectrum architecture: should T1b be folded into T1-Horn?

The S1 OBSERVE four-tier classification was:

| Tier   | Worlds                          | Example                               |
|--------|---------------------------------|---------------------------------------|
| T0     | `S → Prop`                      | `freeModel`                           |
| T1a    | `{w // ⋀ Hᵢ → Bᵢ}`             | `weatherModel`, `ConstrainedWorld`    |
| **T1b**| `{w // ⋀ w aᵢ ↔ w bᵢ}`         | (none yet — this PREP scopes it)      |
| T2     | indexed + accessibility          | (out of scope)                        |
| T3     | `(S → Prop) /~`                 | (out of scope)                        |

Per §2 (`equivModel_iso_hornModel_symm`), **T1b ⊆ T1a** as
definable types: every T1b is iso to a T1a with a symmetric
Horn list. The four-tier classification is therefore
**redundant in the T1a/T1b split**.

Three options for the spectrum architecture going forward:

### Option A — Keep the four-tier classification (least disruption)

Keep T1a and T1b as separate names because the **idiomatic
constructor signatures differ** (one takes asymmetric pairs, one
takes biconditional pairs), even though the underlying types are
iso under symmetric-closure. Document the equivalence in S6 ACT
as a "T1b is implementable on top of T1a" note.

### Option B — Collapse to three-tier (T0 / T1 / T2 / T3)

Drop the T1a/T1b distinction. The Horn constructor `HornModel`
becomes the **canonical T1 representative**, and T1b is just
"T1 with a symmetric constraint list".

### Option C — Keep both, but record the subsumption

Both `HornModel` and `EquivModel` ship as named constructors
(ergonomics matter — `EquivModel cs` is more readable than
`HornModel (cs ++ cs.map Prod.swap)`), but the spectrum analysis
explicitly notes T1b is a sub-spectrum of T1a.

**Recommendation**: Option C. Concrete reasoning:

1. Lean-side ergonomics favour both names being available
   (e.g., a "two-name iff" model is most naturally `EquivModel`,
   not `HornModel` with a 4-element list).
2. The iso (`equivModel_iso_hornModel_symm`) gives a one-line
   conversion when needed.
3. The spectrum analysis (refinement preorder, independence
   failures, etc.) gets *uniform* treatment — each named tier
   gets one independence-failure theorem (already in this PREP §4)
   and one refinement theorem (§3) without coupling them through
   the iso.

Either way, the **knowledge.md and state.md** spectrum tables
should record the new finding: T1b is structurally subsumed by
T1a under symmetric closure.

## 7. Mathlib API audit

Only routine Mathlib used:

| Lemma / Def                              | Path                                          | Use            |
|------------------------------------------|-----------------------------------------------|----------------|
| `List.mem_append`                        | `Mathlib/Data/List/Basic.lean` (core)         | §2, §4         |
| `List.mem_map`                           | `Mathlib/Data/List/Basic.lean` (core)         | §2             |
| `List.mem_cons_self`                     | `Mathlib/Data/List/Basic.lean` (core)         | §4             |
| `Prod.swap`                              | core                                          | §2             |
| `Subtype.map`                            | core                                          | §3             |
| `Quotient` (for §5 cardinality, optional)| core                                          | §5             |
| `Fintype.card` (for §5 cardinality, optional) | `Mathlib/Data/Fintype/Card.lean`          | §5             |

**No exotic API**, no `FirstOrder.Language` integration, no new
imports beyond what S3 ACT's `TractatusOntologyHorn.lean` will
already bring in. S6 ACT consequently depends only on:

1. S3 ACT having shipped (so `HornModel` is in the type
   environment for §2's iso).
2. S2-α ACT (already merged via #18391) for the `Refines`
   predicate used in §3.

S5 ACT and S4 ACT are **not** prerequisites for S6 ACT. S6
ACT can ship in parallel with either.

## 8. Implementation order for S6 ACT

```
proofs/Proofs/TractatusOntologyEquiv.lean  (new file, ~60-80 LOC)
```

Sequence:

1. ☐ Import `Proofs.TractatusOntologyHorn` (assumes S3 ACT shipped).
2. ☐ Define `EquivModel S cs` (S3 PREP §5 signature). [5 LOC]
3. ☐ Define `EquivModel.toWorld : EquivModel S cs → World S`. [3 LOC]
4. ☐ Define `equivModel_to_worldModel`. [5 LOC]
5. ☐ Prove `equivModel_iso_hornModel_symm` (§2). [~20 LOC]
6. ☐ Prove `refines_equivModel_hornModel` (§3). [~6 LOC]
7. ☐ Prove `equivModel_independence_fails` (§4). [~10 LOC]
8. ☐ (Optional) define `equivClasses` setoid and prove
   `equivModel_card` (§5). [~25 LOC, defer to S7+]
9. ☐ Update parent docstring or add cross-reference comment.

**Estimated total** (without §5): ~60 LOC, 0 sorries, 0 new
axioms.

## 9. File placement: sibling vs append

Three options for file placement (same trichotomy as S3 PREP §8):

- **A.** Append to `Proofs/TractatusOntology.lean` — bloats parent.
- **B.** New file `Proofs/TractatusOntologyEquiv.lean` (sibling).
- **C.** Append to `Proofs/TractatusOntologyHorn.lean` (S3 ACT's
   file).

**Recommendation: Option B.** Same rationale as S3 PREP §8 —
keep the parent immutable, scope each spectrum-tier to one file,
each file gets a focused purpose. `TractatusOntologyEquiv.lean`
will be smaller than the Horn file (no multi-clause-Horn
extension scope).

If S3 ACT ships `TractatusOntologyHorn.lean` with sufficiently
generic constructor design, S6 ACT could alternatively *extend*
that file (Option C) — but this couples T1a and T1b updates. Option B
remains the preferred independent-scope choice.

## 10. Race awareness / orthogonality

At PREP push time (2026-05-13 ~03:15 UTC):

| Open PR | Slug | File overlap with this PREP | Conclusion |
|---------|------|------------------------------|------------|
| (none on this slug) | tractatus-ontology-oq-06 | — | Fully orthogonal |

This PREP creates exactly one new file:
`research/problems/tractatus-ontology-oq-06/sessions/2026-05-13-s6-prep-equivmodel-t1b-via-symmetric-horn.md`.

No `gh pr list --search "tractatus-ontology-oq-06 equiv"`,
"T1b", or "EquivModel" rows in any state at PREP draft time.

The merged precursor PREPs reference `EquivModel`/T1b only as a
deferral target (S3 PREP §5 line 167, S4 PREP §13.1 line 418).
This PREP picks up the deferred work and locks the architecture
for S6 ACT.

## 11. Anti-targets (out of scope for S6 PREP)

This PREP **does not**:

- Edit `proofs/Proofs/TractatusOntology.lean`,
  `proofs/Proofs/TractatusOntologySpectrum.lean`,
  `proofs/Proofs/TractatusOntologyHorn.lean` (not yet existing per
  S3 ACT not having shipped), or any other Lean file.
- Edit `state.md`, `problem.md`, `knowledge.md`, or any prior
  `sessions/` doc.
- Edit `src/data/proofs/tractatus-ontology/meta.json` or
  `src/data/research/problems/tractatus-ontology-oq-06.json`.
- Ship `equivModel_card` (the §5 cardinality theorem) — deferred
  to S7+ as optional.
- Resolve the spectrum-architecture question (§6 Options A/B/C) —
  the recommendation is C but the final decision lives in S6 ACT.
- Touch the `FirstOrder.Language` Mathlib bridge — deferred per
  S3 PREP §6.

## 12. Acceptance criteria for S6 ACT (binary)

The S6 ACT PR (the Lean implementation) must:

- [ ] Define `EquivModel S cs` with the signature in §1.
- [ ] Prove `equivModel_iso_hornModel_symm` (§2) — the core
      architectural result.
- [ ] Prove `refines_equivModel_hornModel` (§3).
- [ ] Prove `equivModel_independence_fails` (§4).
- [ ] 0 sorries, 0 new axioms.
- [ ] ≤ 80 LOC for the new file (excluding optional §5).
- [ ] Build successfully via
      `./proofs/scripts/docker-build.sh Proofs.TractatusOntologyEquiv`.
- [ ] Add cross-reference back to S3 ACT's `HornModel` and to
      this PREP doc.
- [ ] Update `state.md` "Sessions" list with the S6 entry.
- [ ] (If §6 Option C accepted) update `knowledge.md` /
      `state.md` spectrum table to record "T1b is structurally
      subsumed by T1a-symmetric".

The S6 ACT PR **must NOT**:

- Resolve the optional §5 cardinality theorem in the same PR
  (defer to S7+).
- Edit the parent file (`TractatusOntology.lean`).
- Refactor S3 ACT's `HornModel` (§2's iso bridges the two; no
  modification of the Horn side is needed).
- Add new Mathlib imports beyond what `TractatusOntologyHorn`
  already brings in.

## 13. Honesty / scope guarantee

This PREP is **doc-only**:

- 1 new file: `research/problems/tractatus-ontology-oq-06/sessions/2026-05-13-s6-prep-equivmodel-t1b-via-symmetric-horn.md`
- 0 edits to existing files
- 0 Lean changes
- 0 gallery / research JSON changes
- 0 changes to `state.md`, `problem.md`, `knowledge.md`, or
  earlier session notes

**Scope honesty**: the §2 iso (`equivModel_iso_hornModel_symm`)
is a **structural** equivalence — the underlying world type is
the same `S → Prop`, only the `Subtype` predicate differs.
Consequently, the iso is `rfl`-able on the world side (the
`left_inv` / `right_inv` proofs reduce to `rfl`). This makes T1b
"cheap" relative to T1a from the Lean-implementation
perspective: T1b adds no genuinely new structural challenge,
only an ergonomic constructor.

**Architecture honesty**: §6 records a possible spectrum-table
revision (drop the T1a/T1b distinction), but the recommendation
is Option C (keep both names, document the subsumption). The
final architecture decision is deferred to the S6 ACT author.

## 14. References

- S1 OBSERVE: PR #18191
  (`research/tractatus-ontology-oq-06-s1`, merged
  2026-05-12 16:10 UTC). Established the four-tier spectrum.
- S2-α ACT: PR #18391
  (`research/tractatus-ontology-oq-06-s2-alpha-*`, merged
  2026-05-13 00:03 UTC). `Refines` preorder + `freeModel`
  maximum.
- S3 PREP: PR #18417
  (`2026-05-12-s3-prep-horn-model-constructor.md`, merged
  2026-05-13 00:46 UTC). Source of the `EquivModel` deferral.
- S4 PREP: PR #18470
  (`2026-05-13-s4-prep-refines-lattice-via-image-profiles.md`,
  merged 2026-05-13 02:24 UTC). Re-acknowledged T1b deferral.
- S5 PREP: PR #18478
  (`2026-05-13-s5-prep-freemodel-uniqueness-via-independence.md`,
  merged 2026-05-13 02:35 UTC). `HasIndependentProfiles`
  predicate.
- Parent file: `proofs/Proofs/TractatusOntology.lean`
  (`ConstrainedWorld` at line 581, `weatherModel` at line ~643).
- Spectrum companion: `proofs/Proofs/TractatusOntologySpectrum.lean`
  (S2-α ACT artifact).
