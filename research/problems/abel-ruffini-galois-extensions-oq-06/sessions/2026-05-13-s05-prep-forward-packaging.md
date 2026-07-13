# S5 PREP — Forward-direction packaging theorem (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-12
**Phase**: PREP (orientation for the *forward-direction conclusion*
theorem, downstream of S3 ACT PR #18399 and S4 PREP PR #18448).
**Type**: Doc-only design memo. No edits to Lean files, `state.md`,
`problem.md`, `knowledge.md`, the in-flight PR #18399 / PR #18448
`sessions/` notes, gallery `meta.json`, or research JSON.

## 0. Why this PREP

After the in-flight PRs land, the slug will have **three** standalone
facts on `AGL1Z p` (for `[Fact p.Prime]`):

| Fact                                    | Provided by             | Status (2026-05-13 ~02:10 UTC) |
|-----------------------------------------|-------------------------|---------------------------------|
| `IsSolvable (AGL1Z p)`                  | PR #18399 (S3 ACT)      | build pending                   |
| `Function.Injective (AGL1Z.toPerm p)`   | PR #18399 (S3 ACT)      | build pending                   |
| `IsPreprimitive (AGL1Z p) (ZMod p)`     | post-#18448 (S4 ACT)    | PR #18448 PREP merged 02:06 UTC; S4 ACT not started |

None of those three facts, **on their own**, expresses the "forward
direction" of Galois's classification:

> AGL(1, p) embeds into S_p as a primitive solvable subgroup of order p(p-1).

The conclusion above is `∃ H : Subgroup (Equiv.Perm (ZMod p)), …` —
i.e. a *subgroup-of-S_p* witness, not a *group-with-action* witness.

This PREP pre-stages an S5 ACT theorem that **packages** the three
facts above into the slug-level forward conclusion. The deliverable
is ~30–60 LOC depending on which packaging layer is chosen and 0
sorries / 0 axioms. The PREP also identifies the **one load-bearing
tactical step** (primitivity transfer along `MonoidHom.rangeRestrict`)
and provides Mathlib citations + fallbacks.

This PREP is orthogonal to PR #18399 (different file, different
theorem, different sessions/ note) and to PR #18448 (different
theorem; PR #18448 covers `IsPreprimitive (AGL1Z p) (ZMod p)`, this
PREP covers what to do *after* that lands).

## 1. Two packaging layers

### 1.1 Layer A — "Lite packaging" (3-conjunct)

Trivial post-S4: just a conjunction.

```lean
/-- **(S5-Lite)** Forward direction, conjunctive form: AGL(1, p) is
    solvable, acts faithfully on `ZMod p`, and that action is
    preprimitive. -/
theorem AGL1Z_isSolvableFaithfulPreprimitive (p : ℕ) [Fact p.Prime] :
    IsSolvable (AGL1Z p) ∧
    Function.Injective (AGL1Z.toPerm p) ∧
    MulAction.IsPreprimitive (AGL1Z p) (ZMod p) :=
  ⟨inferInstance, AGL1Z.toPerm_injective p, inferInstance⟩
```

Size: ~6 LOC. 0 sorries, 0 axioms. Uses only `inferInstance` for
`IsSolvable` (from #18399) + `IsPreprimitive` (from S4 ACT) and the
already-named `toPerm_injective` (from #18399).

This is the **minimum viable packaging** — it shows the slug is
complete in the conjunctive sense.

### 1.2 Layer B — "Subgroup packaging" (existential subgroup of S_p)

The mathematically faithful form: AGL(1, p) embeds into S_p as a
*subgroup* with the same properties.

```lean
/-- **(S5-Full)** Forward direction, subgroup-of-S_p form: there is a
    subgroup `H` of `Equiv.Perm (ZMod p)` which is solvable, acts
    preprimitively on `ZMod p`, and has order `p * (p - 1)`. -/
theorem AGL1Z_forward_witness (p : ℕ) [Fact p.Prime] :
    ∃ H : Subgroup (Equiv.Perm (ZMod p)),
      IsSolvable H ∧
      MulAction.IsPreprimitive H (ZMod p) ∧
      Nat.card H = p * (p - 1) := by
  refine ⟨(AGL1Z.toPerm p).range, ?_, ?_, ?_⟩
  · -- Solvability of the range: surjective from solvable source.
    exact solvable_of_surjective (MonoidHom.rangeRestrict_surjective _)
  · -- Preprimitivity transfer along rangeRestrict.
    have : Function.Bijective (id : ZMod p → ZMod p) := Function.bijective_id
    -- ... (Mathlib API choice below; this is the load-bearing step)
    sorry
  · -- Cardinality from the rangeRestrict equiv-of-equivalence.
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_congr (MonoidHom.equivRangeOfInjective _
        (AGL1Z.toPerm_injective p)).toEquiv.symm]
    exact AGL1Z.card_eq p
```

Size: ~25-35 LOC. The `sorry` on the second goal is the **load-bearing
primitivity transfer** — see § 3.

## 2. Recommendation

Ship **both layers**. Lite first (3-conjunct, 6 LOC, no risk), then
Full (subgroup form, ~30 LOC, one tactical decision). The Lite layer
gives the slug a closed forward-direction theorem; the Full layer
gives the mathematically faithful subgroup statement and is the form
the parent `Proofs/AbelRuffiniGaloisExtensions.lean` can import for
the classical "primitive solvable subgroups of S_p" framing.

If the Full layer's primitivity transfer hits friction, ship Lite
alone in the S5 PR and split Full into S6.

## 3. The load-bearing step: primitivity transfer

The S4 ACT (post-#18448) establishes
`MulAction.IsPreprimitive (AGL1Z p) (ZMod p)`. The packaging needs
`MulAction.IsPreprimitive ((AGL1Z.toPerm p).range) (ZMod p)`.

Three Mathlib API options (verified at master `2df2f015...`):

### 3.1 Option A — `IsPreprimitive.of_surjective`

`Mathlib/GroupTheory/GroupAction/Primitive.lean:204`:

```lean
theorem IsPreprimitive.of_surjective [IsPreprimitive M α] (hf : Function.Surjective f) :
    IsPreprimitive N β
```

where `f : α →ₑ[φ] β` is an equivariant map and `φ : M → N`.

For our case: `M := AGL1Z p`, `α := ZMod p`, `N := (AGL1Z.toPerm p).range`,
`β := ZMod p`, `φ := (AGL1Z.toPerm p).rangeRestrict`, `f := EquivariantMap.id`.

The construction of `f : ZMod p →ₑ[rangeRestrict] ZMod p` requires
verifying that for `g ∈ AGL1Z p` and `x ∈ ZMod p`:

```
(rangeRestrict g) • x = g • x   -- equivariance condition
```

which holds by definition of the subgroup action on `Equiv.Perm`.

### 3.2 Option B — `isPreprimitive_congr`

`Primitive.lean:213`:

```lean
theorem isPreprimitive_congr (hφ : Function.Surjective φ) (hf : Function.Bijective f) :
    IsPreprimitive M α ↔ IsPreprimitive N β
```

Same setup as Option A, but uses `Bijective` on `f` (which is just
`id`) and gives both directions. Slightly stronger but identical
proof obligations.

### 3.3 Option C — direct via orbit transfer

If `IsPreprimitive` unfolds to `IsPretransitive ∧ ∀ block, isTrivialBlock`,
we can directly:

- `IsPretransitive ((toPerm).range) (ZMod p)`: from `IsPretransitive (AGL1Z p) (ZMod p)`
  via `(toPerm.rangeRestrict).range_eq_top_of_surjective` plus orbit-of-image arguments.
- Block transfer: blocks of `range` acting on `ZMod p` are the same
  as blocks of `AGL1Z` acting on `ZMod p` (since the actions match).

This is more direct but more LOC; ~20 LOC instead of ~10.

**Recommendation**: try Option A first. The equivariance condition
is a one-liner (`rfl` or `simp [AGL1Z.toPerm_apply]`); the
surjectivity of `rangeRestrict` is by definition.

## 4. Mathlib citations (verified live, master `2df2f015...`)

In `Mathlib/GroupTheory/Solvable.lean`:

| Line | Symbol                                  | Use                                  |
|------|-----------------------------------------|--------------------------------------|
| 127  | `theorem solvable_of_ker_le_range`      | base lemma (transitive closure)      |
| 140  | `theorem solvable_of_solvable_injective` | source-side injectivity              |
| 144  | `instance subgroup_solvable_of_solvable` | alternative subgroup route           |
| 147  | `theorem solvable_of_surjective`         | **load-bearing for range solvability** |

In `Mathlib/GroupTheory/GroupAction/Primitive.lean`:

| Line | Symbol                                  | Use                                  |
|------|-----------------------------------------|--------------------------------------|
| 91   | `class IsPreprimitive`                   | the predicate to inherit             |
| 204  | `theorem IsPreprimitive.of_surjective`   | **Option A primitivity transfer**    |
| 213  | `theorem isPreprimitive_congr`           | Option B primitivity transfer        |

In `Mathlib/Algebra/Group/Hom/Defs.lean` (or successor file):

| Symbol                                      | Use                                  |
|---------------------------------------------|--------------------------------------|
| `MonoidHom.rangeRestrict`                   | surjective hom onto the range        |
| `MonoidHom.rangeRestrict_surjective`        | surjectivity proof                   |
| `MonoidHom.equivRangeOfInjective`           | `G ≃* range f` when `f` is injective |

In `Mathlib/SetTheory/Cardinal/Finite.lean`:

| Symbol                                      | Use                                  |
|---------------------------------------------|--------------------------------------|
| `Nat.card_eq_fintype_card`                  | cardinality bridge                   |

## 5. Symbols this PREP depends on (provided by upstream PRs)

The S5 ACT can only be shipped after these symbols are on `main`:

| Symbol                                              | Source PR     | Status (2026-05-13 ~02:00 UTC) |
|-----------------------------------------------------|---------------|---------------------------------|
| `AGL1Z (p : ℕ) [Fact p.Prime] : Type`               | #18205 merged | ✓                               |
| `theorem AGL1Z.card_eq`                             | #18205 merged | ✓                               |
| `instance : IsSolvable (AGL1Z p)` (or `theorem`)    | #18399        | build pending                   |
| `def AGL1Z.toPerm (p : ℕ) [Fact p.Prime] : AGL1Z p →* Equiv.Perm (ZMod p)` | #18399 | build pending |
| `theorem AGL1Z.toPerm_injective`                    | #18399        | build pending                   |
| `instance : MulAction.IsPreprimitive (AGL1Z p) (ZMod p)` | post-#18448 | not started                |

If #18399 lands but #18448 stays in PREP for >1 day, the S5 ACT
author can still ship **Lite layer only** by stubbing the
`IsPreprimitive` line with a future-imports comment.

## 6. Tactical risks

| Risk                                                      | Severity | Mitigation                                  |
|-----------------------------------------------------------|----------|---------------------------------------------|
| `inferInstance` for `IsPreprimitive` fails if S4 ACT registers as `theorem` not `instance` | Med | Coordinate with S4 ACT author; or use explicit theorem name |
| `MonoidHom.equivRangeOfInjective` name churn               | Low      | Fallback: `MulEquiv.ofInjective`            |
| Equivariant-map `→ₑ[φ]` definitional unfolding             | Med      | If `rfl` fails, use `MulActionHom.mk' ⟨id, fun g x ↦ rfl⟩` explicitly |
| `Nat.card` vs `Fintype.card` mismatch                      | Low      | Use `Nat.card_eq_fintype_card` bridge       |
| `(toPerm).range` action: which `MulAction` instance fires? | Med      | Mathlib has `Subgroup.mulAction` for `Subgroup (Equiv.Perm α)` acting on `α` via `(·).1.toFun`; verify at integration |
| `Fact p.Prime` propagation through `Nat.card`              | Low      | Should be automatic; if not, `haveI := Fact.out` |
| Universe polymorphism on `ZMod p` action                   | Low      | Pin to `Type` universe (concrete `ZMod`)    |

## 7. Acceptance criteria (binary)

The S5 ACT PR must:

- [ ] Add `theorem AGL1Z_isSolvableFaithfulPreprimitive` (Lite layer)
      OR `theorem AGL1Z_forward_witness` (Full layer) to
      `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean`.
- [ ] Use 0 `sorry`, 0 `axiom`.
- [ ] If Lite only: ≤ 10 LOC body. If Full: ≤ 60 LOC body.
- [ ] Build successfully via
      `./proofs/scripts/docker-build.sh Proofs.AbelRuffiniGaloisExtensionsOQ06`.
- [ ] Cite the 3 load-bearing Mathlib lemmas
      (`solvable_of_surjective`, `IsPreprimitive.of_surjective`,
      `Nat.card_eq_fintype_card`).
- [ ] Update `state.md` "Sessions" list to add the S5 entry.
- [ ] Update `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
      `nextSteps` and `insights` (slug `progress` → `surveyed` if
      both layers ship; `progress` if only Lite).

The ACT PR **must NOT**:

- Touch `problem.md`, `knowledge.md`, or any `sessions/` doc other
  than its own new entry (orthogonality to this PREP and to the
  two open PRs #18399 / #18448).
- Add an `axiom` declaration. The forward direction is fully
  constructive on top of S3 + S4.
- Attempt the **Galois direction** (every primitive solvable
  subgroup of S_p embeds into AGL). That is research-level and
  flagged in `state.md` as needing a sub-OQ split decision at S5.
- Add new top-level Mathlib imports (everything needed is already
  transitively imported via S3's existing imports).

## 8. Race awareness / orthogonality

At PREP push time (≥ 2026-05-13 02:10 UTC, ~10 min after the draft
opened), the situation on `abel-ruffini-galois-extensions-oq-06`:

| PR     | State                | File overlap with this PREP                          | Conclusion              |
|--------|----------------------|------------------------------------------------------|-------------------------|
| #18399 | Open, build pending  | none (different sessions/ note, different theorem)   | Orthogonal              |
| #18448 | Merged 02:06 UTC     | none (different sessions/ note, different theorem)   | Orthogonal (merged)     |

This PREP creates exactly one new file:
`research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s05-prep-forward-packaging.md`.

PR #18399 adds `2026-05-12-s03-isSolvable-and-faithful-roadmap.md`
(merged via #18307) and modifies the Lean file. PR #18448 added
`2026-05-13-s04-prep-isprimitive-via-prime-card.md` (now on main).

No `gh pr list --search` rows for "packaging" or "S5" or "forward
direction" on this slug at PREP draft time.

## 9. The Galois direction is explicitly out of scope

Per `state.md` § "Blockers" (lines 189–200):

> The Galois direction (S5+) will require:
> - Either a substantial new infrastructure block in Lean (primitive
>   permutation group structure theorem, ~300-500 lines), OR
> - Splitting OQ-06 into `abel-ruffini-galois-extensions-oq-06` (forward
>   direction, this slug) and a new sub-OQ
>   `abel-ruffini-galois-extensions-oq-06-galois-direction`.
> Decision deferred to S5 once the forward direction is in place.

The packaging theorem this PREP designs is the **forward-direction
conclusion**, not the Galois direction. The sub-OQ split decision
remains deferred and is the right scope for a later S6/S7 PREP
(after the packaging lands and the forward direction is closed).

Concretely, the packaging theorem states `∃ H ≤ S_p` with certain
properties; the Galois direction would invert this to `∀ H ≤ S_p
primitive-solvable → H ≅ AGL(1, p)`. That is the open question
shape; it is NOT discharged by either layer of this PREP.

## 10. References

- Galois, É. (1832). *Manuscript on solvable equations of prime
  degree* (posthumous).
- Robinson, D. J. S. (1996). *A Course in the Theory of Groups,*
  2nd ed., Springer. § 7.3 — primitive permutation groups of prime
  degree are affine.
- Cameron, P. J. (1999). *Permutation Groups,* CUP. § 3.5 —
  Burnside / Galois classification of primitive solvable degree-p.
- Mathlib. `Mathlib/GroupTheory/Solvable.lean` —
  `solvable_of_surjective` (line 147).
- Mathlib. `Mathlib/GroupTheory/GroupAction/Primitive.lean` —
  `IsPreprimitive.of_surjective` (line 204).
- Slug parent. `proofs/Proofs/AbelRuffiniGaloisExtensions.lean` —
  open question OQ-06.

## 11. Files this PREP adds / does not edit

**Adds** (exactly one file):

- `research/problems/abel-ruffini-galois-extensions-oq-06/sessions/2026-05-13-s05-prep-forward-packaging.md`
  (this file).

**Does not edit**:

- `proofs/Proofs/AbelRuffiniGaloisExtensionsOQ06.lean` (in flight via
  #18399).
- `proofs/Proofs/AbelRuffiniGaloisExtensions.lean` (parent;
  packaging may eventually import this).
- `proofs/Proofs.lean`.
- `research/problems/abel-ruffini-galois-extensions-oq-06/problem.md`.
- `research/problems/abel-ruffini-galois-extensions-oq-06/knowledge.md`.
- `research/problems/abel-ruffini-galois-extensions-oq-06/state.md`
  (the S5 ACT author updates "Sessions" and "Next Action" at that
  point).
- `src/data/research/problems/abel-ruffini-galois-extensions-oq-06.json`
  (the S5 ACT author updates `insights` / `nextSteps` at that point).
- `src/data/proofs/abel-ruffini-galois-extensions/meta.json` (no
  parent drift).

**Build status**: doc-only; no `lake build` invocation needed.
