# S5 PREP — `freeModel S` uniqueness via `HasIndependentProfiles` (S2-γ closure)

**Date**: 2026-05-13
**Researcher**: researcher-9
**Mode**: PREP (doc-only design memo)
**Phase target**: S5 ACT (Lean realisation), ~40-60 LOC append to
`TractatusOntologySpectrum.lean` or sibling `TractatusOntologyUniqueness.lean`
**Status**: pristine orthogonal to open S4 PREP (PR #18470, lattice via
image profiles) and merged S3 PREP (PR #18417, `HornModel` constructor).

## Why this PREP

The S2-α `state.md` (PR #18391, merged 2026-05-13T02:10:19Z) lists in its
"Not yet addressed (open question structure preserved)" section:

> Uniqueness of `freeModel` up to refinement-isomorphism among
> `IndependentWorlds`-style inhabitants (S3+ candidate). Requires bridge
> between the `IndependentWorlds S` typeclass (a property of
> `World S = S → Prop`) and the `WorldModel S` structure. Estimated
> scope: more substantial; possibly benefits from a dedicated
> `IsRefinementIso` predicate.

This is the **S2-γ** candidate from the original S1 OBSERVE
(`knowledge.md §6`):

> **S2-γ (Hard)** Prove the *uniqueness of `freeModel`* characterization:
> any inhabited `WorldModel S` satisfying `IndependentWorlds`-style
> independence at all states of affairs is uniquely determined up to a
> refinement-isomorphism with `freeModel S`.

This memo scopes the precise Lean statement, identifies the right
intermediate predicate (`HasIndependentProfiles`), gives the proof
sketch (it splits cleanly into a *section-retraction pair*, with a
genuine bijection only under the additional `IsTight` hypothesis),
records the bridge to `IndependentWorlds S`, and lays out the S5 ACT
implementation order.

## 1. The right intermediate predicate

`IndependentWorlds S` is a typeclass on the **type** `S` whose
witness is at the level of `World S = S → Prop`:

```lean
class IndependentWorlds (S : Type) where
  realizable : ∀ assignment : S → Prop,
    ∃ w : World S, ∀ s, w s ↔ assignment s
```

This does **not** directly apply to a general `WorldModel S`, whose
worlds live in an opaque type `M.W`. The natural lift to a
`WorldModel`-side predicate is:

```lean
/-- A world model has "independent profiles" when every Boolean
    assignment on `S` is realised by some world. This is the
    `WorldModel`-side analogue of `IndependentWorlds S`. -/
def HasIndependentProfiles (M : WorldModel S) : Prop :=
  ∀ assignment : S → Prop, ∃ w : M.W, ∀ s, M.holds w s ↔ assignment s
```

This predicate is **the bridge**: it says the same thing as
`IndependentWorlds` but quantifies through `M.holds` and `M.W` rather
than through `World S` and function application. The bridge theorem
(§3) shows:

- `freeModel S` satisfies `HasIndependentProfiles` trivially.
- Any subtype-style Tier-1 model `{w : S → Prop // φ w}` (the shape of
  every concrete constrained model in the parent file, including
  `ConstrainedWorld` and `weatherModel`) satisfies
  `HasIndependentProfiles` **iff** `φ` is universally true (and is
  therefore *not* genuinely constrained).

## 2. The uniqueness theorem (S5 ACT target)

The S5 ACT target is the following pair of theorems, conjointly the
"`freeModel` uniqueness" result:

```lean
/-- Half 1.  Every world model refines into `freeModel`.  (Already in
    `TractatusOntologySpectrum.lean` as `refines_freeModel`.) -/
theorem refines_freeModel (M : WorldModel S) :
    Refines M (freeModel S) := …  -- exists in main

/-- Half 2.  Any `HasIndependentProfiles` model is refined into by
    `freeModel`, the converse direction. -/
theorem freeModel_refines_independent
    (M : WorldModel S) (hM : HasIndependentProfiles M) :
    Refines (freeModel S) M := by
  classical
  refine ⟨fun a => (hM a).choose, ?_⟩
  intro a s
  have hspec := (hM a).choose_spec
  simpa [freeModel] using (hspec s).symm
```

Combining both halves gives `Refines M (freeModel S) ∧ Refines (freeModel S) M`,
i.e., **mutual refinement** between `M` and `freeModel S`. Formally:

```lean
/-- The refinement-isomorphism relation: mutual refinement. -/
def RefinesIso (M M' : WorldModel S) : Prop :=
  Refines M M' ∧ Refines M' M

/-- **Uniqueness of `freeModel S` (up to refinement-iso).**  Among
    inhabited `WorldModel S` instances with the independence property,
    `freeModel S` is unique up to mutual refinement. -/
theorem freeModel_unique_refines_iso
    (M : WorldModel S) (hM : HasIndependentProfiles M) :
    RefinesIso M (freeModel S) :=
  ⟨refines_freeModel M, freeModel_refines_independent M hM⟩
```

**Estimated LOC**: 3 defs (`HasIndependentProfiles`, `RefinesIso`,
optional `IsTight`) + 2 theorems (`freeModel_refines_independent`,
`freeModel_unique_refines_iso`) ≈ **40-50 LOC**.

## 3. Bridge theorems (`HasIndependentProfiles` ⇆ `IndependentWorlds`)

### 3a. `freeModel S` always has independent profiles

The default `IndependentWorlds S` instance proves this for free:

```lean
theorem freeModel_hasIndependentProfiles :
    HasIndependentProfiles (freeModel S) := by
  intro a
  exact ⟨a, fun _ => Iff.rfl⟩
```

This statement uses **no** `IndependentWorlds S` hypothesis because
`freeModel S` realises every `a` *as itself* — no typeclass plumbing
needed. The default Mathlib-free instance
(`TractatusOntology.lean:143-144`) is morally the same lemma.

### 3b. Subtype Tier-1 collapse to T0 under independence

This is the **content** of "constraint = independence-failure":

```lean
/-- A subtype-style Tier-1 model satisfies `HasIndependentProfiles`
    iff its constraint predicate is universally true. -/
theorem subtype_model_independent_iff
    (φ : (S → Prop) → Prop) (hne : Nonempty {w : S → Prop // φ w}) :
    HasIndependentProfiles
        ⟨{w : S → Prop // φ w}, fun w s => w.val s, hne⟩
    ↔ ∀ a : S → Prop, φ a := by
  refine ⟨fun h a => ?_, fun h a => ⟨⟨a, h a⟩, fun _ => Iff.rfl⟩⟩
  obtain ⟨⟨w, hw⟩, hmatch⟩ := h a
  have hwa : w = a := funext (fun s => propext (hmatch s))
  exact hwa ▸ hw
```

**Estimated LOC**: ~8.

**Significance.** The lemma says: in the `WorldModel`-spectrum, the
only point in *Tier 1* (predicate-constrained subtype) that satisfies
the independence property is the one whose predicate is **vacuous** —
i.e., it collapses to `freeModel S`. This is the **internal precision**
of TLP 2.061: independence is not a logical theorem; it is a
constraint pinning down `freeModel S` (up to refinement-iso) within
Tier 1.

### 3c. The contrapositive — `weatherModel` fails

```lean
theorem weatherModel_not_hasIndependentProfiles :
    ¬ HasIndependentProfiles weatherModel := by
  intro h
  -- Construct the "rain without clouds" assignment.
  let bad : WeatherFacts → Prop := fun s => s = .rain
  obtain ⟨⟨w, hw⟩, hmatch⟩ := h bad
  have hr : w .rain := (hmatch .rain).mpr rfl
  have hc : w .clouds := hw hr
  have : (.clouds : WeatherFacts) = .rain := (hmatch .clouds).mp hc
  cases this
```

**Estimated LOC**: ~8.

This is structurally `weather_independence_fails` (parent file),
restated in spectrum-level vocabulary. The transcription is mostly
mechanical — same witness assignment, same chain of implications.

## 4. The tightness refinement (optional S6 follow-up)

The `RefinesIso` relation in §2 gives a **section-retraction** pair
of `holds`-preserving maps, but not a genuine bijection: `M.W` may
have multiple worlds with the same Boolean profile (the "spectrum
allows distinguishing intensions that share an extension" case).

For a **genuine `Equiv`**, we need the additional hypothesis:

```lean
/-- A world model is *tight* if no two worlds share a Boolean profile. -/
def IsTight (M : WorldModel S) : Prop :=
  ∀ (w₁ w₂ : M.W),
    (∀ s : S, M.holds w₁ s ↔ M.holds w₂ s) → w₁ = w₂
```

Then we expect (S6 candidate, not S5):

```lean
/-- **Strict uniqueness of `freeModel S`** (up to `Equiv`).  Any
    independent + tight model is `Equiv`-isomorphic to `freeModel S`
    via the Boolean-profile map. -/
noncomputable def IsTight.equiv_freeModel
    (M : WorldModel S)
    (hI : HasIndependentProfiles M) (hT : IsTight M) :
    M.W ≃ (freeModel S).W where
  toFun w := fun s => M.holds w s
  invFun a := (hI a).choose
  left_inv := fun w => by
    have hspec := (hI (fun s => M.holds w s)).choose_spec
    exact hT _ _ (fun s => (hspec s).symm)
  right_inv := fun a => by
    funext s
    exact propext (hI a).choose_spec s
```

**S6 LOC estimate**: ~12 more lines on top of S5.

**Why not include S6 in S5 ACT?** Three reasons:

1. **Stratification.** `RefinesIso` is the *natural* spectrum-level
   equivalence: it is the equivalence induced by the `Refines` preorder
   (mutual refinement). `Equiv` is a *stricter* equivalence that
   demands the choice of representatives. S5 stays at the spectrum
   level; S6 adds the strict-bijection layer.
2. **`noncomputable` cost.** The `Equiv` in §4 requires
   `Classical.choose`. The `Refines`-style maps in §3 can be left as
   `def` without the `noncomputable` modifier when `Classical.choose`
   is invoked locally inside the proof body.
3. **Anti-pyramid principle.** S5 ACT closes the explicit S2-γ /
   state.md deferred item. S6 is a refinement of S5's result and
   would naturally come *after* S5 ACT lands.

## 5. Counter-example trace — what the uniqueness theorem rules out

The uniqueness theorem `freeModel_unique_refines_iso` says:
`HasIndependentProfiles M → RefinesIso M (freeModel S)`.

**Counter-example to the unhypothesised converse**: `weatherModel`
is *not* refinement-iso to `freeModel WeatherFacts`. By the contrapositive
of §3c:

- `weatherModel` does not satisfy `HasIndependentProfiles`.
- Yet by `refines_freeModel`, `Refines weatherModel (freeModel WeatherFacts)`
  holds.
- The reverse direction `Refines (freeModel WeatherFacts) weatherModel`
  fails: the assignment `bad := fun s => s = .rain` is a world of
  `freeModel WeatherFacts` (it is literally a function
  `WeatherFacts → Prop`), but there is no `weatherModel`-world with
  the same Boolean profile. So no `f : (S → Prop) → weatherModel.W`
  can satisfy `(freeModel WeatherFacts).holds a s ↔ weatherModel.holds (f a) s`
  for `a = bad` and `s = .clouds`.

A clean statement of this fact:

```lean
theorem freeModel_not_refines_weatherModel :
    ¬ Refines (freeModel WeatherFacts) weatherModel := by
  intro ⟨f, hf⟩
  let bad : WeatherFacts → Prop := fun s => s = .rain
  have hr : (f bad).val .rain := (hf bad .rain).mp rfl
  have hc : (f bad).val .clouds := (f bad).property hr
  have : (WeatherFacts.clouds : WeatherFacts) = .rain := (hf bad .clouds).mpr hc
  cases this
```

This complements `weather_independence_fails`: not only does
`weatherModel` *internally* fail independence, but **`freeModel`
cannot embed into it** (in the Refines-preorder direction that would
need the embedding to exist). So `weatherModel` is **strictly below**
`freeModel WeatherFacts` in the Refines preorder.

**Estimated LOC**: ~10.

## 6. Comparison with in-flight S4 PREP (PR #18470)

PR #18470 (S4 PREP, doc-only, open at PREP-push time) introduces:

```lean
def ImageProfiles (M : WorldModel S) : Set (S → Prop) :=
  { w | ∃ v : M.W, ∀ s, w s ↔ M.holds v s }
```

and shows `Refines M M' ↔ ImageProfiles M ⊆ ImageProfiles M'` (R-Lattice-1),
deriving the lattice structure on `(WorldModel S, Refines)`.

Connection to **this** S5 PREP:

| Aspect | S4 PREP (#18470) | S5 PREP (this memo) |
|---|---|---|
| Spectrum direction | lattice meet/join | uniqueness of the top |
| Key abstraction | `ImageProfiles : WorldModel S → Set (S → Prop)` | `HasIndependentProfiles : WorldModel S → Prop` |
| New axioms | 0 | 0 |
| Connects to `IndependentWorlds` typeclass? | NO | YES (bridge theorem §3) |
| Touches `weatherModel`? | NO (abstract) | YES (counter-example §5) |
| Lean append target | `TractatusOntologySpectrum.lean` | `TractatusOntologySpectrum.lean` or new sibling |

**Cross-reference**: `HasIndependentProfiles M` is equivalent to
`ImageProfiles M = Set.univ` (by `Set.eq_univ_iff_forall`). So if PR
#18470 merges first, the §3a bridge theorem becomes a one-liner via
`ImageProfiles` (`HasIndependentProfiles M ↔ ImageProfiles M = Set.univ`),
and §3c becomes `ImageProfiles weatherModel ⊊ Set.univ`. This is a
**pleasant amplification** but not a dependency: S5 ACT can ship
without S4 PREP merging.

If S5 ACT ships *before* S4 PREP merges, the two PRs can be unified
via a small refactor that exposes `HasIndependentProfiles` as a
convenience reflecting `ImageProfiles _ = Set.univ`. Either ordering
is fine.

## 7. Comparison with merged S3 PREP (PR #18417)

PR #18417 introduces the `HornModel S cs` constructor (T1a-tier
representative). Connection to **this** S5 PREP:

- `HornModel S cs` is a **subtype** model (constraint `φ w = ∀ c ∈ cs, w c.1 → w c.2`).
- By the §3b subtype-collapse lemma, `HasIndependentProfiles (HornModel S cs) ↔ ∀ a, ∀ c ∈ cs, a c.1 → a c.2`.
- For non-vacuous `cs` (containing at least one pair `(a, b)` with `a ≠ b`),
  the right-hand side is false (witness: `a ↦ true, b ↦ false`).
- Therefore, `HornModel S cs` is **strictly below** `freeModel S` in
  the Refines preorder whenever `cs` is "genuinely constraining" (in
  the sense of `hpair_distinct` from §4 of PR #18417's design memo).

This gives a clean **uniformity statement**: T1a-tier Horn models
satisfy independence iff their Horn theory is vacuous, generalising
both the `weatherModel` fail and the abstract `constrained_independence_fails`.

**Optional S5 ACT bonus theorem** (~5 LOC if we land after PR #18417 merges):

```lean
theorem hornModel_independent_iff_vacuous
    {S : Type} (cs : List (S × S)) (hne : Nonempty (HornModel S cs)) :
    HasIndependentProfiles
        ⟨HornModel S cs, fun w s => w.val s, hne⟩
    ↔ ∀ a : S → Prop, ∀ c ∈ cs, a c.1 → a c.2 :=
  subtype_model_independent_iff _ hne
```

This is one-line `exact subtype_model_independent_iff _ hne`. We add
it conditionally only if the underlying `HornModel` infrastructure
from PR #18417 has been ACT'd by S5 ACT time.

## 8. Mathlib API audit (at pinned v4.26.0)

The S5 ACT proofs require **no new Mathlib imports** beyond what
`TractatusOntologySpectrum.lean` already pulls in (`Proofs.TractatusOntology`,
which transitively imports Mathlib basics). Specific items used:

| Decl | Path | Use |
|------|------|-----|
| `Exists.choose`, `Exists.choose_spec` | `Mathlib.Logic.ExistsUnique` (core) | §2 `freeModel_refines_independent` |
| `Classical.choice` (transitively) | core | enables `noncomputable def` in §4 |
| `funext` | core | §3b `w = a` from `∀ s, w s ↔ a s` (with `propext`) |
| `propext` | core | as above |
| `Iff.rfl` | core | §3a `freeModel` realiser |
| `cases this` / `(_ : a = b)` discharge | core tactic | §5 contradicts `clouds = rain` |
| `Set.eq_univ_iff_forall` | `Mathlib.Data.Set.Basic` | optional §6 bridge if `ImageProfiles` is in scope |

**Net conclusion**: zero new Mathlib dependencies. All ingredients
are core or already-in-scope. The S5 ACT compile should be
**< 1 minute** on a warm cache (this is comparable to the S2-α ACT
which also added a small file with no new imports).

## 9. Implementation order for S5 ACT

Target file: **append to** `proofs/Proofs/TractatusOntologySpectrum.lean`
(current ~120 LOC after S2-α ACT). Rationale: same `namespace Tractatus`,
same dependencies, naturally extends the spectrum infrastructure.
Alternative: new sibling `proofs/Proofs/TractatusOntologyUniqueness.lean`
if reviewers prefer the smaller-file aesthetic.

Sequence:

1. ☐ Add `HasIndependentProfiles : WorldModel S → Prop`. [3 LOC]
2. ☐ Add `RefinesIso : WorldModel S → WorldModel S → Prop`. [2 LOC]
3. ☐ Prove `freeModel_hasIndependentProfiles`. [3 LOC]
4. ☐ Prove `freeModel_refines_independent`. [7 LOC]
5. ☐ Prove `freeModel_unique_refines_iso`. [2 LOC, corollary of 1-4]
6. ☐ Prove `subtype_model_independent_iff`. [8 LOC]
7. ☐ Prove `weatherModel_not_hasIndependentProfiles`. [8 LOC]
8. ☐ Prove `freeModel_not_refines_weatherModel`. [10 LOC]
9. ☐ (Conditional, if PR #18417 has merged) `hornModel_independent_iff_vacuous`. [3 LOC]
10. ☐ Build: `./proofs/scripts/docker-build.sh Proofs.TractatusOntologySpectrum`.
    Expected ~30-60s on warm cache.
11. ☐ Update `state.md`: phase → S5 ACT complete; mark S2-γ closed in
    the "Not yet addressed" list.
12. ☐ Optionally update `proofs/Proofs.lean` (already includes
    `TractatusOntologySpectrum` after S2-α merge).

**Total estimated LOC**: ~45-55 (excluding step 9).
**Estimated sorries on first ACT submission**: 0.
**Estimated new axioms**: 0.

## 10. Why the proof goes through (sanity check)

The load-bearing step is `freeModel_refines_independent`. Its proof
witness is `fun a => (hM a).choose : (freeModel S).W → M.W` (a
"select a realiser for each Boolean profile"). The verification:

For every `a : (freeModel S).W = S → Prop` and every `s : S`:
- `(freeModel S).holds a s = a s` by `def freeModel`.
- `M.holds ((hM a).choose) s ↔ a s` by `(hM a).choose_spec s`.

Therefore `(freeModel S).holds a s ↔ M.holds ((hM a).choose) s` is
exactly the `Iff.symm` of the `choose_spec` line. The Lean `simpa`
tactic resolves this in one step.

**Why no Tightness needed**: We only need `Refines (freeModel S) M`,
i.e., the existence of *some* function. We do **not** need a bijection,
hence no requirement that distinct Boolean profiles map to distinct
`M`-worlds. Multiple choices of `(hM a).choose` (or the same `a`)
would still produce a valid witness — the proof is genuinely about
the *existence* of a section, not the *uniqueness* of one.

**Why the converse fails** without `HasIndependentProfiles`: see §5.

## 11. Honest framing — what S5 ACT does NOT achieve

The S5 ACT result is **uniqueness up to `RefinesIso`**, not
**uniqueness up to `Eq`**. Three caveats:

1. **`RefinesIso` is weaker than `Equiv`.** `M ≃refines (freeModel S)`
   does not imply `M.W ≃ (S → Prop)` as types. Multiple worlds of
   `M` may share a Boolean profile, in which case the section
   `fun a => (hM a).choose` is not a true inverse. For genuine
   `Equiv`, add `IsTight M` (§4, S6 candidate).
2. **`RefinesIso` is not a `Setoid`** without explicit closure under
   symmetry. The definition in §2 is `Refines M M' ∧ Refines M' M`,
   which is symmetric by definition; reflexivity follows from
   `refines_refl`; transitivity is `refines_trans` applied twice.
   So `RefinesIso` *is* an equivalence relation, but we do not need
   to register it as a `Setoid` to state and prove uniqueness.
3. **No claim of "categorical universal property".** A stronger
   statement would phrase the uniqueness in terms of a universal
   property in the category of `WorldModel`s with `Refines`-morphisms.
   This is a (much) larger lift — it requires reifying `Refines`
   into a `Hom`-typed structure with composition, and proving
   `freeModel S` is a terminal object. Deferred to a hypothetical
   S7+ if the team wants the category-theoretic packaging.

In short: **S5 ACT closes the S2-γ / state.md deferred item at the
spectrum level (`RefinesIso`)**, not at the bijection level (`Equiv`)
or the category level (universal property).

## 12. Anti-targets (out of scope for S5 ACT)

1. **`Equiv`-level uniqueness with `IsTight`.** Sketched in §4 as the
   natural S6 follow-up. The S5 ACT does *not* include `IsTight` or
   the `noncomputable Equiv`.
2. **Category-theoretic packaging.** No `Hom`-types, no `Cat`
   instances, no terminal-object statement (see §11.3).
3. **Editing `TractatusOntology.lean`.** Parent file (~800 LOC,
   `status: verified`) is immutable for this PR.
4. **Editing `IndependentWorlds`.** The typeclass stays as-is; we
   add a bridge predicate (`HasIndependentProfiles`), not a redefinition.
5. **Lattice-theoretic interaction with PR #18470's image profiles.**
   Cross-reference acknowledged in §6; the optional bridge lemma
   `HasIndependentProfiles M ↔ ImageProfiles M = Set.univ` is **not**
   shipped in S5 ACT (S4 PREP hasn't ACT'd yet).
6. **Multi-Horn-clause generalisations.** §7 records the conditional
   `hornModel_independent_iff_vacuous` lemma as a single-line
   corollary; full multi-hypothesis Horn coverage is deferred per PR
   #18417 anti-target list.
7. **`elementary_independence`-style statements transferred to
   general `WorldModel`s.** Currently
   `elementary_independence` in the parent file is stated for
   `World S` with the `IndependentWorlds` instance. A generalisation
   to `HasIndependentProfiles M` would read:
   `HasIndependentProfiles M → ∀ a, ∃ w, ∀ s, M.holds w s ↔ a s`
   — but this is *literally the definition*, so no new theorem is
   shipped under that name. The point is that **the typeclass-shaped
   API generalises trivially to the `WorldModel`-shaped API once
   the bridge predicate is in scope.**
8. **Decidability instances on `HasIndependentProfiles` for finite
   `S`.** A natural follow-up (mentioned in `knowledge.md §5 item 5`)
   is to register `Decidable (HasIndependentProfiles M)` when `M.W`
   is `Fintype` and `S` is `Fintype` and the model is "computational"
   (`Decidable (M.holds w s)`). Deferred to a later S-iteration.

## 13. Race awareness

At PREP-push time (2026-05-13, ~03:00 UTC):

- **Open PRs for this slug**: PR #18470 (S4 PREP, doc-only, lattice via
  image profiles). Distinct deliverable: lattice meet/join. No file
  overlap (S5 PREP creates a new file in `sessions/`).
- **Recent merged PRs**:
  - PR #18191 (S1 OBSERVE, four-tier spectrum).
  - PR #18391 (S2-α ACT, refinement preorder + freeModel max +
    tautology pullback).
  - PR #18417 (S3 PREP, HornModel constructor).
- **Latest `origin/main`**: `0c84ce40fd1` (general-quartic-oq-02 S4
  PREP, doc-only). Unrelated slug.
- **Conflict surface**: zero. Strictly additive single-file PR in
  `research/problems/tractatus-ontology-oq-06/sessions/`.

The S5 PREP file name
`2026-05-13-s5-prep-freemodel-uniqueness-via-independence.md` is
distinct from the existing two:

- `2026-05-12-s3-prep-horn-model-constructor.md` (merged via #18417).
- `2026-05-13-s4-prep-refines-lattice-via-image-profiles.md` (in
  flight via #18470).

## 14. No-edit guarantee

Confirmed via design: this PREP adds **exactly one new file**:

```
research/problems/tractatus-ontology-oq-06/sessions/
    2026-05-13-s5-prep-freemodel-uniqueness-via-independence.md
```

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
  - `proofs/Proofs/TractatusOntology.lean` (parent, verified, ~800 LOC)
  - `proofs/Proofs/TractatusOntologySpectrum.lean` (S2-α ACT, in main)
- ✗ No edits to any `.json` file
  - `src/data/research/problems/tractatus-ontology-oq-06.json`
- ✗ No edits to any other session memo
  - `sessions/2026-05-12-s3-prep-horn-model-constructor.md` (merged S3 PREP)

## 15. Hand-off checklist for S5 ACT

1. ☐ Confirm `origin/main` includes `TractatusOntologySpectrum.lean`
   (S2-α ACT, merged via PR #18391 on 2026-05-13T02:10:19Z).
2. ☐ Optionally check whether PR #18417 (S3 PREP HornModel) has been
   followed by an S3 ACT; if so, the conditional
   `hornModel_independent_iff_vacuous` corollary becomes a 1-line
   addition (step 9 of §9).
3. ☐ Optionally check whether PR #18470 (S4 PREP lattice) has merged;
   if so, optionally add the `HasIndependentProfiles M ↔ ImageProfiles M = Set.univ`
   bridge (~3 LOC).
4. ☐ Append items 1-8 of §9 to `TractatusOntologySpectrum.lean`
   (or create sibling `TractatusOntologyUniqueness.lean`, reviewer's
   choice).
5. ☐ `./proofs/scripts/docker-build.sh Proofs.TractatusOntologySpectrum`
   (or the new sibling target). Expect 30-60s on warm cache, 30-45 min
   on broken-symlink fresh clone (cf. researcher memory
   `feedback_researcher_lake_symlink_loop_and_wipe`).
6. ☐ Update `state.md`: phase → S5 ACT complete; mark S2-γ closed
   in the deferred list.
7. ☐ Branch:
   `research/tractatus-ontology-oq-06-s5-act-freemodel-uniqueness-<unix-ts>`.
8. ☐ PR title:
   `research(tractatus-ontology-oq-06): S5 ACT — freeModel uniqueness via HasIndependentProfiles`.

## 16. References

- Wittgenstein, L. (1922). *Tractatus Logico-Philosophicus.* Routledge
  & Kegan Paul.
  - TLP 2.061, 2.062 — states-of-affairs independence (the
    Tractarian commitment captured by `HasIndependentProfiles`).
  - TLP 5.5, 5.501 — truth-functional compositionality.
- This repo:
  - `proofs/Proofs/TractatusOntology.lean:138-144` — `IndependentWorlds`
    typeclass and its default `World S` instance.
  - `proofs/Proofs/TractatusOntology.lean:274-291` — `WorldModel S`
    structure and `freeModel`.
  - `proofs/Proofs/TractatusOntology.lean:437-441` —
    `elementary_independence` (typeclass-shaped statement, currently
    only applies to `World S`).
  - `proofs/Proofs/TractatusOntology.lean:560-649` — `ConstrainedWorld`,
    `weatherModel`, `constrained_independence_fails`,
    `weather_independence_fails`.
  - `proofs/Proofs/TractatusOntologySpectrum.lean:32-119` — S2-α ACT
    output (`Refines` preorder + `refines_freeModel` +
    `tautology_pullback` + `freeModel_tautology_is_universal`).
  - `research/problems/tractatus-ontology-oq-06/state.md:56-69` —
    explicit S2-γ deferred item.
  - `research/problems/tractatus-ontology-oq-06/knowledge.md:96-106` —
    S1 OBSERVE classification of S2-α / S2-β / S2-γ candidates.
  - `research/problems/tractatus-ontology-oq-06/sessions/`
    `2026-05-12-s3-prep-horn-model-constructor.md` — S3 PREP (R2).
- Standard model-theory references:
  - Chang, C. C. & Keisler, H. J. (1990). *Model Theory*, 3rd edn.
    North-Holland. §1.3 (elementary equivalence and embeddings).
  - Hodges, W. (1993). *A Shorter Model Theory*. Cambridge UP. §3.1
    (elementary embeddings as model morphisms).

## 17. Honesty statement

This document is **doc-only PREP**. It produces:

- 0 new Lean theorems shipped
- 0 sorry deltas in any current `.lean` file
- 0 axiom changes
- 0 changes to any other markdown file (`problem.md`, `state.md`,
  `knowledge.md`) or to the JSON pool entry
- 1 new design document (this file) in the existing `sessions/`
  subdirectory

The value is **pre-staging**: a future S5 ACT can ship the uniqueness
result in ~45-55 LOC, 0 sorries, 0 axioms, in well under an hour
(assuming a working Docker build). The S5 ACT closes the S2-γ /
state.md "Uniqueness of `freeModel`" deferred item.

The PREP iteration does **not** discharge any open goal. Status
remains `in-progress` for the slug.

---

**End of S5 PREP — no Lean changes, no gallery changes, no axiom
changes. Second entry in the `sessions/` subdirectory after S3 PREP
(S4 PREP filename `2026-05-13-s4-prep-refines-lattice-via-image-profiles.md`
exists in the open PR #18470 but is not yet on `main`).**
