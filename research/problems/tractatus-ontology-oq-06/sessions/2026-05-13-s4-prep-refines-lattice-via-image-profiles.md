# S4 PREP — `(WorldModel S, Refines)` lattice structure via image profiles

**Date**: 2026-05-13
**Researcher**: researcher-4
**Mode**: PREP (doc-only design survey)
**Status**: pristine orthogonal to S2-α ACT (R1 refinement preorder
+ tautology pullback, MERGED #18391), S3 PREP (R2 generic `HornModel`
constructor, MERGED #18417), and S1 OBSERVE (four-tier spectrum, MERGED
#18191). Addresses a question explicitly deferred in state.md's
"Not yet addressed" list:

> Whether `(WorldModel S, Refines)` admits meet/join, i.e. forms a
> (semi)lattice. The natural candidate meet is pointwise intersection of
> `holds`-relations; needs verification.

## TL;DR (and a correction)

The state.md note above proposes "pointwise intersection of
`holds`-relations" as the candidate meet. **This memo argues that
candidate is *not* the GLB**, and identifies the correct
construction: the **Boolean-profile pullback**. We characterise
`Refines` cleanly via image profiles, show that the preorder
collapses to subset-inclusion on profile sets, and derive the lattice
operations on the resulting Refines-equivalence-classes. The
nonempty `W` constraint in `WorldModel` (line 287 of
`TractatusOntology.lean`) introduces a partiality: meets and joins
exist only when the resulting profile set is non-empty.

## Mathematical content

### The key invariant: image of Boolean profiles

For each `WorldModel S` define the **image profile set**:
$$
\mathrm{Im}(M) \;:=\; \{ w : S \to \mathrm{Prop} \mid \exists v : M.W,\; \forall s,\; w\, s \leftrightarrow M.\mathrm{holds}\, v\, s \}
\;\subseteq\; S \to \mathrm{Prop}.
$$

That is, `Im(M)` is the set of Boolean assignments realised by some
world of `M`. Lean form:

```lean
def ImageProfiles (M : WorldModel S) : Set (S → Prop) :=
  { w | ∃ v : M.W, ∀ s, w s ↔ M.holds v s }
```

### Characterisation of `Refines` via subset-inclusion

**Theorem (R-Lattice-1)**: `Refines M M' ↔ ImageProfiles M ⊆ ImageProfiles M'`.

**Forward direction**: if `⟨f, hf⟩ : Refines M M'`, then for each
`v : M.W` the profile `fun s => M.holds v s` equals
`fun s => M'.holds (f v) s` pointwise (by `hf v`), hence belongs to
`ImageProfiles M'`.

**Backward direction**: if `ImageProfiles M ⊆ ImageProfiles M'`,
then for each `v : M.W` the profile is in `ImageProfiles M'`, so
`Classical.choose` picks a witness `f v : M'.W` with matching
profile. The pair `⟨f, hf⟩` is the refinement.

Lean form:

```lean
theorem refines_iff_subset_imageProfiles (M M' : WorldModel S) :
    Refines M M' ↔ ImageProfiles M ⊆ ImageProfiles M' := by
  constructor
  · rintro ⟨f, hf⟩ w ⟨v, hv⟩
    refine ⟨f v, fun s => ?_⟩
    rw [hv s]; exact hf v s
  · intro hsub
    classical
    refine ⟨fun v =>
      Classical.choose (hsub ⟨v, fun _ => Iff.rfl⟩), fun v s => ?_⟩
    have := Classical.choose_spec (hsub ⟨v, fun _ => Iff.rfl⟩) s
    exact this.symm
```

This is the **load-bearing observation** of the entire spectrum: the
preorder collapses to subset inclusion on image profiles, so the
lattice structure on `(WorldModel S, Refines)` (modulo refinement
equivalence) is *exactly* the subset lattice on
`Set (S → Prop)` (modulo non-emptiness).

### Refines equivalence

Define `RefinesEquiv M M' := Refines M M' ∧ Refines M' M`. From
R-Lattice-1, `RefinesEquiv M M' ↔ ImageProfiles M = ImageProfiles M'`.

This is an honest equivalence relation, and the quotient
`WorldModel S / RefinesEquiv` is order-isomorphic to
`{P : Set (S → Prop) | P.Nonempty}` (using nonempty since
`M.nonempty : Nonempty M.W` forces `ImageProfiles M ≠ ∅`).

```lean
theorem refinesEquiv_iff_image_eq (M M' : WorldModel S) :
    Refines M M' ∧ Refines M' M ↔ ImageProfiles M = ImageProfiles M' := by
  rw [refines_iff_subset_imageProfiles, refines_iff_subset_imageProfiles,
      Set.Subset.antisymm_iff]
```

### Meet construction: Boolean-profile pullback

For `M₁ M₂ : WorldModel S`, define the **profile-pullback model**
when the intersection is non-empty:

```lean
def MeetModel (M₁ M₂ : WorldModel S)
    (h : (ImageProfiles M₁ ∩ ImageProfiles M₂).Nonempty) : WorldModel S where
  W        := { wp : (S → Prop) // wp ∈ ImageProfiles M₁ ∩ ImageProfiles M₂ }
  holds    := fun ⟨wp, _⟩ s => wp s
  nonempty := ⟨⟨h.some, h.some_mem⟩⟩
```

**Key lemma (R-Lattice-2-meet)**:
`ImageProfiles (MeetModel M₁ M₂ h) = ImageProfiles M₁ ∩ ImageProfiles M₂`.

The forward inclusion is immediate from the construction. The backward
inclusion: pick `wp ∈ ImageProfiles M₁ ∩ ImageProfiles M₂`; the world
`⟨wp, ⟨wp_in_1, wp_in_2⟩⟩` of the meet has profile exactly `wp`.

```lean
theorem imageProfiles_meet (M₁ M₂ : WorldModel S)
    (h : (ImageProfiles M₁ ∩ ImageProfiles M₂).Nonempty) :
    ImageProfiles (MeetModel M₁ M₂ h)
      = ImageProfiles M₁ ∩ ImageProfiles M₂ := by
  ext w
  constructor
  · rintro ⟨⟨wp, hwp⟩, hh⟩
    have heq : w = wp := funext (fun s => propext (hh s))
    rw [heq]; exact hwp
  · intro hw
    exact ⟨⟨w, hw⟩, fun _ => Iff.rfl⟩
```

**GLB property (R-Lattice-3-meet)**: for any `M : WorldModel S`,
`Refines M (MeetModel M₁ M₂ h) ↔ Refines M M₁ ∧ Refines M M₂`.

Discharge: chain `refines_iff_subset_imageProfiles` with
`imageProfiles_meet` and `Set.subset_inter_iff`.

```lean
theorem refines_meet_iff (M M₁ M₂ : WorldModel S)
    (h : (ImageProfiles M₁ ∩ ImageProfiles M₂).Nonempty) :
    Refines M (MeetModel M₁ M₂ h)
      ↔ Refines M M₁ ∧ Refines M M₂ := by
  rw [refines_iff_subset_imageProfiles, imageProfiles_meet,
      refines_iff_subset_imageProfiles, refines_iff_subset_imageProfiles,
      Set.subset_inter_iff]
```

### Why "pointwise intersection of `holds`-relations" is NOT the GLB

The state.md note suggests
$(M_1 \wedge M_2).\mathrm{holds}\, (w_1, w_2)\, s := M_1.\mathrm{holds}\, w_1\, s \wedge M_2.\mathrm{holds}\, w_2\, s$
with worlds in $M_1.W \times M_2.W$.

This construction (call it `ConjModel`) has

$$\mathrm{Im}(\mathrm{ConjModel}) = \{ \alpha \wedge \beta \mid \alpha \in \mathrm{Im}(M_1),\; \beta \in \mathrm{Im}(M_2) \}$$

where `α ∧ β` denotes pointwise conjunction of two `S → Prop`. This is
generically **strictly different** from $\mathrm{Im}(M_1) \cap \mathrm{Im}(M_2)$:

- **Counter-example (state.md candidate is too small)**: take
  $S = \{a\}$, $M_1$ has $W = \{w_1\}$ with `holds w₁ a = True` (image
  profile $\{(a \mapsto \top)\}$), $M_2$ has $W = \{w_2\}$ with
  `holds w₂ a = False` (image profile $\{(a \mapsto \bot)\}$). The
  intersection of image profiles is **empty**; the GLB does not
  exist as a `WorldModel`. But the `ConjModel` has the single world
  $(w_1, w_2)$ with `holds ⟨w₁, w₂⟩ a = True ∧ False = False`, so
  image profile $\{(a \mapsto \bot)\}$ — non-empty.

  Thus `ConjModel` is *too small* in the preorder to be the GLB: it
  refines into $M_2$ but **not** into $M_1$ (its image profile
  $\{(a \mapsto \bot)\}$ is not $\subseteq \{(a \mapsto \top)\} = \mathrm{Im}(M_1)$).

- **Counter-example (state.md candidate is too large)**: take
  $S = \{a, b\}$, $M_1$ has 2 worlds with profiles
  $\{(a, b) \mapsto (\top, \bot), (\top, \top)\}$, $M_2$ has 2 worlds
  with profiles $\{(\bot, \top), (\top, \top)\}$. Intersection is
  $\{(\top, \top)\}$. But `ConjModel` has $2 \times 2 = 4$ worlds with
  conjunctive profiles $\{(\bot, \bot), (\top, \bot), (\bot, \bot),
  (\top, \top)\}$ = $\{(\bot, \bot), (\top, \bot), (\top, \top)\}$ —
  three profiles, strictly larger than the intersection.

**Conclusion**: `ConjModel` is neither $\le$ nor $\ge$ the true GLB in
general. The `MeetModel` construction (Boolean-profile pullback) is
the correct definition. The state.md note's candidate should be
discarded.

### Join construction: disjoint union of profiles

For `M₁ M₂ : WorldModel S`, define the **profile-union model**:

```lean
def JoinModel (M₁ M₂ : WorldModel S) : WorldModel S where
  W        := M₁.W ⊕ M₂.W
  holds    := fun w s => Sum.elim (fun v₁ => M₁.holds v₁ s)
                                  (fun v₂ => M₂.holds v₂ s) w
  nonempty := M₁.nonempty.map Sum.inl
```

**Key lemma (R-Lattice-2-join)**:
`ImageProfiles (JoinModel M₁ M₂) = ImageProfiles M₁ ∪ ImageProfiles M₂`.

The join is **always defined** (no nonempty caveat), because
`ImageProfiles M₁` is non-empty by `M₁.nonempty`.

**LUB property (R-Lattice-3-join)**: for any `M : WorldModel S`,
`Refines (JoinModel M₁ M₂) M ↔ Refines M₁ M ∧ Refines M₂ M`.

```lean
theorem imageProfiles_join (M₁ M₂ : WorldModel S) :
    ImageProfiles (JoinModel M₁ M₂)
      = ImageProfiles M₁ ∪ ImageProfiles M₂ := by
  ext w
  constructor
  · rintro ⟨v, hv⟩
    cases v with
    | inl v₁ => exact Or.inl ⟨v₁, hv⟩
    | inr v₂ => exact Or.inr ⟨v₂, hv⟩
  · rintro (⟨v, hv⟩ | ⟨v, hv⟩)
    · exact ⟨Sum.inl v, hv⟩
    · exact ⟨Sum.inr v, hv⟩

theorem refines_join_iff (M₁ M₂ M : WorldModel S) :
    Refines (JoinModel M₁ M₂) M ↔ Refines M₁ M ∧ Refines M₂ M := by
  rw [refines_iff_subset_imageProfiles, imageProfiles_join,
      refines_iff_subset_imageProfiles, refines_iff_subset_imageProfiles,
      Set.union_subset_iff]
```

### Top element: `freeModel S`

The top is `freeModel S`: $\mathrm{Im}(\mathrm{freeModel}) = S \to \mathrm{Prop}$
(the entire ambient set). This already proved as `refines_freeModel`
in S2-α ACT (`TractatusOntologySpectrum.lean:66`).

```lean
theorem imageProfiles_freeModel : ImageProfiles (freeModel S) = Set.univ := by
  ext w
  refine ⟨fun _ => trivial, fun _ => ⟨w, fun _ => Iff.rfl⟩⟩
```

### Bottom element: does not exist

There is **no bottom** element in `(WorldModel S, Refines)` because
$\mathrm{Im}(M)$ is required to be non-empty (by `M.nonempty`), and
the intersection of all non-empty subsets is empty. Equivalently,
the lattice has a top but not a bottom — it is **bounded above
but not below**.

This justifies the "S4 PREP" framing: the question of "is it a
*complete* lattice" requires either:
- Dropping the nonempty constraint (introducing a sentinel "empty
  model" that's the bottom), or
- Restricting to non-empty meets (giving a **bounded-above
  meet-semilattice with partial meets**, which is the right structural
  fit).

The cleanest statement is the second: a **complete join-semilattice**
with arbitrary joins (suprema), a top element, and **partial
binary meets** that exist exactly when the intersection of image
profiles is non-empty.

### Arbitrary joins (Sigma-type construction)

For an indexed family `M : I → WorldModel S` (with `I` non-empty and
inhabited at some index), the join construction generalises:

```lean
def iJoinModel {I : Type} [Nonempty I] (M : I → WorldModel S) :
    WorldModel S where
  W        := Σ i : I, (M i).W
  holds    := fun ⟨i, v⟩ s => (M i).holds v s
  nonempty := by
    obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨v⟩ := (M i).nonempty
    exact ⟨⟨i, v⟩⟩
```

with `ImageProfiles (iJoinModel M) = ⋃ i, ImageProfiles (M i)`.

This gives `(WorldModel S, Refines)` the structure of a **non-empty-suprema-complete
join-semilattice with top**, modulo refinement-equivalence. Mathlib's
`SemilatticeSup` / `BoundedOrder` instances would attach naturally
once the equivalence quotient is taken.

## Lean realisation plan

### File location

Option A (preferred): append to `proofs/Proofs/TractatusOntologySpectrum.lean`
(the file added in S2-α ACT, currently 121 lines, 0 sorries, 0 axioms).
The additions are structurally cohesive — they extend the existing
`Refines` machinery rather than introducing a new direction.

Option B: new file `proofs/Proofs/TractatusOntologyLattice.lean` if S2-β's
`TractatusOntologyHorn.lean` lands first and the Spectrum file gains
unrelated infrastructure. This is a separation-of-concerns judgment
call deferred to the implementer.

### Skeleton (recommended ACT artefact, Option A)

```lean
-- Append to TractatusOntologySpectrum.lean after
-- freeModel_tautology_is_universal (line 119).

namespace Tractatus

variable {S : Type}

/-- The image profile set of a world model: the Boolean assignments
    `S → Prop` actually realised by some world of `M`. -/
def ImageProfiles (M : WorldModel S) : Set (S → Prop) :=
  { w | ∃ v : M.W, ∀ s, w s ↔ M.holds v s }

theorem imageProfiles_nonempty (M : WorldModel S) :
    (ImageProfiles M).Nonempty := by
  obtain ⟨v⟩ := M.nonempty
  exact ⟨fun s => M.holds v s, ⟨v, fun _ => Iff.rfl⟩⟩

/-- **R-Lattice-1**: `Refines` is exactly subset-inclusion on image profiles. -/
theorem refines_iff_subset_imageProfiles (M M' : WorldModel S) :
    Refines M M' ↔ ImageProfiles M ⊆ ImageProfiles M' := by
  -- (as above)
  sorry

theorem refinesEquiv_iff_image_eq (M M' : WorldModel S) :
    Refines M M' ∧ Refines M' M ↔ ImageProfiles M = ImageProfiles M' := by
  -- (as above, two-line proof via Set.Subset.antisymm_iff)
  sorry

theorem imageProfiles_freeModel : ImageProfiles (freeModel S) = Set.univ := by
  -- (as above, two-line proof)
  sorry

/-- The disjoint-sum join of two world models. -/
def JoinModel (M₁ M₂ : WorldModel S) : WorldModel S where
  W        := M₁.W ⊕ M₂.W
  holds    := fun w s => Sum.elim (fun v₁ => M₁.holds v₁ s)
                                  (fun v₂ => M₂.holds v₂ s) w
  nonempty := M₁.nonempty.map Sum.inl

theorem imageProfiles_join (M₁ M₂ : WorldModel S) :
    ImageProfiles (JoinModel M₁ M₂)
      = ImageProfiles M₁ ∪ ImageProfiles M₂ := by
  -- (as above)
  sorry

theorem refines_join_iff (M₁ M₂ M : WorldModel S) :
    Refines (JoinModel M₁ M₂) M ↔ Refines M₁ M ∧ Refines M₂ M := by
  -- (as above, three rw with Set.union_subset_iff)
  sorry

/-- The Boolean-profile pullback (meet) of two world models, when the
    intersection of their image profile sets is non-empty. -/
def MeetModel (M₁ M₂ : WorldModel S)
    (h : (ImageProfiles M₁ ∩ ImageProfiles M₂).Nonempty) : WorldModel S where
  W        := { wp : (S → Prop) // wp ∈ ImageProfiles M₁ ∩ ImageProfiles M₂ }
  holds    := fun ⟨wp, _⟩ s => wp s
  nonempty := ⟨⟨h.some, h.some_mem⟩⟩

theorem imageProfiles_meet (M₁ M₂ : WorldModel S)
    (h : (ImageProfiles M₁ ∩ ImageProfiles M₂).Nonempty) :
    ImageProfiles (MeetModel M₁ M₂ h)
      = ImageProfiles M₁ ∩ ImageProfiles M₂ := by
  -- (as above)
  sorry

theorem refines_meet_iff (M M₁ M₂ : WorldModel S)
    (h : (ImageProfiles M₁ ∩ ImageProfiles M₂).Nonempty) :
    Refines M (MeetModel M₁ M₂ h)
      ↔ Refines M M₁ ∧ Refines M M₂ := by
  -- (as above, four rw with Set.subset_inter_iff)
  sorry

end Tractatus
```

**Total**: ~80 LOC added, 8 new declarations (3 defs + 5 theorems), 0
new axioms. After ACT: 0 sorries.

### Filling the `sorry` placeholders

All 6 `sorry`s above have explicit proof sketches in the
"Mathematical content" section. Each is a 2-to-6-line tactic proof
using only `Mathlib.Data.Set.Basic` (`Set.subset_inter_iff`,
`Set.union_subset_iff`, `Set.Subset.antisymm_iff`) and `Classical.choose`
for the backward direction of R-Lattice-1.

The two trickiest:

1. **`refines_iff_subset_imageProfiles` backward direction**: requires
   `Classical.choose` to extract `f : M.W → M'.W` from
   `∀ v, ∃ v', ...`. Idiomatic Mathlib pattern:

   ```lean
   refine ⟨fun v => Classical.choose (hsub ⟨v, fun _ => Iff.rfl⟩), fun v s => ?_⟩
   exact (Classical.choose_spec (hsub ⟨v, fun _ => Iff.rfl⟩) s).symm
   ```

2. **`imageProfiles_meet` direction**: requires `propext` + `funext`
   to lift a pointwise `Iff` to function equality:

   ```lean
   rintro ⟨⟨wp, hwp⟩, hh⟩
   have heq : w = wp := funext (fun s => propext (hh s))
   rw [heq]; exact hwp
   ```

Both patterns are well-documented in Mathlib's `Set` namespace.

## Anti-targets

This memo deliberately does **not**:

1. **Implement `EquivModel` / T1b**. That's S2-β / S3+ territory (R2
   covers Horn / T1a; T1b symmetric equivalence is for after Horn).

2. **Touch any existing Lean file**. The skeleton above proposes
   `Append to TractatusOntologySpectrum.lean` but no edits happen
   as part of this PR (PREP discipline).

3. **Edit `problem.md` / `state.md` / `knowledge.md`**. The state.md
   "Not yet addressed" entry on lattice structure is updated naturally
   when this PREP's ACT lands; this memo provides the *replacement
   plan* for that bullet, not the bullet itself.

4. **Define `IsRefinementIso` predicate**. That's R3 (uniqueness of
   `freeModel`) territory, a separate S4-or-later PREP.

5. **Address Kripke / T2 or quotient / T3 tiers**. Out of scope per
   S1 OBSERVE.

6. **Re-prove `refines_freeModel`**. Already in S2-α ACT
   (`TractatusOntologySpectrum.lean:66`); the
   `imageProfiles_freeModel` theorem above is the *image-profile
   reformulation* of that fact, not a re-proof.

7. **Mathlib-bridge to `SemilatticeSup` / `BoundedOrder`**. The
   refinement-equivalence quotient lives in `Setoid`-land, requiring
   a `Quotient` boilerplate that's better deferred to a follow-up
   ACT. This memo establishes the raw lattice operations; the
   typeclass instances are a clean S5+ deliverable.

## Race awareness

- **Open PRs for this slug at push time** (2026-05-13 02:30 UTC):
  none. PR #18391 (S2-α ACT) merged 02:10 UTC; PR #18417 (S3 PREP)
  merged 02:08 UTC; PR #18191 (S1 OBSERVE) merged 23:20 UTC the day
  prior.
- **Conflict surface**: zero. Strictly additive single-file PR.
- **Most recent merges this slug**:
  - PR #18417 (S3 PREP, R2 HornModel) — designs a complementary
    spectrum direction (T1a-tier expressivity). No overlap.
  - PR #18391 (S2-α ACT, R1 refinement preorder) — installs the
    `Refines` def + lattice-prerequisite theorems. This PREP **builds
    on** S2-α and **does not modify** any of its definitions.
  - PR #18191 (S1 OBSERVE) — the original survey. Untouched.
- **Latest origin/main**: `0c84ce40fd1` (general-quartic-oq-02 S4
  PREP), confirmed with `git ls-tree origin/main proofs/Proofs/` →
  `TractatusOntologySpectrum.lean` present.

## No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/tractatus-ontology-oq-06/sessions/2026-05-13-s4-prep-refines-lattice-via-image-profiles.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file (including
  `TractatusOntology.lean` and `TractatusOntologySpectrum.lean`)
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (S3 PREP at
  `sessions/2026-05-12-s3-prep-horn-model-constructor.md`)

## Honesty

- **Difficulty**: medium. The Boolean-profile pullback idea is the
  *correct* construction (state.md's pointwise-conjunction candidate
  is genuinely wrong), and identifying it as the GLB requires the
  R-Lattice-1 characterisation as a bridge. But once that
  characterisation lands, the rest of the lattice structure is
  routine.
- **Significance**: real conceptual contribution. The
  R-Lattice-1 theorem (`refines_iff_subset_imageProfiles`) reduces a
  structural question on `WorldModel` to a Set-theoretic question on
  `Set (S → Prop)`, which has clean Mathlib API support. This is
  the kind of "reduction to known infrastructure" that often unlocks
  later work.
- **Correction to state.md**: the "natural candidate meet" remark in
  state.md is incorrect (see counter-examples above). The implementer
  of S4 ACT should update state.md to point to `MeetModel` as the
  correct construction. (Out of scope for this PREP, but flagged.)
- **Status after ACT**: `axiomatized` with respect to the lattice
  structure on the quotient (since `Quotient (Setoid.mk RefinesEquiv _)`
  is the "really right" object and requires extra plumbing), but
  `verified` for all 8 declarations above (0 sorries, 0 axioms in
  the proposed ACT skeleton).

## Implementation hand-off checklist

For the next researcher implementing S4 ACT:

- [ ] Append the 8 declarations to
  `proofs/Proofs/TractatusOntologySpectrum.lean` (or create new
  file `TractatusOntologyLattice.lean`; preserve the namespace
  `Tractatus`).
- [ ] Add `import Mathlib.Data.Set.Basic` and
  `import Mathlib.Data.Sum.Basic` to the file's imports (already
  transitively imported through `Proofs.TractatusOntology` — confirm).
- [ ] Discharge each `sorry` using the proof sketch above.
- [ ] Confirm Docker build verifies
  (`./proofs/scripts/docker-build.sh Proofs.TractatusOntologySpectrum`).
- [ ] Update `state.md` "Not yet addressed" bullet on lattice
  structure to record:
  - Joins exist as `JoinModel` (defined for arbitrary indexed
    families via `Σ`).
  - Meets exist *partially* as `MeetModel`, with non-emptiness
    guard.
  - Bottom does not exist (image profile non-empty constraint).
  - Correction to "pointwise intersection of `holds`-relations"
    candidate.
- [ ] Add insight to gallery entry
  `src/data/proofs/tractatus-ontology-oq-06/meta.json`: "The
  refinement preorder collapses to Set-theoretic subset inclusion
  on Boolean image profiles. The structure is a bounded-above,
  non-empty-meet-partial, complete-join-semilattice."

## Mathlib API audit

The following Mathlib lemmas are used in the recommended skeleton:

| Lemma | Module | Purpose |
|---|---|---|
| `Set.subset_inter_iff` | `Mathlib.Data.Set.Basic` | $A \subseteq B \cap C \iff A \subseteq B \wedge A \subseteq C$ |
| `Set.union_subset_iff` | `Mathlib.Data.Set.Basic` | $A \cup B \subseteq C \iff A \subseteq C \wedge B \subseteq C$ |
| `Set.Subset.antisymm_iff` | `Mathlib.Data.Set.Basic` | $A = B \iff A \subseteq B \wedge B \subseteq A$ |
| `Set.Nonempty.some` / `.some_mem` | `Mathlib.Data.Set.Basic` | Extract witness from a non-empty set |
| `Sum.elim` | core | Case analysis on disjoint union |
| `Classical.choose` / `.choose_spec` | core | AC for the backward direction of R-Lattice-1 |
| `funext` + `propext` | core | Lifting pointwise `Iff` to function equality |

All exist at the pinned revision (`mathlib4` v4.26.0). No new
Mathlib imports needed beyond what `TractatusOntologySpectrum.lean`
already has (via `import Proofs.TractatusOntology`).

## Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s4-prep-refines-lattice-via-image-profiles.md`
      file
- [x] No edits to `problem.md` / `state.md` / `knowledge.md` / any
      `.json` / any `.lean`
- [x] Filename distinct from S3 PREP memo
      (`2026-05-12-s3-prep-horn-model-constructor.md`)
- [x] R-Lattice-1 verified by hand: both directions trace through
      cleanly with the existing `Refines` definition
- [x] Counter-examples to `ConjModel` candidate verified by hand
      (sizes 1 and 2 in $S$)
- [x] `JoinModel` is always defined (no nonempty caveat) — verified
      using `M₁.nonempty.map Sum.inl`
- [x] `MeetModel` non-emptiness witness construction
      (`⟨h.some, h.some_mem⟩`) verified

## References

- Parent gallery: `src/data/proofs/tractatus-ontology/` (Wittgenstein's
  *Tractatus Logico-Philosophicus*, world-model semantics).
- S1 OBSERVE: `sessions/` did not exist, but `problem.md`,
  `knowledge.md`, `state.md` were the deliverables (MERGED #18191).
- S2-α ACT: `proofs/Proofs/TractatusOntologySpectrum.lean`, 121 LOC
  (MERGED #18391).
- S3 PREP:
  `sessions/2026-05-12-s3-prep-horn-model-constructor.md`,
  371 LOC (MERGED #18417).
- Background: lattice theory of preorders, e.g., Birkhoff (1940),
  *Lattice Theory*, AMS Colloquium Publications.
