# S5 PREP — `¬ HasSBP TopCat` first failure-witness instance

**Date**: 2026-05-13
**Researcher**: researcher-12
**Phase**: PREP (orientation for a *negative* `HasSBP` instance,
orthogonal to the two open positive-instance PRs).
**Type**: Doc-only design memo. No edits to Lean files, `state.md`,
`problem.md`, `knowledge.md`, the in-flight PR #18383 / PR #18428
`sessions/` notes, gallery `meta.json`, or research JSON.

## 0. Why this PREP

The slug has two open PRs on positive instances of `HasSBP`:

| PR    | Phase          | Target                                       |
|-------|----------------|----------------------------------------------|
| #18383 | S2/S3 ACT      | `HasSBP` def + `hasSBP_Type` (Mathlib bridge) |
| #18428 | S4 PREP        | `hasSBP_Discrete` (every-morphism-iso trick)  |

Both PRs show that **SBP holds**. Neither demonstrates that the
predicate is *non-trivial*: as written, every theorem on the slug
would discharge to `True`-up-to-coherence if `HasSBP` were a tautology.

`state.md` lines 50–56 anticipated this gap:

> The Bumby / Gowers counter-examples are documented but not Lean-formal;
> S3 counter-example witnesses may need to remain at the
> `axiomatized` level (cite paper, state `¬ HasSBP Grp` as axiom).

`knowledge.md` lists only **Grp** (Bumby torsion split) and **Ban**
(Gowers 1996) as failure witnesses — both well beyond Lean's reach
without committing to axiomatic-level statements.

**This PREP locks a third, fully-Lean-tractable failure witness:**
`¬ HasSBP TopCat`. The proof reduces to a 4-line tactic chain using
already-merged Mathlib API: compactness of `[0,1]`, non-compactness
of `(0,1)`, the standard bridge `TopCat.mono_iff_injective`, and
`Homeomorph.compactSpace`. No axiom, no `sorry`, no new Mathlib API
required.

Choosing TopCat over Grp/Ban is deliberate: TopCat's counter-example
[0,1]-vs-(0,1) is *elementary* (compactness vs. non-compactness; one
inequality), whereas Grp requires an embedding `ℤ ⊕ ℤ/2 → ℤ` whose
construction is non-trivial, and Gowers' Banach result is research-
level. TopCat is the **easiest** failure witness, not the deepest.

## 1. Goal of the eventual S5-Top ACT

Add a single theorem to `proofs/Proofs/SchroederBernsteinOQ01.lean`,
after `hasSBP_Discrete` (or alongside, depending on merge order):

```lean
/-- **(S5-Top)** The category of topological spaces lacks SBP:
    `[0,1]` and `(0,1)` admit mutual injective continuous maps but
    are not homeomorphic (compactness is preserved by homeomorphism;
    `[0,1]` is compact and `(0,1)` is not). -/
theorem not_hasSBP_TopCat : ¬ HasSBP TopCat := by
  intro h
  -- X := TopCat.of ↥(Set.Icc (0 : ℝ) 1) is compact
  -- Y := TopCat.of ↥(Set.Ioo (0 : ℝ) 1) is not compact
  -- mutual monos via TopCat.mono_iff_injective; iso via h would
  -- give a homeomorphism, but compactness transfer fails.
  sorry
```

Net delta target: **~25–35 LOC** including docstring + the two
helper-`def`s for the unit-interval / open-interval `TopCat` objects
and the two continuous-injection maps. 0 sorries, 0 axioms, no new
top-level imports beyond `Mathlib.Topology.Category.TopCat.EpiMono`
and `Mathlib.Topology.Order.Compact` (both already pulled
transitively by `Mathlib.CategoryTheory.Types`).

## 2. Mathematical witness — `[0,1]` vs `(0,1)`

### 2.1 The two objects

Let

```
X := TopCat.of ↥(Set.Icc (0 : ℝ) 1)   -- closed unit interval, compact
Y := TopCat.of ↥(Set.Ioo (0 : ℝ) 1)   -- open unit interval, not compact
```

`Set.Icc` and `Set.Ioo` carry the **subspace topology** from `ℝ`,
which is the canonical `TopologicalSpace` instance on the coerced
subtype `↥s := {x // x ∈ s}`. `TopCat.of` lifts this to the category.

### 2.2 The two mutual injective continuous maps

**Map `f : X → Y`** (compress into the middle quarter):

```
f ⟨x, hx⟩ := ⟨(x + 1) / 4, ?_⟩
```

The proof `?_` of membership in `Set.Ioo 0 1` follows from
`0 ≤ x ≤ 1`:

- `x = 0` ⇒ `(x + 1)/4 = 1/4 ∈ (0, 1)` ✓
- `x = 1` ⇒ `(x + 1)/4 = 1/2 ∈ (0, 1)` ✓
- General `x ∈ [0, 1]`: `(x + 1)/4 ∈ [1/4, 1/2] ⊂ (0, 1)` by
  `1/4 > 0` and `1/2 < 1` — pure `linarith` discharge.

Continuity of `f` follows from continuity of `(· + 1) / 4` on `ℝ`
and continuity of the subtype-codomain pairing
(`Continuous.subtype_mk`). Injectivity is immediate
(`(a + 1)/4 = (b + 1)/4 → a = b` via field arithmetic).

**Map `g : Y → X`** (subspace inclusion, after subset extension):

```
g ⟨y, hy⟩ := ⟨y, (Set.Ioo_subset_Icc_self) hy⟩
```

Continuity is the standard subtype-inclusion lemma; injectivity is
immediate from `Subtype.ext`.

### 2.3 The contradiction

From `h : HasSBP TopCat`, applying `h X Y ⟨f, mono_f⟩ ⟨g, mono_g⟩`
(with `mono_f` and `mono_g` extracted from
`(TopCat.mono_iff_injective _).mpr`) produces `⟨iso⟩ : Nonempty (X ≅ Y)`.

`TopCat.homeoOfIso iso : X ≃ₜ Y` is the corresponding homeomorphism.
`Homeomorph.compactSpace iso.symm` (or directly via `iso`) transfers
the `CompactSpace X` instance to `CompactSpace Y`.

But `CompactSpace Y ↔ IsCompact (Set.univ : Set ↥(Set.Ioo 0 1))`,
and via the subtype-Coercion lemma this transfers to
`IsCompact (Set.Ioo 0 1)` in `ℝ`. By `isCompact_Ioo_iff`, this would
force `1 ≤ 0`, contradicting `(0 : ℝ) < 1`.

## 3. Mathlib citations (verified live, master `2df2f015...`)

In `Mathlib/Topology/Category/TopCat/EpiMono.lean`:

| Line | Symbol                              | Use                                  |
|------|-------------------------------------|--------------------------------------|
| 38   | `theorem TopCat.mono_iff_injective` | bridge `Mono f ↔ Function.Injective f` |
| 28   | `theorem TopCat.epi_iff_surjective` | dual bridge (unused; orientation only) |

In `Mathlib/Topology/Category/TopCat/Basic.lean`:

| Line | Symbol                                  | Use                                  |
|------|-----------------------------------------|--------------------------------------|
| 198  | `def TopCat.isoOfHomeo`                 | iso ← homeomorph (orientation only)  |
| 204  | `def TopCat.homeoOfIso`                 | **iso → homeomorph (load-bearing)**  |
| 234  | `lemma TopCat.isIso_iff_isHomeomorph`   | alternative phrasing                 |

In `Mathlib/Topology/Order/Compact.lean`:

| Line | Symbol                  | Use                                              |
|------|-------------------------|--------------------------------------------------|
| 54   | `CompactIccSpace.isCompact_Icc` | `IsCompact (Set.Icc a b)` over ℝ         |
| 132  | `theorem isCompact_Ioo_iff` | **`IsCompact (Set.Ioo a b) ↔ b ≤ a` (load-bearing)** |

In `Mathlib/Topology/Homeomorph/Lemmas.lean`:

| Line | Symbol                              | Use                              |
|------|-------------------------------------|----------------------------------|
| 104  | `protected theorem Homeomorph.compactSpace` | `[CompactSpace X] → X ≃ₜ Y → CompactSpace Y` |

In `Mathlib/Topology/Compactness/Compact.lean`:

| Line | Symbol                          | Use                                   |
|------|---------------------------------|---------------------------------------|
| 1020 | `theorem isCompact_iff_compactSpace` | bridge `IsCompact s ↔ CompactSpace s` |

Subtype-coercion lemmas (`Continuous.subtype_mk`, `Subtype.ext`,
`Set.Ioo_subset_Icc_self`) are in
`Mathlib.Topology.Constructions` and `Mathlib.Data.Set.Intervals.Basic`
and need no specific line citation.

## 4. Proof body sketch (the S5 ACT author's path)

```lean
theorem not_hasSBP_TopCat : ¬ HasSBP TopCat := by
  intro h
  set X : TopCat.{0} := TopCat.of ↥(Set.Icc (0 : ℝ) 1)
  set Y : TopCat.{0} := TopCat.of ↥(Set.Ioo (0 : ℝ) 1)
  -- Mutual monos.
  have mono_f : ∃ m : X ⟶ Y, Mono m := by
    refine ⟨TopCat.ofHom ⟨fun ⟨x, hx⟩ => ⟨(x + 1) / 4, ?_⟩, ?_⟩, ?_⟩
    · rcases hx with ⟨h0, h1⟩; constructor <;> [linarith; linarith]
    · -- continuity of (·+1)/4 composed with subtype_mk
      fun_prop
    · rw [TopCat.mono_iff_injective]
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      ext
      linarith
  have mono_g : ∃ n : Y ⟶ X, Mono n := by
    refine ⟨TopCat.ofHom ⟨fun ⟨y, hy⟩ => ⟨y, Set.Ioo_subset_Icc_self hy⟩, ?_⟩, ?_⟩
    · fun_prop
    · rw [TopCat.mono_iff_injective]
      intro a b hab
      simp only [Subtype.mk.injEq] at hab
      exact Subtype.ext hab
  obtain ⟨iso⟩ := h X Y mono_f mono_g
  -- Iso to homeomorph, then transfer compactness.
  have hX : CompactSpace X := by
    rw [show (X : Type) = ↥(Set.Icc (0 : ℝ) 1) from rfl]
    exact isCompact_iff_compactSpace.mp isCompact_Icc
  have hY : CompactSpace Y := (TopCat.homeoOfIso iso).compactSpace
  -- (0,1) is non-compact: contradicts CompactSpace Y.
  have : IsCompact (Set.Ioo (0 : ℝ) 1) := by
    rw [← (Set.Ioo (0 : ℝ) 1).image_coe] -- or use the converse direction
    exact (isCompact_iff_compactSpace.mpr hY).image continuous_subtype_val
  rw [isCompact_Ioo_iff] at this
  linarith
```

This sketch is illustrative; the actual ACT author should refine
the subtype-coercion ritual (specifically the `(X : Type) = …` rewrite,
which may be `TopCat.coe_of`) against Mathlib at integration time.

## 5. Tactical risks

| Risk                                                      | Severity | Mitigation                                  |
|-----------------------------------------------------------|----------|---------------------------------------------|
| `TopCat.of` universe-polymorphism: `TopCat.{0}` vs `.{u}` | Med      | Pin to `TopCat.{0}` (concrete ℝ subtypes)   |
| `TopCat.ofHom` / `TopCat.Hom` API name (Mathlib has churned here) | Med | Verify against `Mathlib.Topology.Category.TopCat.Basic` at integration |
| `fun_prop` for `(·+1)/4 ∘ Subtype.val` continuity         | Low      | Fallback: explicit `Continuous.div_const.comp Continuous.subtype_val.add_const` |
| Subspace topology vs subtype topology: equal but Lean may not unfold | Med | Use `TopCat.coe_of` rewrite; if absent, fall back to `show` |
| Compactness transfer direction: `Homeomorph.compactSpace` consumes `[CompactSpace X]` instance, not hypothesis | Low | Use `haveI := hX` to register before applying |
| `iso.toEquiv` vs `(homeoOfIso iso).toEquiv`               | Low      | Mathlib provides both routes; pick whichever simp closes |
| Image of `Set.univ` under subtype.val: `Set.image_univ_coe_eq` | Med | Use `Set.image_univ` + range characterization; or `isCompact_iff_isCompact_univ` |

The most likely source of friction is the **subtype-coercion ritual**
in lines 5–6 of the sketch: making `(X : Type) = ↥(Set.Icc 0 1)` and
`(Y : Type) = ↥(Set.Ioo 0 1)` definitionally transparent so
`isCompact_iff_compactSpace` and `Homeomorph.compactSpace` chain.
The ACT author should expect one or two `show`/`change` rewrites
to bridge `TopCat.of α : TopCat` and the underlying `α : Type`.

## 6. Acceptance criteria (binary)

The S5-Top ACT PR must:

- [ ] Add `theorem not_hasSBP_TopCat : ¬ HasSBP TopCat` to
      `proofs/Proofs/SchroederBernsteinOQ01.lean` *after* the merges
      of #18383 (introducing `HasSBP`) and #18428 (or its successor).
- [ ] Use 0 `sorry`, 0 `axiom`, ≤ 35 LOC body (excluding docstring),
      ≤ 2 new imports (`Mathlib.Topology.Category.TopCat.EpiMono`,
      `Mathlib.Topology.Order.Compact`).
- [ ] Build successfully via
      `./proofs/scripts/docker-build.sh Proofs.SchroederBernsteinOQ01`.
- [ ] Cite the 4 load-bearing Mathlib lemmas (`mono_iff_injective`,
      `homeoOfIso`, `isCompact_Icc`, `isCompact_Ioo_iff`).
- [ ] Update `state.md` "Sessions" list to add the S5 entry.
- [ ] Update `src/data/research/problems/schroeder-bernstein-oq-01.json`
      `insights` to record TopCat as the first Lean-formal failure
      witness.

The ACT PR **must NOT**:

- Touch `problem.md`, `knowledge.md`, or any `sessions/` doc other
  than its own new entry (orthogonality to this PREP and to the
  two open positive-instance PRs).
- Add an `axiom` declaration (the proof is fully constructive over
  Mathlib's classical foundations).
- Generalize beyond `TopCat` (e.g. to `CompHausLike` or
  `MetricSpaceCat`) before the concrete `TopCat` witness is in.

## 7. Race awareness / orthogonality

At PREP push time (≥ 2026-05-13 01:54 UTC, ~6 min after this draft
opened), open PRs on `schroeder-bernstein-oq-01`:

| PR     | File overlap with this PREP | Conclusion              |
|--------|------------------------------|-------------------------|
| #18383 | none (different sessions/ note, different theorem) | Orthogonal |
| #18428 | none (different sessions/ note, different theorem) | Orthogonal |

This PREP creates exactly one new file:
`research/problems/schroeder-bernstein-oq-01/sessions/2026-05-13-s05-prep-top-counterexample.md`.

Both #18383 and #18428 add their own `sessions/2026-05-12-*.md` files
and neither edits `problem.md` / `knowledge.md`. The eventual S5 ACT
PR will be sequenced *after* #18383's `HasSBP` definition merges; if
#18383 is in flight at S5 ACT time, the ACT author should rebase to
include #18383's branch as a dependency.

No `gh pr list --search` rows for "TopCat" or "S5" or "counterexample"
on this slug at PREP draft time.

## 8. Honest scope

This PREP **does not**:

- Prove the open characterization of SBP (Pradic-Brown 2019, Trnková
  1975). The B-B sufficient condition is also out of scope here.
- Generalize to other failure witnesses (Grp, Ban). Grp specifically
  requires an `ℤ ⊕ ℤ/2 ↪ ℤ` embedding whose Lean construction is
  open research; Ban requires Gowers (1996), beyond Lean's reach.
- Add infrastructure for "categories of topological spaces with
  extra structure". The `TopCat` failure already suffices to show
  `HasSBP` is non-trivial.

This PREP **does**:

- Pin a concrete, ~25-35 LOC Lean theorem that is *the easiest*
  failure-witness in the slug's mathematical roadmap (per
  `knowledge.md`).
- Verify all four load-bearing Mathlib lemmas at master
  `2df2f015...` with exact file/line citations.
- Anticipate the most likely tactical risks and provide fallbacks.
- Keep the slug's positive-vs-negative balance: after #18383 +
  #18428 + this S5-Top ACT, the gallery will exhibit two positive
  instances (Type u, Discrete α) and one negative instance (TopCat),
  making `HasSBP` a *content-bearing* predicate, not a vacuous one.

## 9. References

- Banaschewski, B. & Brümmer, G. C. L. (1986). *Thoughts on the
  Cantor-Bernstein theorem.* Quaestiones Mathematicae 9, 1–27.
- Reid Barton (Mathlib). `Mathlib/Topology/Category/TopCat/EpiMono.lean`
  — `mono_iff_injective` (line 38).
- Mathlib. `Mathlib/Topology/Category/TopCat/Basic.lean` —
  `homeoOfIso` (line 204), `isIso_iff_isHomeomorph` (line 234).
- Mathlib. `Mathlib/Topology/Order/Compact.lean` —
  `isCompact_Ioo_iff` (line 132), exported `isCompact_Icc` (line 56).
- Mathlib. `Mathlib/Topology/Homeomorph/Lemmas.lean` —
  `Homeomorph.compactSpace` (line 104).

## 10. Files this PREP adds / does not edit

**Adds** (exactly one file):

- `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-13-s05-prep-top-counterexample.md`
  (this file).

**Does not edit**:

- `proofs/Proofs/SchroederBernsteinOQ01.lean` (not yet on main; lands
  with PR #18383).
- `proofs/Proofs.lean`.
- `research/problems/schroeder-bernstein-oq-01/problem.md`.
- `research/problems/schroeder-bernstein-oq-01/knowledge.md`.
- `research/problems/schroeder-bernstein-oq-01/state.md` (the S5
  ACT author updates "Sessions" and "Next Action" at that point).
- `src/data/research/problems/schroeder-bernstein-oq-01.json` (the
  S5 ACT author updates `insights` / `nextSteps` at that point).
- `src/data/proofs/schroeder-bernstein/meta.json` (no parent drift).

**Build status**: doc-only; no `lake build` invocation needed.
