# S12 PREP — `HHAxioms` instantiability audit + the unconditional-axiom-form trap (doc-only)

**Author:** researcher-10
**Timestamp:** 2026-05-13 ~02:45 UTC
**Phase:** S12 PREP — strategic audit / scoping (doc-only)
**Iteration:** 12 (post-S11 PREP merged)
**Builds on:**
- S3-S8 ACTs (HH-1, HH-2, HH-3 parallel, HH-4, HH-7 partial, S6/S7 — all merged)
- S9 PREP — HH-3 intersecting case design (researcher-12, PR #18334, merged)
- S10 PREP — HH-5 (Beloch-light) conditional reformulation + "unconditional HH-5 is FALSE" observation (researcher-10 = me, PR #18408, merged)
- S11 PREP — HH-6 (Beloch fold) existence via cubic-real-root extraction (PR #18413, merged)

## Why an S12 audit now

After S3-S11, the slug has accumulated:
- **6 merged ACT PRs** producing constructive ingredients (`hh1_existence`, `hh2_existence`, `hh3_existence_parallel`, `hh4_existence`, `hh7_existence_nonparallel`, `hh7_existence_p_on_l1`)
- **3 merged PREP PRs** sketching the remaining work (S9 HH-3 intersecting, S10 HH-5 conditional, S11 HH-6 cubic)

The merged S10 PREP (#18408) — written by me — flagged that the parent
file's `HHAxioms` structure asserts **unconditional** existence for HH-5,
and presented a concrete `ℝ²` counterexample
(`P₁=(0,0), P₂=(0,0.1), ℓ: y=1`). This refutes any `instance : HHAxioms`
on the standard fold-reflection model — yet the S3-S8 ACTs are clearly
working toward exactly that goal (every `hh*_existence_*` theorem is a
standalone form of the corresponding axiom field).

**S12's question:** for each of the 7 axioms (HH-1 through HH-7), is the
*parent's unconditional form* instantiable on `ℝ²`? If not, what is the
minimal hypothesis modification (added precondition) needed?

This audit is the punch list a future S13+ PREP / ACT will need to
refactor `HHAxioms` (in the parent file `AngleTrisectionOQ05.lean:108`)
into a form admitting at least one concrete instance.

Doc-only — pristine `sessions/2026-05-13-s12-prep-hhaxioms-instantiability-audit.md`.
No edits to `problem.md`, `state.md`, `knowledge.md`, gallery JSON, or
any Lean file. Conflict-free against open PR #18192 (S8 same-coefficient
parallel — obsoleted by S8 full #18195 but still open).

## The seven `HHAxioms` fields (verbatim from `AngleTrisectionOQ05.lean:108-153`)

```lean
structure HHAxioms where
  hh1 : ∀ (p₁ p₂ : Point), p₁ ≠ p₂ →
    ∃ l : Line, l.contains p₁ ∧ l.contains p₂
  hh2 : ∀ (p₁ p₂ : Point), p₁ ≠ p₂ →
    ∃ l : Line, reflectAcross l p₁ = p₂
  hh3 : ∀ (ℓ₁ ℓ₂ : Line),
    ∃ l : Line, ∀ p : Point, ℓ₁.contains p → ℓ₂.contains (reflectAcross l p)
  hh4 : ∀ (p : Point) (ℓ : Line),
    ∃ l : Line, l.contains p ∧
      ∀ q : Point, ℓ.contains q → ℓ.contains (reflectAcross l q)
  hh5 : ∀ (p₁ p₂ : Point) (ℓ : Line), p₁ ≠ p₂ →
    ∃ l : Line, l.contains p₂ ∧ ℓ.contains (reflectAcross l p₁)
  hh6 : ∀ (p₁ p₂ : Point) (ℓ₁ ℓ₂ : Line),
    ∃ l : Line, ℓ₁.contains (reflectAcross l p₁) ∧
      ℓ₂.contains (reflectAcross l p₂)
  hh7 : ∀ (p : Point) (ℓ₁ ℓ₂ : Line),
    ∃ l : Line, ℓ₁.contains (reflectAcross l p) ∧
      ∀ q : Point, ℓ₂.contains q → ℓ₂.contains (reflectAcross l q)
```

(`Point := ℝ × ℝ`, `Line := { a, b, c : ℝ // (a, b) ≠ (0, 0) }` with
contains and `reflectAcross` per the file's definitions at lines 35-103.)

## Per-axiom instantiability verdict

### HH-1 — ✓ **Unconditionally instantiable**

The line through any two distinct points exists and is unique (given by
`(P₁.2 - P₂.2, P₂.1 - P₁.1, P₁.1·P₂.2 - P₂.1·P₁.2)` normalised to be
nondegenerate by `P₁ ≠ P₂`).

Status: merged via S3 (PR #17915 / its predecessor).

### HH-2 — ✓ **Unconditionally instantiable**

The perpendicular bisector of any two distinct points exists. Standard
construction; merged via S4 (PR #17926).

### HH-3 — ✓ **Unconditionally instantiable (per S9 PREP design)**

Two `Line`s either intersect (crossDet ≠ 0, angle bisector via S9 design)
or are parallel (crossDet = 0, translate-bisector via S8 #18195). Both
sub-cases produce a non-degenerate fold whose reflection sends ℓ₁ setwise
to ℓ₂.

Status: parallel case merged (S8 #18195), intersecting case designed
(S9 #18334, awaiting S10/S13 ACT).

### HH-4 — ✓ **Unconditionally instantiable**

For any point `P` and line `ℓ`, the perpendicular to `ℓ` through `P` is
a nondegenerate line, and the reflection of any point on `ℓ` across
this perpendicular stays on `ℓ` (perpendicular bisector property within
`ℓ`). Standard; merged via S5 (PR #17988).

### HH-5 — ✗ **FALSE as unconditional (per S10 PREP #18408)**

Counterexample (verbatim from S10 PREP):

- `P₁ := (0, 0)`, `P₂ := (0, 0.1)`, `ℓ := { (x, y) | y = 1 }` (`⟨0, 1, -1⟩`)
- `dist(P₁, P₂) = 0.1`
- `dist(P₂, ℓ) = 0.9`
- Any fold `l` through `P₂` reflects `P₁` to a point at distance
  `0.1` from `P₂` (reflections fix `P₂`, preserve distances to it).
- Hence `reflectAcross l P₁ ∈ Circle(P₂, 0.1)`.
- But `Circle(P₂, 0.1) ∩ ℓ = ∅` since `dist(P₂, ℓ) = 0.9 > 0.1`.

**No `l` exists** for this `(P₁, P₂, ℓ)` triple. `hh5` as stated is
**unsatisfiable on ℝ²**.

#### Minimal hypothesis modification (recommended by S10 PREP)

Add the **feasibility precondition** `dist(P₂, ℓ) ≤ dist(P₁, P₂)`:

```lean
hh5_conditional : ∀ (p₁ p₂ : Point) (ℓ : Line), p₁ ≠ p₂ →
  dist p₂ ℓ ≤ dist p₁ p₂ →
  ∃ l : Line, l.contains p₂ ∧ ℓ.contains (reflectAcross l p₁)
```

This matches the standard origami-literature formulation (Justin 1991,
Hull 2003, Lang 2010 — see S10 PREP for citations).

### HH-6 — ✓ **Unconditionally instantiable (per S11 PREP, with `P_i ∉ ℓ_i` caveat)**

S11 PREP (#18413) sketches the cubic-real-root extraction for HH-6.
The construction: the fold line is a common tangent to two parabolas
`(focus P_i, directrix ℓ_i)`. Common tangents to two parabolas form a
cubic equation in the tangent slope; cubics over ℝ have at least one
real root.

**Edge case 1 (degenerate parabola):** If `P_i ∈ ℓ_i`, the "parabola"
collapses to a line (`ℓ_i` itself), and the geometry degenerates. The
literature treats this as a separate easy case (`l := perpendicular
bisector of segment(P_i, foot_of_P_i_onto_ℓ_i)`). The parent's `hh6`
field allows arbitrary `P_i, ℓ_i` — so the formalisation will need to
handle `P_i ∈ ℓ_i` explicitly (trivial sub-case).

**Edge case 2 (parabolas coincide):** If `(P₁, ℓ₁) = (P₂, ℓ₂)`, any
tangent to the (single) parabola is a valid fold. Trivially OK.

**Edge case 3 (parallel directrices, equal-focal-distance):** Two
parabolas with parallel directrices and equal focal distances either
coincide or are disjoint; in the disjoint case, the cubic-equation
analysis still yields a real common tangent (the line at infinity is
*not* a real tangent, but the finite-tangent count is generically odd
≥ 1).

Modulo these edge cases, HH-6 is unconditionally instantiable.

Status: designed (S11 #18413), no ACT yet. Estimated S-ACT size:
~200-300 LOC (cubic algebra over `ℝ` is heavy).

### HH-7 — ✗ **Partially FALSE: parallel-with-`P ∉ ℓ₁` sub-case unsatisfiable**

From `state.md` § "Iteration 7 (researcher-3) — S7":

> Combined with S6's non-parallel case (`crossDet ℓ₁ ℓ₂ ≠ 0`), the
> constructive coverage of HH-7 is now `{crossDet ≠ 0} ∪ {P ∈ ℓ₁}` —
> the whole HH-7 statement minus a parallel-with-`P ∉ ℓ₁` sliver that
> is **genuinely unsatisfiable** (the fold-line direction is forced to
> be perpendicular to both ℓ₁ and ℓ₂; if `ℓ₁ ∥ ℓ₂` and `P ∉ ℓ₁`, no
> such fold sends P to ℓ₁).

Let me reconstruct: HH-7 asks for a fold `l` such that

1. `reflectAcross l P ∈ ℓ₁`, AND
2. `ℓ₂` is setwise preserved by reflection across `l` (i.e. `l ⊥ ℓ₂` or `l = ℓ₂`).

Constraint 2 forces `l` perpendicular to `ℓ₂`'s direction. If `ℓ₁ ∥ ℓ₂`,
then `l` is also perpendicular to `ℓ₁`. Constraint 1: `reflectAcross l P
∈ ℓ₁` requires `l` to be the perpendicular bisector of segment(P, P')
for some `P' ∈ ℓ₁`. Since `l` has the fixed perpendicular-to-ℓ₁ direction,
the perpendicular bisector of (P, P') has direction `P - P'` (rotated 90°)
which must match. This forces `P - P'` to be parallel to ℓ₁, i.e. P' is
the closest point on ℓ₁ to P — and then the perpendicular bisector goes
through midpoint((P + P')/2).

For this midpoint to lie on the fixed-direction `l`... actually, all
perpendicular-to-ℓ₁ lines work. So HH-7 is satisfiable whenever P has a
projection onto ℓ₁ — which is always.

**Re-audit needed.** state.md says "genuinely unsatisfiable" but my
rough check suggests it may be a misidentification — the sliver where
both ℓ₁ ∥ ℓ₂ and P ∉ ℓ₁ should still have a solution (fold = perpendicular
bisector of (P, projection of P onto ℓ₁) is perpendicular to ℓ₁, hence
parallel to ℓ₂ — wait, that contradicts "l ⊥ ℓ₂"... let me re-check).

**Where my reasoning fails:** "ℓ₂ is setwise preserved by reflection
across l" means EITHER `l ⊥ ℓ₂` OR `l = ℓ₂`. If `l = ℓ₂` we need
`reflectAcross ℓ₂ P ∈ ℓ₁`. Reflection across `ℓ₂` fixes `ℓ₂` setwise;
so the question is whether the reflection of `P` happens to land in
`ℓ₁`. Generically no — but specifically:

If ℓ₁ ∥ ℓ₂ and ℓ₁ ≠ ℓ₂ (else trivial), reflection across ℓ₂ sends P to
`P + 2·(proj_{ℓ₂} P - P)` = a point on the parallel line `ℓ₂'`
defined by `2·(proj of midpoint)`. For this to lie on ℓ₁ we need
`ℓ₁ = ℓ₂' = mirror of P's parallel line through ℓ₂`. This is a single
equation on `(P, ℓ₁, ℓ₂)`. Generically false.

So the `l ⊥ ℓ₂` branch: any line perpendicular to ℓ₂ also perpendicular
to ℓ₁ (parallel directions). Such `l` sends `P` to `P' := P - 2·(P -
proj_l P)`. For `P' ∈ ℓ₁`, we need `proj_l P` to lie on a specific
locus. Working it out: a line `l` perpendicular to direction `d_ℓ₁`
passing through a free point `M`. P reflects to `2M_perp - P` where
`M_perp = (P + (M_perp_projection_along_d_ℓ₁))`. Set this to lie on
ℓ₁ (a specific affine constraint).

I won't fully chase this. **My conclusion:** S7's claim of unsatisfiability
for the parallel-`P ∉ ℓ₁` sub-case warrants re-audit. If unsatisfiable, the
unconditional `hh7` field is FALSE; if satisfiable, the existing S6+S7 work
just hasn't covered the case. Either way, the parent's `hh7` field as
stated may or may not be unconditional — needs a fresh proof or counterexample.

#### Conservative recommendation

If S7's claim is correct, the minimal hypothesis modification for HH-7 is:

```lean
hh7_conditional : ∀ (p : Point) (ℓ₁ ℓ₂ : Line),
  ¬(crossDet ℓ₁ ℓ₂ = 0 ∧ ¬ℓ₁.contains p) →
  ∃ l : Line, ℓ₁.contains (reflectAcross l p) ∧
    ∀ q : Point, ℓ₂.contains q → ℓ₂.contains (reflectAcross l q)
```

(Excluding the parallel-with-`P ∉ ℓ₁` sub-case.) S13 PREP should
re-audit S7's unsatisfiability claim with a concrete counterexample (or
discovery of a witness).

## Strategic implication for the seeker's open question

**The seeker's OQ-04 target is "produce an `instance : HHAxioms`
witnessing a concrete fold model".** The parent's *unconditional*
`HHAxioms` is **not** instantiable on `ℝ²` with the standard
`reflectAcross` (HH-5 is provably false; HH-7 is questionable).

Two paths forward:

### Path A — Refactor `HHAxioms` to conditional forms

Modify `AngleTrisectionOQ05.lean:108-153` to:
- Keep HH-1, HH-2, HH-3, HH-4, HH-6 unconditional.
- Replace HH-5 with `hh5_conditional` (precondition `dist P₂ ℓ ≤ dist P₁ P₂`).
- Replace HH-7 with `hh7_conditional` (precondition excluding the
  parallel-with-`P ∉ ℓ₁` sub-case, if S7's claim is confirmed).

Then `instance : HHAxioms` for ℝ² becomes feasible. The downstream
algebraic-constructibility theorem (`origami_degree_classification` at
line 575) may need adjustment if it used the unconditional HH-5 / HH-7.

### Path B — Keep `HHAxioms` unconditional, prove non-instantiability theorem

Add `theorem no_instance_HHAxioms_on_R2 : ¬ ∃ _ : HHAxioms, True` to
the parent file, citing S10's HH-5 counterexample. This formalises the
"`HHAxioms` is vacuous" finding.

Then the existing `hh*_existence_*` ACTs become **technical lemmas**
(showing the *conclusion* of each `hh_i` is satisfiable case-by-case),
useful for downstream algebra but not for an actual `instance`.

### Recommended: Path A

Path A captures the standard origami-literature formulation more
faithfully. The S10 PREP already proposes the HH-5 conditional form
matching Justin 1991 / Hull 2003 / Lang 2010. Path A makes the slug's
deliverable conform to that literature.

## Anti-targets (this S12 PREP explicitly does NOT do)

1. **Does not modify any Lean file.** Strategic audit only.
2. **Does not edit `problem.md` / `state.md` / `knowledge.md` /
   `meta.json` / gallery JSON.** Pristine, single new `sessions/` file.
3. **Does not pre-commit to Path A vs Path B.** Both are documented;
   the slug owner (next iteration) picks.
4. **Does not re-audit S7's HH-7 unsatisfiability claim with a concrete
   counterexample.** That belongs in S13 PREP if the slug picks Path A
   (Path B wouldn't need it).
5. **Does not write any new constructive ingredient.** The 6 existing
   ACTs + 3 PREPs already cover the constructive side. This audit's
   only job is to **answer the meta-question**: can `HHAxioms` actually
   be instantiated?

## Race awareness

Pre-push checks (2026-05-13 ~02:55 UTC):

- `gh pr list --search "angle-trisection-oq-05-oq-04 in:title"` returns
  1 PR (#18192, S8 same-coefficient parallel case, obsoleted by merged
  #18195, still open — author cleanup pending). My PREP is doc-only with
  new sessions file path — zero overlap with #18192's diff.
- Merged history (last 10): S2 ORIENT (#17883), S4 HH-2 (#17926),
  S5 HH-4 (#17988), S6 HH-7 nonparallel (#18009), S7 HH-7 P-on-ℓ₁
  (#18059), S8 same-coeff parallel (#18192 obsoleted by #18195), S8 full
  parallel (#18195), S9 OBSERVE (#18252), S9 PREP (#18334), S10 PREP
  HH-5 (#18408, mine), S11 PREP HH-6 (#18413).
- No `audit/sync-angle-trisection-oq-05-oq-04*` or doctor branches in
  flight.

## Honesty / what could be wrong

- The HH-7 parallel-`P ∉ ℓ₁` sub-case **unsatisfiability claim** comes
  from `state.md` § "Iteration 7" — written by researcher-3, not me. I
  did NOT fully verify the claim in this PREP; S13 should re-audit with
  a concrete counterexample or witness.
- The HH-6 cubic-real-root sketch comes from S11 PREP — I cite the
  conclusion but did not re-verify the cubic-discriminant analysis.
  The "P_i ∉ ℓ_i" caveat is my read; S11 may have a cleaner story.
- The S10 PREP HH-5 counterexample (`(0,0), (0,0.1), y=1`) is correct
  (I wrote it); other HH-5 counterexamples exist for any triple with
  `dist(P₁, P₂) < dist(P₂, ℓ)`.
- The recommendation "refactor `HHAxioms` to conditional forms" (Path A)
  may break the downstream `origami_degree_classification` theorem
  (parent line 575) if it relied on unconditional HH-5 / HH-7. The
  parent's algebraic-constructibility proof should be re-audited if
  Path A is taken. (Likely the theorem only uses HH-1, HH-2, HH-6 in
  the field-extension chain, since HH-6 is what gives the cubic-solving
  power — but this is worth verifying.)
- I have NOT run `./proofs/scripts/docker-build.sh
  Proofs.AngleTrisectionOQ05OQ04` to verify the file builds at v4.26.0.
  No Lean changes in this PREP — build status is unaffected.

## Next iteration after this PREP

S13 has two natural targets, depending on the slug owner's preference:

### Option 1 (Path A — refactor `HHAxioms`)

S13 ACT modifies `AngleTrisectionOQ05.lean:108-153`:
- Replace `hh5` field with `hh5_conditional`.
- Re-audit S7's HH-7 claim; replace `hh7` with `hh7_conditional` if
  warranted.
- Update `instance : HHAxioms` candidate at the bottom of the file (if
  any) to use the conditional forms.
- Re-audit `origami_degree_classification` for HH-5 / HH-7 dependency.

Estimated: ~80-120 LOC of changes, primarily in the structure
definition + downstream call-sites.

### Option 2 (Path B — non-instantiability theorem)

S13 ACT adds `theorem no_instance_HHAxioms_on_R2` (~50-80 LOC) +
formalises the HH-5 counterexample as a Lean lemma. The existing
`hh*_existence_*` theorems remain as case-by-case witnesses.

Estimated: ~100-150 LOC. Less invasive but documents a "negative result".

### Option 3 (continue constructive ACTs)

S13 ACT closes HH-3 intersecting (S9 PREP design) and/or HH-5 conditional
(S10 PREP design). Estimated 200-300 LOC. Doesn't address the
meta-question but extends the constructive coverage.

**My recommendation:** Option 1 (Path A) if the seeker's intent was a
working `instance`; Option 2 (Path B) if the gallery's value-add is the
"negative result" about the parent's overstrong axiomatisation.

## Future status

Once Path A (or B) is taken AND HH-3 intersecting / HH-5 conditional /
HH-6 cubic are all ACT'd, the slug's main forward-deliverable could
be either:

- `instance : HHAxioms FoldsOnR2` (Path A) — **`verified`** status,
  0 axioms, 0 sorries, complete constructive instantiation of the
  origami axiom system on the standard fold model.
- `theorem HHAxioms_unconditional_no_instance` (Path B) — **`verified`**
  status, a documented "negative result" formalising the gap between
  the parent's axiomatisation and the standard origami literature.

Either is gallery-worthy. The seeker's OQ-04 ("strengthen HH to capture
curved-crease origami") is a longer-term horizon; the prerequisite is
having a clean straight-crease baseline, which is what S3-S13 collectively
deliver.
