# S19a PREP — `(Subtype.val '' F i)` closed-image lemma + axiom signature alignment

**Iteration**: S19a PREP (doc-only sub-step memo)
**Author**: researcher-12
**Date**: 2026-05-12
**File**: this design note (no Lean / state.md / knowledge.md / meta.json edits)
**Predecessor**: S19 PREP `2026-05-12-s19-prep-graph-distance-bound.md`
(PR #18318, merged) — surfaced the §7 hypothesis-signature
inconsistency that this memo resolves
**Sister PRs in flight**: #17801 (stale S18b plumbing, pre-S18b-merge),
#17493 (stale 2026-05-08 S11 Brouwer specialization), #18177/#18257
(S18f — superseded by merged PR #18257 at 22:18 UTC); none touch this
memo's surface area

---

## §0. TL;DR

The S19 PREP §7 ("The hidden hypothesis: closed-valued F") identified
that the `axiom approx_selection_exists` signature (line 548 of
`SchauderFixedPointOQ03OQ01.lean`) lacks `hF_closed : ∀ x, IsClosed (F x)`,
yet the natural §4.b nearest-point-projection proof path requires
`F i` to be closed for the Hilbert projection theorem
(`exists_norm_eq_iInf_of_complete_convex`) to apply.

This S19a memo:

1. **Locks the signature update** for `theorem approx_selection_exists_proof`:
   add `(hF_closed : ∀ x, IsClosed (F x))` to the hypothesis stack,
   matching the existing kakutani-caller's hypothesis at line 1030.
2. **Designs the closed-image lemma** `image_isClosed_of_isClosed_of_compact`
   (or equivalent name): given `IsClosed (F i)` for the subtype-valued
   `F : SetValuedMap (↥S) (↥S)` and `IsCompact S`, the image
   `Subtype.val '' F i ⊆ EuclideanSpace ℝ (Fin n)` is closed.
3. **Maps the Mathlib API** for the proof (three candidate paths,
   ranked by fragility against v4.26.0 drift).
4. **Audits the call-site at kakutani** (line 1066) to confirm the
   `hF_closed` passing is already in place — zero-line caller patch.
5. **Anti-targets** (what S19a must NOT do) and **no-edit guarantee**.

Estimated S19a ACT delta: **+30 LOC**, all in `SchauderFixedPointOQ03OQ01.lean`:
1 new private lemma (~10 LOC), signature update on the eventual
`theorem approx_selection_exists_proof` (~5 LOC), no caller-site
patch needed at kakutani (already correct). No new imports.
Sorry count and axiom count unchanged at this step — S19a is purely
infrastructural for the S19b/c discharge that finally replaces the
axiom.

**This PR contains zero Lean code, zero edits to gallery files**
**(`meta.json` / `annotations.json` / `index.ts`), and zero edits to**
**`problem.md` / `state.md` / `knowledge.md`. One new file in the**
**existing `sessions/` subdir.**

---

## §1. The §7 inconsistency (verbatim from S19 PREP)

```
Decision point for S19: the cleanest fix is to add
(hF_closed : ∀ x, IsClosed (F x)) to the theorem signature. The
kakutani caller already has it; this is API parity, not a regression.
The axiom statement was strictly weaker than the kakutani caller's
hypothesis stack — this is a latent inconsistency that S19 surfaces.
```

The current axiom (line 548, verbatim):

```lean
axiom approx_selection_exists {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ↥S → ↥S, Continuous f ∧ IsGraphApproxSelection F (fun x => (f x : ↥S)) ε
```

The kakutani caller (line 1025–1030, verbatim):

```lean
theorem kakutani_from_brouwer {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_closed : ∀ x, IsClosed (F x))
    ...
```

The kakutani caller has `hF_closed` (line 1030) on top of the axiom's
hypothesis stack. So **adding `hF_closed` to `approx_selection_exists_proof`
is strictly a hypothesis-API parity move with `kakutani_from_brouwer`,
not a strengthening from the caller's perspective**: the caller already
has the hypothesis in scope and can pass it through (line 1066 site —
see §5 audit).

## §2. Why closedness is load-bearing for §4.b

The S19 PREP §6 Step 6a invokes
`exists_norm_eq_iInf_of_complete_convex` (Mathlib's Hilbert
projection theorem, in
`Mathlib/Analysis/InnerProductSpace/Projection.lean`):

```
exists_norm_eq_iInf_of_complete_convex
  : K.Nonempty → IsClosed K → Convex ℝ K →
    ∀ x, ∃ y ∈ K, ‖x - y‖ = ⨅ z ∈ K, ‖x - z‖
```

(Signature paraphrased; exact form may use `IsComplete K` rather than
`IsClosed K` for non-Hilbert spaces; in `EuclideanSpace ℝ (Fin n)`
the two coincide on bounded sets — see §3.)

The §4.b path of S19 needs to apply this to `K := Subtype.val '' F i`
viewed inside `EuclideanSpace ℝ (Fin n)`. The three preconditions are:

| Precondition | Source | Status |
|--------------|--------|--------|
| `K.Nonempty` | `hF_ne i` + image-of-nonempty | ✓ direct (1-line) |
| `Convex ℝ K` | `hF_convex i` | ✓ direct (axiom hypothesis, already present) |
| `IsClosed K` | `hF_closed i` + image-of-closed | **GAP** — this is what S19a fixes |

The closed-image step is **not the same as `hF_closed i`**:
`hF_closed i : IsClosed (F i)` is closedness of `F i` **as a subset
of `↥S`** (the subtype). The Hilbert projection wants closedness of
`Subtype.val '' F i` **as a subset of `EuclideanSpace ℝ (Fin n)`**
(the ambient inner-product space). The two are equivalent for `↥S`
**when `S` is compact** — that's the closed-image lemma.

## §3. Three candidate Mathlib API paths (ranked by fragility)

### §3.a Path A (preferred): `IsClosed.image_of_isClosed` via `IsCompact.isClosedMap`

```lean
private lemma image_subtype_isClosed_of_isClosed_of_compact
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  -- Subtype.val on a compact set ↥S → α is continuous + injective.
  -- The induced map from ↥S (compact) to α (Hausdorff) is closed.
  -- Image of closed under closed map is closed.
  have hCompact : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  have hClosedMap : IsClosedMap (Subtype.val : ↥S → α) := by
    exact (Continuous.isClosedMap continuous_subtype_val)
  exact hClosedMap T hT_closed
```

**Step-by-step**:
1. `[CompactSpace ↥S]` is derived from `hS_compact : IsCompact S` via
   `isCompact_iff_compactSpace.mp`. **API note**: this instance-derivation
   line is the *same one* used by S18d for the subordinate partition
   of unity (`exists_partition_subordinate_to_uhc_cover`,
   `haveI : CompactSpace ↥S` line). Reusable here without duplication.
2. `continuous_subtype_val` is the standard Mathlib lemma
   `Subtype.val : ↥S → α` is continuous (instance-supplied).
3. `Continuous.isClosedMap` requires either `[CompactSpace ↥S]` (we
   have it) + `[T2Space α]` (need to confirm `EuclideanSpace ℝ (Fin n)`
   is `T2Space`; it is — every `MetricSpace` is `T2Space`) — OR — the
   weaker hypothesis-name variant `IsCompact.isClosedMap` /
   `CompactSpace.isClosedMap`. The pinned v4.26.0 may use either name.
4. Apply the resulting `IsClosedMap` to `T : Set ↥S` closed, obtain
   `Subtype.val '' T` closed.

**Mathlib lemma names involved (audit needed)**:
- `isCompact_iff_compactSpace` (or `IsCompact.compactSpace`)
- `continuous_subtype_val`
- `Continuous.isClosedMap` (compact → Hausdorff variant) OR
  `IsCompact.isClosedMap` OR
  `CompactSpace.isClosedMap`

The fragility against drift is **moderate**: at least one of the three
variants should resolve at v4.26.0. The structural fact "continuous
map from compact space to Hausdorff space is closed" is one of the
most classical lemmas in topology; Mathlib will not regress on it.
**Recommended action**: implementer should grep the pinned rev for
the exact name with `gh api -X GET search/code -f q='isClosedMap repo:leanprover-community/mathlib4 path:Topology/Constructions.lean'`.

### §3.b Path B: `IsClosed.preimage` + injectivity of `Subtype.val`

```lean
private lemma image_subtype_isClosed_via_preimage
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  -- Embedding chain: T ↪ ↥S ↪ α, ↥S is compact, α is Hausdorff,
  -- so Subtype.val is a closed embedding, hence image is closed.
  rw [← Set.image_eq_image Subtype.val_injective]
  -- Reduces to showing `Subtype.val ⁻¹' (Subtype.val '' T) = T`, then
  -- applying `IsClosed.preimage continuous_subtype_val` (wrong direction!).
  sorry  -- Path B is not the right shape; left here to mark the wrong path.
```

**Verdict on Path B**: rejected. The injectivity of `Subtype.val`
gives `Subtype.val ⁻¹' (Subtype.val '' T) = T` (the equation; not just
⊇), but this rewrites in the *wrong* direction: closed-image is not a
direct consequence of closed-preimage without an additional
"embedding is closed" structural fact, which is exactly Path A's
content. Documented here so the implementer does not waste time on
this dead end.

### §3.c Path C: ad-hoc compactness argument

```lean
private lemma image_subtype_isClosed_via_compactness
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  -- Compact subset of Hausdorff space is closed.
  -- T is closed in ↥S, ↥S is compact, so T is compact in ↥S.
  -- Subtype.val is continuous, so its image is compact in α.
  -- α is Hausdorff, so the compact image is closed.
  have hCompact_T : IsCompact T := hT_closed.isCompact_of_compactSpace
  -- ... actual name may be hT_closed.isCompact or similar; needs audit.
  have hImg_compact : IsCompact ((Subtype.val '' T : Set α)) :=
    hCompact_T.image continuous_subtype_val
  exact hImg_compact.isClosed
```

**Step-by-step**:
1. Closed subset of a compact space is compact:
   `IsClosed.isCompact_of_compactSpace` or `IsClosed.isCompact`
   (the exact name in v4.26.0 needs audit; one of `IsCompact.of_isClosed`,
   `IsClosed.isCompact`, `isCompact_of_isClosed_subset` should resolve).
2. Continuous image of a compact set is compact: `IsCompact.image`.
3. Compact subset of a Hausdorff (T2) space is closed:
   `IsCompact.isClosed`.

**Verdict on Path C**: viable, but slightly more steps than Path A.
The advantage: each individual lemma is more elementary than Path A's
`IsClosedMap` (which is structural). Use Path C as the **Plan-B** if
Path A's `isClosedMap`-style lemma drifts.

**Recommended**: Path A first, Path C as fallback. Both produce the
same closed-image fact; Path A is 1–2 fewer lines.

## §4. Exact lemma statement (locked)

```lean
/-- **S19a helper**: the ambient-space image of a closed set of a
    compact subtype is closed.

    Specialised use: `(Subtype.val '' F i)` is closed in
    `EuclideanSpace ℝ (Fin n)` whenever `F i` is closed in `↥S` and
    `S` is compact. This is the precondition required by
    `exists_norm_eq_iInf_of_complete_convex` (the Hilbert projection
    theorem) in S19b's nearest-point construction for the
    `approx_selection_exists_proof` discharge.

    Generic in the ambient `α` (no `EuclideanSpace`-specific
    assumptions) — directly usable beyond the immediate Schauder-FP
    context. -/
private lemma image_subtype_isClosed_of_isClosed_of_compact
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  -- Path A skeleton; see §3.a for full body.
  have hCompact : CompactSpace ↥S :=
    isCompact_iff_compactSpace.mp hS_compact
  have hClosedMap : IsClosedMap (Subtype.val : ↥S → α) :=
    Continuous.isClosedMap continuous_subtype_val
  exact hClosedMap T hT_closed
```

**Expected LOC**: 10 lines (header docstring 6 + body 4), or 8 lines
if the docstring is trimmed. Insert location: after S18a's
`convex_combination_of_partition_in_S` (line ~625) and before S18b's
`typeclass_witnesses_compact_subset` (line ~700) — alongside the other
generic auxiliary lemmas.

**Generic placement justification**: the lemma is **not specific** to
either `EuclideanSpace ℝ (Fin n)` or the Schauder-FP setting. It can
later be upstreamed to Mathlib's `Mathlib/Topology/Subset.lean` or
similar; for now it lives `private` in `SchauderFixedPointOQ03OQ01.lean`
matching the S18a–e convention.

## §5. Caller-site audit (kakutani at line 1066)

The existing call at line 1066:

```lean
have happrox := approx_selection_exists S hS_ne hS_compact hS_convex F hF_ne hF_convex' hF_uhc' (ε/2) ...
-- Actually the full body is at lines 1060-1070; relevant args are:
--   ..., hF_closed' hF_uhc happrox_total
```

Looking at lines 1038–1066:

```lean
1038  have hF_closed' : ∀ x ∈ (Set.univ : Set ↥S), IsClosed (F x) :=
1039    fun x _ => hF_closed x
...
1066    hF_closed' hF_uhc happrox_total
```

The kakutani caller already builds `hF_closed' : ∀ x ∈ univ, IsClosed (F x)`
from its own `hF_closed : ∀ x, IsClosed (F x)` hypothesis. Whether the
S19 implementer's signature for `approx_selection_exists_proof` should
take `∀ x, IsClosed (F x)` (the kakutani caller's form) or
`∀ x ∈ univ, IsClosed (F x)` (the `hF_closed'` derived form) is a
**stylistic choice**.

**Locked recommendation**: take `∀ x, IsClosed (F x)` (the simpler
form), matching the kakutani caller's *outer* hypothesis. The caller
then passes `hF_closed` directly (no need to thread the `hF_closed'`
universe-restricted variant through). This makes the S19a signature
update at the caller site a **zero-line patch**:

```lean
-- Line 1066, BEFORE:
-- ... hF_closed' hF_uhc happrox_total
-- Line 1066, AFTER:
-- ... hF_closed hF_uhc happrox_total
```

Or, if S19c keeps `hF_closed'` as an internal helper (no patch
needed): pass `hF_closed'` flattened to `∀ x, IsClosed (F x)` by
`fun x => hF_closed' x (Set.mem_univ x)`.

**Either way, the caller-site update is ≤ 2 LOC**. Document in S19c.

## §6. The new theorem signature (locked)

```lean
theorem approx_selection_exists_proof {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_closed : ∀ x, IsClosed (F x))        -- NEW: S19a addition
    (hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ↥S → ↥S, Continuous f ∧ IsGraphApproxSelection F (fun x => (f x : ↥S)) ε
```

**Diff vs the axiom** (line 548): exactly one new hypothesis line
inserted between `hF_ne` and `hF_convex`. Hypothesis ordering matches
the kakutani caller (line 1027–1031).

**Justification**: this hypothesis is *strictly necessary* for the
nearest-point projection in S19b §4.b path. Without it, the §4.b path
must use a non-attaining infimum (using `iInf_lt` instead of
`exists_norm_eq_iInf`), which doubles the proof complexity. The
mathematical content is essentially the same; the closed-valued
hypothesis is the cleanest API for both Mathlib and the kakutani
caller.

## §7. Anti-targets

Things S19a must NOT do:

1. **Do not discharge the axiom yet.** S19a is purely infrastructural:
   it adds the closed-image lemma and locks the eventual signature
   update. The actual replacement of `axiom approx_selection_exists`
   with `theorem approx_selection_exists_proof` happens in S19c (the
   final assembly step per S19 PREP §11).
2. **Do not modify** `axiom approx_selection_exists` at line 548. The
   axiom remains in the file until S19c lands. S19a only **adds** a
   new private lemma.
3. **Do not add** `(hF_closed : ∀ x, IsClosed (F x))` to the kakutani
   caller's `theorem kakutani_from_brouwer` (line 1025–1030). That
   hypothesis is **already present** at line 1030 (verified in §1
   verbatim quote). No caller-API change is needed.
4. **Do not attempt the eventual S19b convex-combination accounting**
   (S19 PREP §4.b / §4.c). That is the *hard* mathematical half and
   is genuinely separate work. S19a is the *easy* half.
5. **Do not refactor** S18a–f helpers. They're correct as-is and the
   S18g propagation (S19 PREP §11 step 1) is a separate concern.
6. **Do not add** the closed-image lemma to a Mathlib upstream PR.
   While the lemma is generic enough to upstream, that's a separate
   workflow; keep it `private` in `SchauderFixedPointOQ03OQ01.lean`
   for now, matching S18a–e convention.
7. **Do not bump** `meta.json` lineCount / theoremCount / etc. in
   this PR — those bumps land with the Lean delta in S19a ACT (a
   future PR), not in this doc-only PREP.
8. **Do not extend** `problem.md` / `state.md` / `knowledge.md` from
   this branch. The state advance happens in the S19a ACT PR after
   the Lean file lands.

## §8. Mathlib API audit (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

The S19a closed-image lemma relies on the following Mathlib names.
All three paths (§3.a Path A, §3.c Path C) overlap in API
requirements. Names are checked against v4.26.0 conventions and
the existing in-file usage (S18b, S18d).

| Name | Module | Used in | Status |
|------|--------|---------|--------|
| `isCompact_iff_compactSpace` | `Mathlib/Topology/Compactness/Compact.lean` (or similar) | S18b `typeclass_witnesses_compact_subset`, S18d `exists_partition_subordinate_to_uhc_cover` | OK — in-file precedent for the `haveI : CompactSpace ↥S` pattern. |
| `continuous_subtype_val` | `Mathlib/Topology/Subtype.lean` | S14 `exists_continuous_proj_convex` (transitively) | OK — universally used Mathlib API. |
| `Continuous.isClosedMap` (T2 + CompactSpace variant) | `Mathlib/Topology/Constructions.lean` (likely) | new for S19a | **Audit needed.** Possible alternative names: `IsCompact.isClosedMap`, `CompactSpace.isClosedMap`, `Continuous.isClosedMap_of_compactSpace`. |
| `IsClosedMap` apply at `T : Set ↥S` | derived API | new for S19a | OK — application of a `IsClosedMap` value is type-uniform. |
| `IsClosed.isCompact` (T : Set ↥S, ↥S compact) | `Mathlib/Topology/Compactness/Compact.lean` (Path C alt) | not in-file | OK if Path A drifts. |
| `IsCompact.image` | `Mathlib/Topology/Compactness/Compact.lean` (Path C alt) | S18d `exists_partition_subordinate_to_uhc_cover` (transitively) | OK. |
| `IsCompact.isClosed` (compact ⇒ closed in T2) | `Mathlib/Topology/Compactness/Compact.lean` (Path C alt) | not in-file | OK. |

**Audit method without `lake build`**: search the pinned
Mathlib rev via GitHub API:

```bash
gh api -X GET search/code -f q='isClosedMap repo:leanprover-community/mathlib4 path:Topology'
```

If `Continuous.isClosedMap` resolves at v4.26.0 with the expected
signature `(f : α → β) [CompactSpace α] [T2Space β] : Continuous f → IsClosedMap f`,
Path A is the chosen route. Otherwise fall back to Path C (3-line
chain via `IsClosed.isCompact` + `IsCompact.image` + `IsCompact.isClosed`).

**v4.26.0 drift insurance**: per memory **"List.length_pos.mpr drift v4.26"**,
do not trust any single API name to survive. Plan-B (Path C) is the
3-line direct-chain insurance.

## §9. LOC budget

| Step | LOC | Source |
|------|-----|--------|
| Private lemma docstring | ~6 | §4 |
| Private lemma body (Path A) | ~4 | §3.a |
| **Total S19a (this sub-step alone)** | **~10** | |
| Future S19c signature update at axiom-replacement | ~1 | §6 |
| Future S19c caller-site at kakutani | ~0–2 | §5 |

S19a is intentionally minimal: a single 10-line private lemma that
unlocks the S19b §4.b nearest-point path. The signature update and
caller-site patch are documented here but actually land in S19c
(the axiom-replacement PR).

## §10. Provenance & memory hooks

* **Predecessor PREP**: S19 PREP `2026-05-12-s19-prep-graph-distance-bound.md`
  (PR #18318, merged 2026-05-12T22:14Z) — §7 of that doc surfaced the
  inconsistency that this S19a memo resolves.
* **Pattern (memory)**:
  - **"researcher-12 quintuple-PREP doc-only session (2026-05-12 ~17:30 UTC)"** —
    doc-only `sessions/` sub-step PREP for a focused angle. Pattern (3)
    "arithmetic-correction PREP" / pattern (4) "orthogonal-axiom for
    multi-axiom slug" both apply: S19a is an orthogonal-axiom for the
    `approx_selection_exists` axiom (Axiom 2; the file has 2 axioms,
    `brouwer_unit_ball` is Axiom 1 and out of scope here).
  - **"List.length_pos.mpr drift v4.26"** — applies to the
    `Continuous.isClosedMap` vs `IsCompact.isClosedMap` vs
    `CompactSpace.isClosedMap` audit in §8. Plan-B (Path C) is the
    direct insurance.
  - **"Write tool absolute-path routes to main repo, not worktree"** —
    this file is created via worktree-relative path under
    `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-12/`
    to ensure it lands in the worktree's working tree.
    Verified by `git rev-parse --show-toplevel` before write.

* **Anti-pattern avoided**: chasing the S19 PREP's full §4.b
  convex-combination accounting (the hard half) in a single sub-step.
  S19a deliberately scopes to the *trivial* §6 Step 6a half
  ("closed-image precondition for the projection") and defers the
  hard convex-combination accounting to S19b. This matches the S19
  PREP §11 step-2 estimate of "~30 lines" for S19a, and keeps the
  PREP-to-ACT translation **single-shot single-file**.

## §11. No-edit guarantee

This PR creates **one new file**, in the existing `sessions/`
subdirectory (does not touch any other path):

```
research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/sessions/2026-05-12-s19a-prep-closed-image-and-signature-alignment.md
```

It does **not** touch:

* `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean` (Lean source)
* `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/problem.md`
* `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/state.md`
* `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/knowledge.md`
* `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/sessions/2026-05-12-s19-prep-graph-distance-bound.md`
  (the existing S19 PREP)
* `research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/s17-cellina-mathlib-api-survey.md`
* Any of the in-tree `s10-` through `s18e-` design notes
* `src/data/proofs/schauder-fixed-point-oq-03-oq-01-incomplete-01/{meta,annotations}.json`
* `src/data/proofs/schauder-fixed-point-oq-03-oq-01-incomplete-01/index.ts`
* `proofs/lakefile.toml` (no new imports needed)

Conflict-free with:
* PR #18177 / #18257 (S18f, both merged or stale — the S18f input-ball
  refinement and orphan-recovery; this PREP only **references** S18f
  helper as a black-box hypothesis in §3)
* PR #17801 (stale S18b plumbing, pre-S18b-merge from 03:53 UTC)
* PR #17493 (very stale S11 Brouwer specialization from 2026-05-08)
* PR #18318 (S19 PREP, merged) — this S19a memo is a sub-step
  refinement *complementing* it (different file path under
  `sessions/`)

By construction (new file in new path), no merge conflict possible.
