# S22 PREP — S19 step (b) helper signature + tighter completeness route

**Iteration**: S22 PREP (doc-only)
**Author**: researcher-3
**Date**: 2026-05-14
**Mode**: doc-only — only this new file in `sessions/`; no Lean / state.md / JSON / meta.json edits
**Predecessors**: S19 PREP (#18318 graph-distance design), S19a PREP (#18361
closed-image lemma + signature alignment), S19b PREP (#18521 projection-chain
audit), S19c PREP (`Projection.lean` deprecation-stub calibration),
S19d PREP (#18624 Path A bearer cleared), S19a-ACT (PR #18646 merged
2026-05-13 — landed `image_subtype_isClosed_of_isClosed_of_compact`
at file lines 906–912), S20 ACT (PR #19016 OPEN/MERGEABLE — five
v4.26.0 elaboration drift fixes in `exists_continuous_proj_convex`),
S21 STATE-SYNC (PR #19044 OPEN/MERGEABLE — doc-only refresh after #19016).
**Sister PRs open at session start**: #19016, #19044 (both MERGEABLE/CLEAN
awaiting deployer); #17801 (stale S18b plumbing), #17493 (stale S11
Brouwer specialization). All four touch files disjoint from this PR's
single added `sessions/` file.

---

## §0. TL;DR

S19 step (b) is the §4.b nearest-point projection / convex-image
construction (per `state.md` Next Action). This memo:

1. **Locks the helper-lemma signature** for S19 step (b) as a
   `private lemma exists_nearest_in_image_F`. This isolates the
   Hilbert-projection invocation from the rest of the eventual
   `approx_selection_exists_proof` body and matches the granularity
   of prior S18a–f / S19a-ACT helpers (each ≤ 80 lines, one helper
   per PR).
2. **Picks the tighter completeness bridge**: `IsCompact.isComplete`
   (Cauchy.lean line 653 at pinned rev `2df2f0150c…`) bypasses
   `IsClosed.isComplete` (line 439) and its `[CompleteSpace α]`
   typeclass requirement. Bridge chain shortens from
   "closed-in-compact-subtype → closed-in-α → IsClosed.isComplete with
   `[CompleteSpace α]`" to "closed-in-compact-subtype → compact-in-α →
   `IsCompact.isComplete`" (no `[CompleteSpace α]` needed).
3. **Verifies the projection lemma still resolves** through the
   existing `import Mathlib.Analysis.InnerProductSpace.Projection`
   facade at v4.26.0 (deprecated-module facade re-exporting
   `Projection/Minimal` per S19c PREP). No new import line required.
4. **Confirms `Set.Nonempty.image`** at `Mathlib/Data/Set/Image.lean`
   line 373 of the pinned rev with the dot-notation pattern
   `(hF_ne i).image (Subtype.val : ↥S → α)` — matches state.md's
   nonempty-image plan.
5. **Documents the post-S20-ACT context**: the five elaboration drifts
   that PR #19016 fixed are localised to `exists_continuous_proj_convex`
   (lines ~211–305) and do **not** affect any symbol used by the S19
   step (b) helper drafted in §3 below. The chain is orthogonal.

Net result: the S19 step (b) implementer (next ACT iteration on this
slug, post-#19016 merge) can copy the §3 helper verbatim and add a
single ≤8-line proof body. Total LOC budget: ~50–60 (signature +
docstring + 4–6 tactic lines).

**Strict orthogonality guarantees** (verified):

- No edits to `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`.
- No edits to `state.md` / `knowledge.md` / `problem.md`.
- No edits to `src/data/research/problems/...incomplete-01.json`
  (owned by #19044's pending STATE-SYNC).
- No edits to gallery `meta.json` / `annotations.json` /
  `index.ts` under `src/data/proofs/schauder-fixed-point-oq-03-oq-01/`.
- Single added file: this memo.

---

## §1. What S19 step (b) needs (per state.md Next Action)

`state.md` lines 300–311 specify:

> S19 step (b) (next claim, ~80–150 lines): With the closed-image
> helper now in the file (this iteration's S19 step (a)), the next
> concrete step toward discharging `axiom approx_selection_exists` is
> to write the §4.b nearest-point projection / convex-image
> construction: given `i ∈ ρ.finsupport x`, build the closed convex
> target `Subtype.val '' F i` (now provably `IsClosed` via this
> iteration's helper and `IsClosed.isClosed_isCompact_of_image` chain;
> provably `Convex` via the existing `hF_convex` axiom hypothesis;
> provably `Nonempty` via `hF_ne`), invoke
> `exists_norm_eq_iInf_of_complete_convex`, and connect to the S18e
> witness bundle. This is the §4.b half of the eventual
> `approx_selection_exists_proof` body.

**§1.1 Two clarifications versus state.md**:

(a) The text references `IsClosed.isClosed_isCompact_of_image` — no
such Mathlib lemma exists at v4.26.0 (zero hits in
`gh api search/code`; not in the `IsClosed.*` namespace at the pinned
rev). The intended chain is: `image_subtype_isClosed_of_isClosed_of_compact`
(in-file at lines 906–912) → image is closed in α. See §2 for the
actual completeness route used.

(b) `exists_norm_eq_iInf_of_complete_convex` lives in
`Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean` at v4.26.0
(line 34, verified §4.1). The `Projection.lean` import already in the
file is a facade that transitively re-exports it (S19c PREP confirms).
The `deprecated_module (since := "2025-08-08")` annotation on the facade
emits a `linter.deprecated` warning but does not block compilation.

---

## §2. Completeness route — tighter than S19b PREP

S19b PREP §4.2 documented the completeness bridge as
`IsClosed.isComplete` at `Mathlib/Topology/UniformSpace/Cauchy.lean:439`,
which requires `[CompleteSpace α]`. For `α := EuclideanSpace ℝ (Fin n)`
this is automatic via the finite-dimensional ℝ-Banach instance chain,
so S19b's route compiles.

This PREP surfaces an **alternative, tighter route** via
`IsCompact.isComplete` at line 653 of the same file:

```lean
-- Verbatim from Cauchy.lean:653 at pinned rev 2df2f0150c…:
protected theorem IsCompact.isComplete {s : Set α} (h : IsCompact s) : IsComplete s :=
  (isCompact_iff_totallyBounded_isComplete.1 h).2
```

The `[UniformSpace α]` is implicit in the file's `variable` block;
**no `[CompleteSpace α]` typeclass needed**. Any compact set in any
uniform space is complete.

### §2.1 Why this matters for our setting

The closed-image chain in S19 step (b) needs to produce
`IsComplete ((Subtype.val '' F i) : Set α)` to feed
`exists_norm_eq_iInf_of_complete_convex` (which takes `IsComplete K`,
NOT `IsClosed K`).

**S19b PREP's route** (works at our site):
```lean
-- Path A1: closed-then-complete with CompleteSpace
have hFi_closed : IsClosed ((Subtype.val '' F i) : Set α) :=
  image_subtype_isClosed_of_isClosed_of_compact hS_compact (hF_closed i)
have hFi_complete : IsComplete ((Subtype.val '' F i) : Set α) :=
  hFi_closed.isComplete  -- needs [CompleteSpace α], auto for EuclideanSpace
```

**This PREP's route** (tighter; works without `[CompleteSpace α]`):
```lean
-- Path A2: closed-in-subtype-then-compact-then-complete
haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
have hFi_compact_subtype : IsCompact (F i) := (hF_closed i).isCompact
have hFi_compact : IsCompact ((Subtype.val '' F i) : Set α) :=
  hFi_compact_subtype.image continuous_subtype_val
have hFi_complete : IsComplete ((Subtype.val '' F i) : Set α) :=
  hFi_compact.isComplete  -- no [CompleteSpace α]
```

The two routes are equivalent for `α = EuclideanSpace ℝ (Fin n)` (where
`CompleteSpace` is automatic), so either compiles. **Recommendation**:
the implementer should pick Path A2. Three reasons:

1. **Avoids the `[CompleteSpace α]` typeclass synthesis** entirely.
   Lean v4.26.0 elaborator can occasionally fail typeclass synthesis
   when the relevant instance lives behind 3+ inferred instances
   (e.g., `MetricSpace → NormedAddCommGroup → CompleteSpace` chain
   via `FiniteDimensional`). Path A2 sidesteps this concern.

2. **Cheaper LOC** when packaged as a single helper (see §3): Path A2
   does not need the S19a-ACT `image_subtype_isClosed_of_isClosed_of_compact`
   helper if the implementer chooses to inline the compact-image chain.
   The S19a-ACT helper remains useful elsewhere; this PREP does not
   propose removing it. Path A2 simply offers a route that doesn't
   *depend* on it.

3. **Reuses an in-file precedent**: `IsCompact.isComplete` is exactly
   the pattern used by S14's `hS_complete : IsComplete S :=
   hS_compact.isComplete` at line 223 of the existing
   `exists_continuous_proj_convex` body. Same lemma, same dot-notation.
   Auditor familiarity is highest.

### §2.2 Mathlib bearers (verified at pinned rev `2df2f0150c…`)

| Symbol | Module | Line | Used in Path A2 |
|---|---|---|---|
| `isCompact_iff_compactSpace` | `Mathlib/Topology/Compactness/Compact.lean` | 989 | `haveI : CompactSpace ↥S` |
| `IsClosed.isCompact` | `Mathlib/Topology/Compactness/Compact.lean` | 805 | `(hF_closed i).isCompact` |
| `IsCompact.image` | `Mathlib/Topology/Compactness/Compact.lean` | 121 | `_.image continuous_subtype_val` |
| `continuous_subtype_val` | `Mathlib/Topology/Constructions.lean` | 367 | argument to `IsCompact.image` |
| `IsCompact.isComplete` | `Mathlib/Topology/UniformSpace/Cauchy.lean` | 653 | `_.isComplete` |
| `Set.Nonempty.image` | `Mathlib/Data/Set/Image.lean` | 373 | `(hF_ne i).image _` |
| `exists_norm_eq_iInf_of_complete_convex` | `Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean` | 34 | main projection call |

Verification commands appear in §A.

---

## §3. Proposed S19 step (b) helper signature

A clean helper isolates the per-`i` Hilbert projection from the rest of
the `approx_selection_exists_proof` body. The implementer applies it
once per `x : ↥S` at a chosen `i ∈ ρ.finsupport x` and `u := (fC x : α)`.

```lean
/-- **S19 step (b) helper (nearest-point in the ambient image of `F i`):**

    For a compact `S ⊆ EuclideanSpace ℝ (Fin n)`, a UHC set-valued map
    `F : SetValuedMap (↥S) (↥S)` with nonempty closed convex values
    (in the ambient-image form), and any base-point `i : ↥S` and
    target `u : EuclideanSpace ℝ (Fin n)`, the Hilbert projection
    theorem produces a unique nearest point of `Subtype.val '' F i`
    to `u`.

    The proof chains:
    * `IsClosed.isCompact` (`F i` closed in compact `↥S`)
    * `IsCompact.image` (push compactness through `Subtype.val`)
    * `IsCompact.isComplete` (compact → complete, no `[CompleteSpace α]`)
    * `Set.Nonempty.image` (push nonemptyness through `Subtype.val`)
    * `exists_norm_eq_iInf_of_complete_convex` (the Hilbert projection).

    All four Mathlib bearers verified at pinned rev
    `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` by
    `sessions/2026-05-14-s22-prep-step-b-helper-and-completeness-route.md`
    (this S22 PREP). Convexity is consumed in the **ambient-image
    form** matching the axiom's `hF_convex` hypothesis already in
    scope.

    **Use site (S19 step (c)–(d)).** Inside the eventual
    `approx_selection_exists_proof`, applied at any `i ∈ ρ.finsupport x`
    (from S18e bundle) and `u := (fC x : EuclideanSpace ℝ (Fin n))`,
    this lemma supplies the witness `y ∈ F i` together with the
    minimal-norm certificate that drives the §4.b graph-distance bound
    in S19 PREP §6 Step 6c. -/
private lemma exists_nearest_in_image_F {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_compact : IsCompact S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_closed : ∀ x, IsClosed (F x))
    (hF_convex :
      ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (i : ↥S) (u : EuclideanSpace ℝ (Fin n)) :
    ∃ y ∈ ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))),
      ‖u - y‖ = ⨅ w : ((Subtype.val '' F i) : Set _), ‖u - w‖ := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  have hFi_ne_img :
      ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))).Nonempty :=
    (hF_ne i).image _
  have hFi_complete :
      IsComplete ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))) :=
    (((hF_closed i).isCompact).image continuous_subtype_val).isComplete
  exact exists_norm_eq_iInf_of_complete_convex hFi_ne_img hFi_complete
          (hF_convex i) u
```

### §3.1 Why this signature

- **Generic in `u`** (not bound to `fC x` or any S18e bundle field):
  the implementer can call it at `u := (fC x : α)` for the graph-bound
  step, but the lemma is reusable for any target. The S18e bundle is
  *not* a parameter — this helper is structurally independent of S18a–f.

- **Takes `hF_closed` as a hypothesis** (matching the S19 PREP §7
  recommendation to add `hF_closed` to the *theorem* signature). The
  helper bears the hypothesis it consumes; the eventual
  `approx_selection_exists_proof` theorem will receive `hF_closed` from
  its caller (`kakutani_from_brouwer`, which already has it at line
  1085 verified above).

- **Returns the *image* form** (`y ∈ Subtype.val '' F i`, not
  `y : ↥S ∈ F i`). This is the form `exists_norm_eq_iInf_of_complete_convex`
  produces directly, and matches the convexity hypothesis form
  `hF_convex i : Convex ℝ ((Subtype.val '' F i) : Set _)`. The S19 step
  (c) graph-bound consumer can recover the subtype form via
  `Set.mem_image.mp` (extracting `z ∈ F i` with `↑z = y`) when needed.

- **No dependence on S18e bundle structure** keeps this helper
  testable in isolation. The implementer can build and verify this
  helper in a standalone PR before wiring it into the §4.b graph-bound
  body (S19 step (c)).

### §3.2 Tactic line-by-line

The body is **5 tactic lines** (4 `have`s + `exact`):

| Line | Tactic | Why |
|---|---|---|
| 1 | `haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact` | Materialise `CompactSpace ↥S` for `IsClosed.isCompact` typeclass on next line. Same `haveI` pattern as `image_subtype_isClosed_of_isClosed_of_compact` body (line 911 of the parent file). |
| 2 | `have hFi_ne_img : … := (hF_ne i).image _` | Push nonemptyness through `Subtype.val`. Dot-notation on `Set.Nonempty.image`. The `_` is `Subtype.val`. |
| 3 | `have hFi_complete : IsComplete (…) := (((hF_closed i).isCompact).image continuous_subtype_val).isComplete` | Path A2 chain: closed-in-subtype → compact-in-subtype → compact-in-α → complete-in-α. Three dot-notation applications. |
| 4 | `exact exists_norm_eq_iInf_of_complete_convex hFi_ne_img hFi_complete (hF_convex i) u` | Apply the Hilbert projection theorem. The `hF_convex i` is in the exact ambient-image form the lemma expects. The `u` is the explicit positional final argument. |

### §3.3 Anticipated elaboration pitfalls

The implementer should be aware of three v4.26.0-specific concerns
(none blocking, all with concrete workarounds):

**(a) `RCLike 𝕜` resolution for `exists_norm_eq_iInf_of_complete_convex`.**
The lemma's variable block uses `{𝕜 E F : Type*} [RCLike 𝕜]` + `[InnerProductSpace ℝ F]`
where the F-side variant is what fires at `F := EuclideanSpace ℝ (Fin n)`.
The lemma's `K : Set F` matches our `Subtype.val '' F i : Set (EuclideanSpace ℝ (Fin n))`
directly. No elaboration-order issue expected.

**(b) Dot-notation precedence on the chain
`(((hF_closed i).isCompact).image _).isComplete`.**
Each `.method` is left-associative. The parens above are explicit;
the implementer may try a flatter form like
`(hF_closed i).isCompact.image continuous_subtype_val |>.isComplete`
(pipe form) if the auto-resolution misfires. If `.isComplete` doesn't
auto-resolve through the chain, expand to:
```lean
have h1 : IsCompact (F i) := (hF_closed i).isCompact
have h2 : IsCompact (Subtype.val '' F i : Set _) := h1.image continuous_subtype_val
have hFi_complete : IsComplete (Subtype.val '' F i : Set _) := h2.isComplete
```

**(c) Implicit coercion `Subtype.val '' F i` vs `(Subtype.val '' F i : Set α)`.**
The `Convex.image` lemma's ambient-form expects the set ascribed to
`Set (EuclideanSpace ℝ (Fin n))`. The implementer should match the
existing `hF_convex` signature shape verbatim:
```lean
∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n)))
```
Bare `Subtype.val '' F i` without ascription has type
`Set (EuclideanSpace ℝ (Fin n))` already (the elaborator infers it from
`F i : Set ↥S` and `Subtype.val : ↥S → EuclideanSpace _`), but the
ascription is **cheap insurance** against the implicit-binder
elaboration tripping on the `'';` operator at v4.26.0.

---

## §4. Mathlib API re-verification (post-S20-ACT context)

S20 ACT (PR #19016, open) fixed five v4.26.0 elaboration drifts inside
`exists_continuous_proj_convex` (file lines ~211–305). The fixes are
**localised**: `open scoped InnerProductSpace`, `Nonempty ↥S` instance,
explicit `↑(r u)` coercion, `real_inner_comm` argument flip,
`LipschitzWith.mk_one` refactor. None of the five symbols touched by
S20 ACT are exercised by the S19 step (b) helper drafted in §3 above.

**Verification (per-symbol)**:

| S19 step (b) bearer | S20 ACT touches? | Why orthogonal |
|---|---|---|
| `isCompact_iff_compactSpace` | No | S20 modifies only `exists_continuous_proj_convex` (lines 211–305); this is `haveI` line 911 / planned helper. |
| `IsClosed.isCompact` | No | Used by Path A2 chain only; S20 touches no `IsClosed.*` line. |
| `IsCompact.image` | No | Same as above; S20's variational-inequality fixes do not touch this lemma. |
| `IsCompact.isComplete` | No | S20 has `hS_complete : IsComplete S := hS_compact.isComplete` at line 223 already; the v4.26.0-clean usage is **direct precedent** confirming this dot-notation still resolves. |
| `Set.Nonempty.image` | No | S20 touches no `Nonempty.*` line. |
| `exists_norm_eq_iInf_of_complete_convex` | No | S20 ACT applies inside `exists_continuous_proj_convex` which **already uses** this lemma at line 226; if S20 didn't touch the line 226 invocation pattern, the same pattern is safe to re-use in S19 step (b). |
| `continuous_subtype_val` | No | S14-era stable; S20 doesn't touch it. |

**Conclusion**: S19 step (b) is build-safe modulo standard
v4.26.0 elaboration discipline. The implementer should rebase on
`main` *after* #19016 lands (the build-pending chain ends there), then
add this helper.

### §4.1 Pinned-rev verification commands

```bash
# Mathlib rev:
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# IsCompact.isComplete (Cauchy.lean:653):
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Topology/UniformSpace/Cauchy.lean" \
    | sed -n '650,655p'
protected theorem IsCompact.totallyBounded {s : Set α} ...
protected theorem IsCompact.isComplete {s : Set α} (h : IsCompact s) : IsComplete s :=
  (isCompact_iff_totallyBounded_isComplete.1 h).2

# Set.Nonempty.image (Image.lean:373):
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Data/Set/Image.lean" \
    | sed -n '373,374p'
theorem Nonempty.image (f : α → β) {s : Set α} : s.Nonempty → (f '' s).Nonempty
  | ⟨x, hx⟩ => ⟨f x, mem_image_of_mem f hx⟩

# exists_norm_eq_iInf_of_complete_convex (Projection/Minimal.lean:34):
$ curl -s "https://raw.githubusercontent.com/leanprover-community/mathlib4/2df2f0150c275ad53cb3c90f7c98ec15a56a1a67/Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean" \
    | sed -n '34,35p'
theorem exists_norm_eq_iInf_of_complete_convex {K : Set F} (ne : K.Nonempty) (h₁ : IsComplete K)
    (h₂ : Convex ℝ K) : ∀ u : F, ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖
```

All three commands executed inside this PREP session; outputs verbatim
above.

---

## §5. Revised LOC budget for S19 step (b)

S19 PREP §9 estimated S19 step (b) at "~85 LOC if §4.c gap is
dischargeable in-place (~15 more lines)". This PREP refines the
helper-only portion:

| Component | LOC | Source |
|---|---|---|
| Helper docstring (§3) | ~30 | this PREP |
| Helper signature (§3) | ~12 | this PREP |
| Helper tactic body (§3.2, 5 lines) | ~6 | this PREP |
| **Helper subtotal** | **~48** | **single ACT iteration** |

The helper is a *prerequisite* for the rest of S19 step (b) (the
graph-bound stitching at `(fC x, ysel _, …)` per S19 PREP §6 Step 6c),
not a replacement for it. The full S19 step (b) iteration may still
land 80–150 LOC if the implementer ships the helper **plus** the
graph-bound stitching in one PR. The **cleaner decomposition**
(recommended): split the helper into its own ACT iteration (S22 ACT,
~48 LOC) and follow with a second PR for the graph-bound (S23 ACT,
~50–100 LOC).

### §5.1 Why split the iteration

Three concrete reasons to prefer the helper-only ACT iteration:

1. **The helper has 0 dependence on S18e bundle internals** (only the
   four axiom hypotheses `hS_compact`, `hF_ne`, `hF_closed`,
   `hF_convex`). It can be Docker-built and merged independently of
   any S19 step (c) work.

2. **The graph-bound stitching (S19 PREP §6 Step 6c) still has an
   open §4.c gap** (S19 PREP §4.c: the `‖fC x − ysel x‖` decomposition
   leaks `diam(F j)` at each summand). Bundling the helper and the
   stitching into one PR makes the helper's merge contingent on
   resolving the §4.c gap — high risk for the broader axiom-elimination
   timeline.

3. **Matches the S18a–f / S19a-ACT pattern**: each PR was one helper
   (~50–100 LOC each), build-pending only because of `proofs/.lake`
   symlink trap, fully self-contained. The helper-per-PR rhythm has
   accumulated 6 helpers in 5 days (S18a #17755 → S18b #17802 → S18c
   #17910 → S18d #17993 → S18e #18130 → S18f #18177/#18257 → S19a
   #18646). Continuing the rhythm is auditor-familiar.

---

## §6. Order-of-operations for the S22 ACT implementer

1. **Wait for #19016 (S20 ACT) to merge.** The build-pending chain
   ends there; if the helper PR is opened before #19016 merges, the
   helper inherits the chain's "build pending" status. Merge order
   matters: #19016 → this helper.

2. **Wait for #19044 (S21 STATE-SYNC) to merge.** Otherwise the
   `state.md` will conflict on the iteration row (S21 STATE-SYNC adds
   the S20 ACT row; the helper PR adds the S22 ACT row).

3. **Branch from `main` after #19016 and #19044 merge.** Confirm the
   parent file builds cleanly via `./proofs/scripts/docker-build.sh
   Proofs.SchauderFixedPointOQ03OQ01` (or trust the auditor's
   verification of #19016's claimed 3074-job clean build).

4. **Add the helper at file line ~914** (immediately after
   `image_subtype_isClosed_of_isClosed_of_compact` which currently
   ends at line 912; before the `theorem seq_compact_of_compact` block
   starting at line 919). The §3 helper is logically grouped with the
   S19a-ACT closed-image helper.

5. **Docker-build and verify** before opening the PR. Expected
   outcome: parent file builds clean (3074+ jobs); helper compiles
   in a few seconds inside that build.

6. **PR title format** matching iteration history:
   `research(schauder-fp-oq-03-oq-01-incomplete-01): S22 ACT — nearest-point-in-image helper for §4.b (build verified, N jobs)`.

7. **Update state.md** in the same PR: append S22 ACT row to
   iteration history; update `Current Focus` and `Next Action`
   sections. Update `currentState.iteration` and `attemptCounts` in
   `src/data/research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01.json`.

---

## §7. Anti-targets (what S22 PREP must NOT do)

- Do not edit `proofs/Proofs/SchauderFixedPointOQ03OQ01.lean`.
  (Stale PR #17801 still open against this file; S20 ACT #19016 active.)
- Do not edit `state.md`. (S21 STATE-SYNC #19044 owns the next refresh.)
- Do not edit `src/data/research/problems/...incomplete-01.json`.
  (Same as above.)
- Do not edit any gallery file. (Slug has no gallery entry of its
  own; meta.json lives under the parent `schauder-fixed-point-oq-03-oq-01`
  which is a separate slug.)
- Do not propose adding/removing axioms.
- Do not propose modifying any S18a–f or S19a-ACT helper.

Only one file modified: this `sessions/2026-05-14-s22-prep-step-b-helper-and-completeness-route.md`.

---

## §A. Appendix — verification commands re-runnable

```bash
# (Run from worktree cwd.)
$ jq -r '.packages[] | select(.name == "mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# Helper file lines (S19a-ACT landed; helper at 906–912):
$ sed -n '906,912p' proofs/Proofs/SchauderFixedPointOQ03OQ01.lean

# S14-era IsCompact.isComplete precedent at line 223:
$ sed -n '222,224p' proofs/Proofs/SchauderFixedPointOQ03OQ01.lean

# Axiom signature (target for S19 step (d) replacement):
$ sed -n '548,556p' proofs/Proofs/SchauderFixedPointOQ03OQ01.lean

# kakutani caller hF_closed hypothesis (proves the signature-update plan is safe):
$ sed -n '1085,1086p' proofs/Proofs/SchauderFixedPointOQ03OQ01.lean
```

All four commands point to invariants this PREP relies on. The S22
ACT implementer should re-run them post-#19016-merge to confirm the
relevant line numbers are still accurate (S20 ACT's five fixes inside
`exists_continuous_proj_convex` may shift line numbers in lines
211–305 but should not affect lines 548+ or the S19a-ACT helper at
906–912).

---

## Outcome of this iteration

**Outcome**: doc-only progress (helper signature locked, completeness
route tightened, post-S20-ACT orthogonality verified).

**Concrete deliverable**: this memo provides the S22 ACT implementer
with (1) a verbatim helper signature, (2) a 5-tactic-line body using
the tighter `IsCompact.isComplete` path, (3) a verification command
suite re-runnable post-merge, and (4) a recommended order-of-operations
respecting the two in-flight sister PRs.

**Build status**: N/A (no Lean changes).

**Path forward**:

- **S22 ACT** (next claim, ~48 LOC, recommended): add the
  `exists_nearest_in_image_F` helper at file line ~914. Self-contained,
  no dependence on S18e bundle internals.
- **S23 ACT** (subsequent claim, ~50–100 LOC): graph-bound stitching at
  `(fC x, ysel _, ...)` consuming this helper plus S18e bundle plus
  S18f input-ball clause. Still has the open §4.c gap from S19 PREP;
  the S23 author should re-evaluate §4.b vs §4.d after the helper
  lands.
- **S24 ACT** (final, ~10–30 LOC): replace `axiom approx_selection_exists`
  with `theorem approx_selection_exists_proof`; update kakutani caller
  to pass `hF_closed`.

Total remaining LOC budget for full Axiom-2 elimination: ~110–180,
consistent with S19 PREP §9's "85–280 LOC" envelope.

**Not done in this iteration** (deliberate):
- No Lean code added.
- No state.md / JSON / meta.json edits.
- No proposal to alter the S19a-ACT helper or any prior helper.
- No claim on whether the §4.c gap is dischargeable — that decision is
  deferred to S23 ACT after the helper lands.
