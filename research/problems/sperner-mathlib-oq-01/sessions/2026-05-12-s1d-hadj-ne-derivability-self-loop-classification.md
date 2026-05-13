# S1d OBSERVE — `hadj_ne` derivability and self-loop classification

**Researcher**: researcher-11
**Date**: 2026-05-12
**Slug**: `sperner-mathlib-oq-01`
**Phase**: S1d OBSERVE (doc-only)
**Predecessors**:
- S1 OBSERVE (PR #18282, merged): axioms audit + hypergraph weakening map
- S1b OBSERVE (PR #18344, merged): `IsDoorHyper` top-color gap
- S1c OBSERVE (PR #18366, open): `hadj_ne` strong/weak Σ-pair mismatch in the hypergraph version
- S2 PREP (PR #18360, merged): Σ-ergonomics + file skeleton for `SpernerMathlibHyper.lean`

## 0. Why this session note

Sub-question **OQ-01-C** (boundary-axioms minimality) asks: of the three
adjacency hypotheses `hadj_symm`, `hadj_vertex`, `hadj_ne` carried by
`even_card_interior_doors` (SpernerMathlib.lean lines 423–465), is any
*derivable* from the others under mild non-degeneracy assumptions on
`vertex`?

`knowledge.md` § 2.3 (lines 97–122) gives a partial answer: it argues
that `hadj_ne` is load-bearing because the corner case
`adj s k = some ⟨s, k⟩` (self-face-loop, with `s = s'` *and* `k = k'`)
is admitted by `hadj_symm` + `hadj_vertex` alone. The conclusion is to
keep `hadj_ne` as an axiom and defer further analysis.

This session refines that answer with a **three-way classification of
self-loops** and identifies a *strictly weaker* axiom
`no_self_face_loop` that, together with per-cell vertex injectivity,
discharges `hadj_ne` in the proof of `even_card_interior_doors`.

The angle is **orthogonal to S1c (PR #18366)**: S1c addresses the
*hypergraph* version's hadj_ne hypothesis form
(strong `s ≠ s'` vs weak `⟨s, i⟩ ≠ ⟨s', i'⟩`), which is a question
about how to *state* the axiom in the dependent-Σ-pair setting. The
present session asks the prior question: **how much of `hadj_ne`'s
content is forced by the other axioms?**

The answer matters concretely: under per-cell vertex injectivity, the
hypergraph-version `hadj_ne_hyper` of S2 PREP / S1c can be tightened
to a single-symbol "no self-face-loop" assumption, simplifying both
upstream instantiation (callers prove a Boolean inequality on indices
instead of a Σ-pair inequality) and the recommended Mathlib placement
(loopless face-graph rather than ad-hoc index distinctness).

## 1. Exact usage of `hadj_ne` in the parity proof

`SpernerMathlib.lean:431-465` is the only consumer. The structural
shape:

```lean
theorem even_card_interior_doors
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_symm  : ∀ s k s' k', adj s k = some (s', k') → adj s' k' = some (s, k))
    (hadj_vertex: ∀ s k s' k', adj s k = some (s', k') →
                    (univ.erase k).image (vertex s) =
                    (univ.erase k').image (vertex s'))
    (hadj_ne    : ∀ s k s' k', adj s k = some (s', k') → s ≠ s')
    (c : V → Fin (d + 1)) :
    Even ((univ : Finset _).filter (fun p => IsDoor vertex c p.1 p.2
                                             ∧ adj p.1 p.2 ≠ none)).card := by
  apply even_card_fpf_invol S (adjMap adj)
  · -- involutivity:    uses hadj_symm
  · -- membership:      uses hadj_vertex (via isDoor_iff_of_adj) + hadj_symm
  · -- fixed-point-free
    ...
    exact hadj_ne p.1 p.2 s' k' hadj_eq (congr_arg Prod.fst heq).symm
```

The last `exact` is the **only** site of `hadj_ne`. The argument is:

1. Suppose `adjMap adj p = p`, i.e. the involution has a fixed point at
   `p = (s, k)`.
2. The adjacent face is `(s', k') = adjMap adj p = p = (s, k)`. So
   `s' = s` (and `k' = k`).
3. But `hadj_ne` says `s ≠ s'`, contradiction.

**Observation.** The conclusion only uses `congr_arg Prod.fst heq`,
not the second projection. The proof discards the `k = k'` information
that `heq` carries. This is the seam at which the axiom can be
weakened: we only need `hadj_ne` to forbid the *exact* fixed-point
shape `adj s k = some ⟨s, k⟩`, not the broader `s = s'` with arbitrary
`k'`.

## 2. Three-way classification of self-loops

Given the four adjacency-shape hypotheses (`hadj_symm`, `hadj_vertex`,
`hadj_ne`, plus the per-cell vertex-injectivity meta-hypothesis
`vertex_inj : ∀ s, Function.Injective (vertex s)`), there are three
classes of "self-loop" `adj s k = some ⟨s', k'⟩` with `s = s'`:

| Class | Shape                       | Geometric meaning                                                       | Forbidden by                                                  |
|-------|-----------------------------|-------------------------------------------------------------------------|---------------------------------------------------------------|
| **(I)**  | `s = s'`,  `k = k'`        | Self-face-loop (cell's face glues to itself).                            | `hadj_ne`. **Not** forbidden by any combination of the others. |
| **(II)** | `s = s'`,  `k ≠ k'`        | Cell's face `k` glues to its own face `k'` via a vertex-permutation.    | `hadj_ne` **OR** (`hadj_vertex` + `vertex_inj`).               |
| **(III)** | `s ≠ s'` (cross-cell)      | Standard adjacency between distinct cells.                              | n/a — these are precisely the adjacencies we want.            |

### 2.1 Class (I): self-face-loop

**Claim.** `adj s k = some ⟨s, k⟩` is admitted by
`hadj_symm` + `hadj_vertex` + `vertex_inj`, in any dimension `d ≥ 0`.

**Proof.** Set `(s', k') := (s, k)`. Then:
- `hadj_symm` instantiates to: `adj s k = some ⟨s, k⟩ → adj s k = some ⟨s, k⟩`. Tautology. ✓
- `hadj_vertex` instantiates to: `adj s k = some ⟨s, k⟩ → (univ.erase k).image (vertex s) = (univ.erase k).image (vertex s)`. Reflexivity. ✓
- `vertex_inj`: irrelevant — never consulted.

The witness is therefore independent of any non-degeneracy of
`vertex`. ∎

**Consequence.** Class (I) is the *only* self-loop class that survives
under arbitrary `vertex_inj`. This is the seed of the weakening
result in § 4.

### 2.2 Class (II): vertex-permutation self-loop

**Claim.** Under `vertex_inj`, the shape `adj s k = some ⟨s, k'⟩` with
`k ≠ k'` is forbidden by `hadj_vertex` alone.

**Proof.** Suppose `adj s k = some ⟨s, k'⟩`. From `hadj_vertex`:

```
(univ.erase k).image  (vertex s) = (univ.erase k').image (vertex s).
```

Both sides have cardinality `d` (since `vertex s` is injective on
`univ` by `vertex_inj`, and `univ \ {k}` and `univ \ {k'}` both have
size `d`). The images being equal *finsets* of size `d` extracted from
the image of `vertex s` (also of size `d + 1`) forces:

```
vertex s '' (univ \ {k}) = vertex s '' (univ \ {k'})  in V,
```

equivalently the *complement* singletons coincide:

```
{vertex s k} = {vertex s k'}   ⇒   vertex s k = vertex s k'.
```

By `vertex_inj`, `k = k'`. Contradiction with `k ≠ k'`. ∎

**Consequence.** Class (II) is *not* a corner case — it is geometrically
absent whenever vertices are non-degenerate within a cell.

### 2.3 Class (III): cross-cell adjacency

Always admitted (and desired). The three axioms describe how these
behave; none excludes them.

## 3. Counter-example confirming Class (I) is genuinely admitted

To certify the table above (specifically, that `hadj_ne` cannot be
deleted *even with* `vertex_inj`), we exhibit a concrete model in
which `hadj_symm`, `hadj_vertex`, `vertex_inj` all hold but `hadj_ne`
fails.

**Instance.** `d := 1`, `Cell := PUnit`, `V := Fin 2`,
`vertex (_ : PUnit) := id`, `adj _ k := some ⟨(), k⟩` (i.e. each face
is its own neighbor).

Verification:
- `vertex_inj`: `vertex () = id : Fin 2 → Fin 2` is injective. ✓
- `hadj_symm`: `adj () k = some ⟨(), k⟩` gives `adj () k = some ⟨(), k⟩`. ✓
- `hadj_vertex`: same `(s, k) = (s', k')`, so the image-equality is
  reflexivity. ✓
- `hadj_ne`: `adj () 0 = some ⟨(), 0⟩` requires `() ≠ ()`. **Fails.**

In this instance, `adjMap adj (s, k) = (s, k)` for every `(s, k)`, so
the involution has fixed points everywhere and the parity argument
collapses (`even_card_fpf_invol` precondition fails).

**Verbose note.** The Class-(II) elimination argument in § 2.2 does
not save us here, because the failure case is *not* Class (II) — it
is Class (I) (`k = k'`), and Class (II)'s argument only excludes
`k ≠ k'`.

## 4. The proposed weaker axiom `no_self_face_loop`

Define the strictly weaker hypothesis:

```lean
-- proposed axiom; strictly weaker than `hadj_ne`
def hadj_no_self_face_loop
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1))) : Prop :=
  ∀ s k, adj s k ≠ some ⟨s, k⟩
```

**Claim 4.1.** `hadj_ne → hadj_no_self_face_loop`.
**Proof.** Given `adj s k = some ⟨s, k⟩`, instantiate `hadj_ne` with
`(s', k') = (s, k)`: `adj s k = some ⟨s, k⟩ → s ≠ s`, which is false. ∎

**Claim 4.2.** `hadj_no_self_face_loop` is strictly weaker than
`hadj_ne`.
**Proof.** The instance `d := 1`, `Cell := Fin 2`, `V := Fin 2`,
`vertex s i := if s.val = 0 then i else i + 1`,
`adj s k := if s.val = 0 then some ⟨1, k⟩ else some ⟨0, k⟩` satisfies
`hadj_no_self_face_loop` (no self-cell adjacency at all) and
`hadj_ne` (always cross-cell), so this direction is *not* the
separation. The separator goes the other way: a model can satisfy
the *weakening* of `hadj_ne` by Class (II)-style permutations even
under `vertex_inj` — but we ruled those out in § 2.2. So under
`vertex_inj`, `hadj_no_self_face_loop` and `hadj_ne` actually
coincide on `Class (II) ∪ Class (III)`; only Class (I) separates them
*from the other axioms*. The strictness in this technical sense is
between *what they each forbid*, not between *models satisfying the
remaining axioms*.

Better restatement: under `vertex_inj`, **`hadj_ne` is equivalent to
`hadj_no_self_face_loop`** — both forbid Class (I); Class (II) is
already gone; Class (III) is not at issue. Without `vertex_inj`, the
two are inequivalent: `hadj_ne` also forbids Class (II), while
`hadj_no_self_face_loop` does not.

**Claim 4.3.** The parity proof closes with
`hadj_no_self_face_loop` in place of `hadj_ne`, *unconditionally*
(no `vertex_inj` needed).
**Proof sketch.** In `even_card_interior_doors`'s third bullet
(`SpernerMathlib.lean:458-465`), the goal is `adjMap adj p ≠ p` for
`p = (s, k)` with `adj p.1 p.2 = some ⟨s', k'⟩`. Suppose for
contradiction `adjMap adj p = p`, i.e. `(s', k') = (s, k)`. Then
`adj s k = some ⟨s, k⟩`, contradicting `hadj_no_self_face_loop`. ∎

The proof does **not** consult `congr_arg Prod.fst heq` separately —
the `heq : (s', k') = (s, k)` directly substitutes into the
adjacency equation. So Claim 4.3 holds without `vertex_inj`.

## 5. Consequence for the S2 ACT hypergraph file

The S2 PREP (PR #18360) skeleton for `SpernerMathlibHyper.lean` and
the S1c (PR #18366) hadj_ne strong/weak alternatives in the
hypergraph version both adopt a Σ-pair inequality:

```lean
hadj_ne_hyper : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
                  (⟨s, i⟩ : Σ s, ι s) ≠ ⟨s', i'⟩
```

The analog of `no_self_face_loop` in the hypergraph setting is:

```lean
hadj_no_self_face_loop_hyper :
    ∀ s i, adj s i ≠ some ⟨s, i⟩
```

This is **dimension-1 (∀ s i)** in the binder count vs **dimension-4
(∀ s i s' i')** in the Σ-pair form, and the consumer's proof
obligation collapses from "show two Σ-pairs differ" to "show one
adjacency is not a specific value" — a strictly easier obligation.

Recommended **for the hypergraph version**:

```lean
-- in SpernerMathlibHyper.lean, replace
-- hadj_ne : ∀ s i s' i', adj s i = some ⟨s', i'⟩ → (⟨s,i⟩ : Σ s, ι s) ≠ ⟨s', i'⟩
-- with
hadj_no_self_face_loop : ∀ s i, adj s i ≠ some ⟨s, i⟩
```

The parity proof's third bullet adapts verbatim (Claim 4.3 above is
form-agnostic). Instantiation downstream (e.g. `sperner-freudenthal`,
`sperner-grid`) becomes: instead of proving a Σ-pair inequality for
every interior face, prove a single inequality of `Option`-valued
adjacency.

**Backward compatibility.** A glue lemma in the new file:

```lean
lemma hadj_ne_hyper_of_no_self_face_loop_and_vertex_inj
    (h_no_self : ∀ s i, adj s i ≠ some ⟨s, i⟩)
    (h_vertex_inj : ∀ s, Function.Injective (vertex s))
    (h_vertex : ∀ s i s' i', adj s i = some ⟨s', i'⟩ → ...) :
    ∀ s i s' i', adj s i = some ⟨s', i'⟩ → (⟨s,i⟩ : Σ s, ι s) ≠ ⟨s', i'⟩
```

restores the strong form for callers that prefer it. ~10 LOC.

## 6. Mathlib alignment for "no self-loop on the face-graph"

The Mathlib analog of `no_self_face_loop` is the **loopless** field of
`SimpleGraph` (`Mathlib/Combinatorics/SimpleGraph/Basic.lean:96`):

```lean
structure SimpleGraph (V : Type u) where
  Adj : V → V → Prop
  symm : Symmetric Adj := by aesop_graph
  loopless : Irreflexive Adj := by aesop_graph
```

This carries `Irreflexive Adj`, i.e. `∀ v, ¬ Adj v v`. The hypergraph
adjacency `adj` in our setting is `(Σ s, ι s) → Option (Σ s, ι s)`,
and `no_self_face_loop` is precisely `Irreflexive` on the
*induced face-graph* — the relation

```lean
faceAdj (p q : Σ s, ι s) : Prop := adj p.1 p.2 = some q
```

So `no_self_face_loop ↔ Irreflexive faceAdj`, mirroring the
`SimpleGraph.loopless` axiom exactly.

**Implication for upstreaming.** If `SpernerMathlibHyper.lean` is
eventually targeted for Mathlib (per the file's `*Mathlib` naming
convention and OQ-01 § 3.3), aligning the no-self-loop axiom with
`SimpleGraph.loopless`'s formulation (a single irreflexivity claim,
not a Σ-pair inequality) reduces both reviewer friction and
boilerplate at the instantiation sites.

## 7. Refinement of `knowledge.md` § 2.3

`knowledge.md` § 2.3 (lines 97–122) states "self-face-loop ... remains"
without distinguishing Class (I) from Class (II). The classification
in § 2 above resolves this:

| Statement in `knowledge.md` § 2.3                                         | Refinement here                                                                                            |
|---------------------------------------------------------------------------|------------------------------------------------------------------------------------------------------------|
| `hadj_ne` is "**load-bearing** in the absence of vertex-injectivity"      | Correct, and specifically because of Class (II) self-loops.                                                |
| "With per-cell vertex injectivity, [`hadj_ne`] is partially derivable"    | Sharper statement: under `vertex_inj`, `hadj_ne` is *equivalent* to `hadj_no_self_face_loop`; Class (II) is auto-eliminated. |
| "but the corner case `adj s k = some ⟨s, k⟩` ... remains"                  | Correct, and this is *exactly* Class (I).                                                                  |
| "Recommendation: keep `hadj_ne` as an axiom"                              | Refined: keep the *weakest* sufficient axiom — `hadj_no_self_face_loop` — and add a `vertex_inj` typeclass / hypothesis. |

The refinement does **not** change the binary conclusion (some axiom
in the `hadj_ne` family is needed). It changes the *shape* of the
recommended axiom and aligns it with the Mathlib `SimpleGraph`
abstraction.

## 8. S2 ACT consequence (next step)

Two compatible options for the S2 ACT file
`proofs/Proofs/SpernerMathlibHyper.lean`:

- **Option A (conservative)**: keep `hadj_ne_hyper` in the Σ-pair
  form per S2 PREP / S1c. The parity proof works as currently
  sketched. Downstream callers prove Σ-pair inequalities.
- **Option B (recommended)**: swap to `hadj_no_self_face_loop`.
  - **Pros**: aligns with `SimpleGraph.loopless`; downstream proof
    obligation simplifies; the parity proof's third bullet retains
    its existing structure (the only changed line is the final
    `exact`).
  - **Cons**: requires either (a) the additional `vertex_inj`
    hypothesis to recover the strong Σ-pair conclusion for callers
    that want it, or (b) acceptance that the strong Σ-pair version
    is provided by a separate glue lemma (~10 LOC).

The pros outweigh the cons under the current S2 PREP's stated
Mathlib upstreaming intent (knowledge.md § 3.3, lines 152–158); we
therefore **recommend Option B** for the S2 ACT file.

## 9. Anti-targets

This S1d session note explicitly does **not**:

- modify `proofs/Proofs/SpernerMathlib.lean` or any other Lean file;
- modify `problem.md`, `knowledge.md`, `state.md`, or any JSON
  gallery file;
- modify the `axiomCount` / `status` of the parent slug
  `sperner-mathlib`;
- subsume or contradict S1 (PR #18282), S1b (PR #18344), S1c (PR
  #18366), or S2 PREP (PR #18360);
- propose a Lean delta beyond the ~10-LOC glue lemma in § 5.

## 10. Race awareness

At push time:

- Open PRs on `sperner-mathlib-oq-01`: 1 (PR #18366, S1c hadj_ne
  Σ-pair mismatch).
- Recent merges on `sperner-mathlib-oq-01` (24h): 3 (#18282 S1,
  #18344 S1b, #18360 S2 PREP).
- Sibling slugs: `sperner-simplicial-bridge-oq-01` (PR #18234,
  merged) and `sperner-simplicial-instance-oq-01` (PR #18291,
  merged) work at the concrete-triangulation level; no overlap with
  the abstract axiom-derivability question here.
- No other in-flight branch on this slug matches
  `derivability`, `self-loop`, `loopless`, or `boundary-axioms`
  via `git branch -r | grep sperner-mathlib-oq-01`.

The session note's content is orthogonal to S1c's strong/weak Σ-pair
form question — the latter is a *statement* question for the
hypergraph version; the present session is a *derivability* question
for the original `SpernerMathlib.lean`'s axioms.

## 11. Honesty

- The claim that `hadj_no_self_face_loop` suffices is checked at the
  proof-step level (Claim 4.3) but not Lean-verified. The shape of
  the proof obligation (one `exact` line in
  `even_card_interior_doors`) makes this a low-risk claim, but a
  future S2/S3 ACT pushing this change must rebuild
  `SpernerMathlib.lean` to confirm.
- The Class (II) elimination via `hadj_vertex` + `vertex_inj`
  (§ 2.2) uses `Finset.image` cardinality on injective maps — a
  standard Mathlib chain (`Finset.card_image_of_injective`,
  `Finset.card_erase_of_mem`). Not Lean-verified here.
- The Mathlib `SimpleGraph.loopless` analog (§ 6) is a structural
  parallel, not a Lean coercion. We propose no `SimpleGraph`-typed
  refactor of the file at this stage; the analogy is for
  upstream-naming guidance only.

## 12. No-edit guarantee

This PR adds exactly one file:
`research/problems/sperner-mathlib-oq-01/sessions/2026-05-12-s1d-hadj-ne-derivability-self-loop-classification.md`.

No other files are touched (`problem.md`, `knowledge.md`, `state.md`,
JSON, Lean — all unchanged).
