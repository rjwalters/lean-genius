# Session 2026-05-12 S1 OBSERVE — Mathlib has the chain-complex machinery but no Tucker/Borsuk-Ulam; CellComplex needs a `sign` field

**Mode**: FRESH (S1 OBSERVE, doc-only)
**Researcher**: researcher-3
**Outcome**: scouted — Mathlib has the abstract chain-complex /
`AlternatingFaceMapComplex` framework (Joël Riou et al., 2021) but
does **not** have Tucker's lemma or Borsuk-Ulam formalized. The
parent's `CellComplex` is unsigned (adjacency only, no orientation);
extending it to signed cell complexes is a genuinely new gallery
contribution. Three S2 targets identified.

## 1. The slug, taken literally

`sperner-ndim-mathlib-oq-01` (parent, multiple Lean files: 377 LOC
`SpernerNDimMathlibOQ01.lean` + 600+ LOC supporting infrastructure)
is "Concrete CellComplex Instances for Sperner's Lemma: The
Freudenthal Bridge". Its `src/data/proofs/sperner-ndim-mathlib-oq-01/meta.json`
lists six open questions. The fourth — extracted as the slug
`sperner-ndim-mathlib-oq-01-oq-04` on 2026-05-12 — reads:

> "Generalize the `CellComplex` framework to **signed cell complexes**
> (orientations on $d$-cells), enabling formalization of **Tucker's
> lemma** and the **Borsuk–Ulam theorem** as sibling Sperner-style
> parity arguments."

Notes: `"AVAILABLE — added by seeker 2026-05-12"`, tier B,
significance 6, tractability 6, tags `combinatorics` + `topology` +
`sperner` + `abstract-cell-complex`.

The literal mathematical content: lift the parent's *unsigned*
`CellComplex V d` structure to a *signed* version where each cell
carries an orientation, enabling Z/2-parity arguments for Tucker
(antipodal Z/2 colorings on the boundary) and Borsuk–Ulam
(continuous antipodal maps `S^n → ℝ^n` hit zero on antipodal pairs).

## 2. What the parent file's `CellComplex` looks like (unsigned)

`proofs/Proofs/SpernerNDimMathlib.lean` (lines 52–66):

```lean
namespace SpernerAbstract

/-- An abstract cell complex with adjacency. Each cell has `d + 1`
    vertices from type `V`. Interior facets pair up via `adj`; boundary
    facets have `adj = none`. -/
structure CellComplex (V : Type*) [DecidableEq V] (d : ℕ) where
  Simplex : Type
  simplex_decidableEq : DecidableEq Simplex
  simplex_fintype : Fintype Simplex
  vertices : Simplex → Fin (d + 1) → V
  vertices_injective : ∀ s, Function.Injective (vertices s)
  adj : Simplex → Fin (d + 1) → Option (Simplex × Fin (d + 1))
  adj_symm : ∀ s k s' k', adj s k = some (s', k') → adj s' k' = some (s, k)
  adj_vertices : ∀ s k s' k', adj s k = some (s', k') →
    (Finset.univ.erase k).image (vertices s) =
    (Finset.univ.erase k').image (vertices s')
  adj_ne : ∀ s k s' k', adj s k = some (s', k') → s ≠ s'

end SpernerAbstract
```

The crucial observation: `adj` is **unsigned**. The facet pairing
`(s, k) ↔ (s', k')` carries no `±1` (or `ZMod 2`) information. This
is sufficient for Sperner's lemma — the Z/2-parity argument in
`even_card_fpf_invol` (line 101) only uses adjacency cardinality,
not orientation.

But Tucker's lemma and Borsuk–Ulam both require the **signed**
pairing: the boundary operator `∂ : C_n → C_{n-1}` of the chain
complex is *alternating* (signs `(-1)^k` on the k-th face), and the
Tucker antipodal hypothesis kills these signed sums in pairs of
opposite orientation.

## 3. Mathlib coverage

### What Mathlib HAS

#### Abstract chain-complex framework (full coverage)

`Mathlib.AlgebraicTopology.AlternatingFaceMapComplex` (Joël Riou,
Adam Topaz, Johan Commelin, 2021):

```lean
/-- We construct the alternating face map complex, as a functor
    `alternatingFaceMapComplex : SimplicialObject C ⥤ ChainComplex C ℕ`
    for any preadditive category `C`. -/
```

In English: for any simplicial object `X : SimplicialObject C` in a
preadditive category, the alternating face-map complex
`... → X_2 → X_1 → X_0` exists, with differentials being the
alternating sums of face maps. This is the *categorical* version of
the signed cell complex.

Supporting infrastructure:
- `Mathlib.AlgebraicTopology.SimplexCategory` — the simplex category Δ
- `Mathlib.AlgebraicTopology.SimplicialObject` — simplicial objects in any category
- `Mathlib.AlgebraicTopology.SimplicialSet.*` — when C = Type
- `Mathlib.AlgebraicTopology.MooreComplex` — normalized Moore complex
- `Mathlib.AlgebraicTopology.DoldKan.*` — Dold–Kan correspondence

This is full categorical-level coverage of "signed simplicial complex"
in the topos sense.

#### Geometric simplicial complex

`Mathlib.Analysis.Convex.SimplicialComplex.Basic`: the affine-space
version, with vertices as points in a real vector space and faces as
convex hulls. Does NOT carry orientation information directly.

### What Mathlib does NOT have

- **Tucker's lemma** — search `Mathlib` for `"Tucker"` returns 0 hits
  in topology / combinatorics paths. Not formalized.
- **Borsuk–Ulam theorem** — search `Mathlib` for `"BorsukUlam"` or
  `"borsuk_ulam"` returns 0 hits. Mentioned in
  `Mathlib.Topology.Homotopy.LocallyContractible` only as a comment
  pointer, not as a theorem.
- **Antipodal Z/2 actions on cell complexes** — no formalized
  framework. Mathlib has `MulAction` of `ZMod 2`, but not glued to
  `SimplicialComplex` / `CellComplex`-style structures.
- **Signed `CellComplex`-style finite-combinatorial framework** —
  Mathlib's signed structures are *categorical* (chain complex in a
  preadditive category), not the combinatorial "label `Fin (d+1)`
  faces with `±1` and demand coherence on shared facets" structure
  that Tucker / Borsuk–Ulam typically use.

### The semantic gap

Mathlib's `AlternatingFaceMapComplex` is the *correct* categorical
framework — every signed cell complex *should* embed into it — but
the parent's `CellComplex` is purposefully *combinatorial* (finite,
decidable, computable) for finitary Sperner-style parity proofs. The
gap is:

> *Mathlib has the categorical signed-chain-complex framework.*
> *Mathlib does not have a finite-combinatorial signed cell complex.*

So the S2 ACT target is genuinely new content: a finite-combinatorial
`SignedCellComplex` structure that *induces* a chain complex in
Mathlib's `AlternatingFaceMapComplex` framework (the bridge is via
`ZMod 2`-valued sign).

## 4. Three narrow S2 targets (in order of recommended priority)

### S2-A (RECOMMENDED). Signed `CellComplex` definition + Z/2-coherence (~120–180 LOC, 2–3 sorries → 0)

Create `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` containing:

```lean
import Proofs.SpernerNDimMathlib
import Mathlib.Data.ZMod.Basic

namespace SpernerAbstract.Signed

variable {V : Type*} [DecidableEq V] {d : ℕ}

/-- A *signed* cell complex: an unsigned `CellComplex` together with
    a `ZMod 2`-valued sign on each face index, satisfying the
    coherence condition that adjacent facets have *opposite* signs. -/
structure SignedCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends CellComplex V d where
  sign : Simplex → Fin (d + 1) → ZMod 2
  /-- Adjacent facets carry opposite signs (Z/2-orientation coherence). -/
  sign_adj : ∀ s k s' k', adj s k = some (s', k') →
    sign s k + sign s' k' = 1
  /-- Standard alternating-sign on the unsigned default: sign s k = k. -/
  -- Allow user to override; default = (fun _ k => k.val % 2 : ZMod 2)
  sign_default_compat : ∀ s k, sign s k = (k.val % 2 : ZMod 2) ∨
    ∃ σ : Equiv.Perm (Fin (d + 1)), sign s k = (σ k).val % 2

/-- The *signed* counterpart of `IsFC`: a fully-colored simplex
    additionally carries the sum of vertex-signs as a ZMod 2 label. -/
def signedFC (c : V → Fin (d + 1)) (K : SignedCellComplex V d) (s : K.Simplex) : ZMod 2 :=
  ∑ k, K.sign s k

/-- **Signed boundary count parity**: in a signed cell complex with
    Z/2-coherent boundary signs, the parity of "signed doors on the
    boundary" determines the parity of "fully-colored signed cells". -/
theorem signed_door_count_parity (c : V → Fin (d + 1)) (K : SignedCellComplex V d) :
    (∑ s, signedFC c K s) = (∑ s, ∑ k, if isDoorAt c K.toCellComplex s k then K.sign s k else 0) := by
  sorry

end SpernerAbstract.Signed
```

**Value**: Gives the bare structural definition + the one parity
theorem that makes signed cell complexes useful (the analog of the
parent's `even_card_fpf_invol`, but with sign-tracking). Closes one
sorry via the existing `even_card_fpf_invol` framework, with sign
arithmetic done in `ZMod 2`.

**Risk**: ~150 LOC; 1 sorry (the signed-parity theorem) closes via
the parent's pairing infrastructure + `Finset.sum_involution` on the
adjacency map weighted by sign. The `sign_default_compat` field is
redundant for triangle case; can be removed in a refinement.

### S2-B. Bridge to Mathlib's `AlternatingFaceMapComplex` (~50–80 LOC, 2 sorries → 0)

Show that a `SignedCellComplex V d` (with finite `Simplex` type)
induces a chain complex of `(ZMod 2)`-modules via Mathlib's
`AlternatingFaceMapComplex` framework, with the differential
matching the signed-adjacency operator.

**Strategy**: Define the simplicial object `X : SimplicialObject (ModuleCat (ZMod 2))`
with `X_k := Free (ZMod 2)` on the set of `k`-simplices, and the
face maps matching the parent's `vertices ∘ Fin.castSucc`. The
alternating-sign on faces is `sign_adj`-coherent.

**Value**: Bridges the *combinatorial* signed structure to Mathlib's
*categorical* chain-complex API. After this bridge, downstream
theorems about chain-complex homology apply directly. This is the
honest "Mathlib integration" angle.

**Risk**: ~80 LOC; 2 sorries; categorical-style proof requires
careful naming of the simplicial structure maps. Probably needs a
small `open scoped CategoryTheory SimplicialObject` block.

### S2-C. Tucker's-lemma scaffold (~80–120 LOC, ALL sorries — pure scaffold)

State Tucker's lemma over a signed cell complex without proving
it; identify the supporting lemmas and sub-sorries that would be
needed for a full proof.

```lean
/-- **Tucker's lemma** (statement only): for an antipodally symmetric
    triangulation of `S^n` and an antipodal Z/2 labeling `λ : V → Fin (2n+1)`
    with `λ(-v) = -λ(v)`, some adjacent pair `(v, w)` satisfies
    `λ(v) = -λ(w)`. -/
theorem tucker_statement (K : SignedCellComplex V n)
    (h_antipodal : ∃ ι : V → V, Function.Involutive ι ∧ …)
    (λ : V → Fin (2*n + 1))
    (h_antipodal_label : ∀ v, λ (ι v) = -λ v) :
    ∃ s k s' k', K.adj s k = some (s', k') ∧
      λ (K.vertices s ⟨k, ?_⟩) = -λ (K.vertices s' ⟨k', ?_⟩) := by
  sorry  -- full proof outside scope; ~600 LOC estimate

/-- Borsuk-Ulam as a corollary (statement only). -/
theorem borsuk_ulam_statement_via_tucker (f : C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))
    (hf : ∀ x, f (-x) = -f x) :
    ∃ x, f x = 0 := by
  sorry  -- via Tucker + density argument
```

**Value**: Articulates the downstream theorems whose formalization
S2-A and S2-B enable. Useful as a *roadmap* document for future
research; even if all proofs are sorry'd, the *statement* clarifies
what the framework is for.

**Risk**: 2 sorries (both statement-only). Should be tagged
`status: "scaffold"`, not `"verified"`, in any gallery entry.

## 5. Anti-targets

The following should NOT be S2 targets:

- **Re-implementing Mathlib's `AlternatingFaceMapComplex`** in a
  Sperner-specific form: it would duplicate Joël Riou's work
  unnecessarily. Use the bridge in S2-B instead.
- **Full Tucker's lemma proof**: the proof in
  Matoušek's *Using the Borsuk-Ulam Theorem* (Theorem 2.3.1)
  is ~600 LOC of careful induction; out of scope for an S2 ACT
  session. Defer to a multi-session S3+ chain after S2-A and S2-B
  ship.
- **Geometric Borsuk-Ulam directly (without Tucker)**: this is a
  topology-heavy proof using degree theory or homology; out of scope
  for the combinatorial-Sperner-style angle of this slug.

## 6. Race / saturation context

Pre-claim probe at 2026-05-12 23:18 UTC:

```
sperner-ndim-mathlib-oq-01-oq-04   open_PRs=0   remote_branches=0   recent_merges=0
```

Genuinely pristine. The parent `sperner-ndim-mathlib-oq-01` itself has
no open PRs and was last touched 2026-05-07 (PR #16663, enrichment).

Among the tier-B pristine candidates at probe time, this slug was
chosen because:
- Mathlib has *substantial* upstream coverage (chain-complex framework)
  to bridge to;
- The "what's missing" gap is well-defined (finite-combinatorial
  signed structure);
- Tucker / Borsuk-Ulam are concrete downstream theorems giving the
  S2 work clear motivation.

researcher-3 prior session PRs: #18316 (`euler-totient-oq-04-oq-01`),
#18320 (`cevas-theorem-oq-04-oq-01`) — both S1 OBSERVE doc-only with
the same Mathlib-duplicate-detection / missing-bridge framing.

## 7. Honesty assessment

The slug literally asks for "signed cell complexes enabling Tucker
and Borsuk-Ulam". The honest framing is:

1. **Mathlib has the categorical framework** (`AlternatingFaceMapComplex`).
2. **Mathlib does not have Tucker or Borsuk-Ulam formalized.**
3. **The parent's `CellComplex` is unsigned** — extending it is the
   genuinely new structural contribution.
4. **A full S2 ACT shipping just S2-A (the signed structure)** is
   honest as "structural definition + Z/2-coherence parity theorem".
   It is NOT "Tucker's lemma proved" or "Borsuk-Ulam proved" — those
   are downstream consequences requiring further work.

The S2 ACT meta.json should explicitly state:
- `contribution`: "Signed cell-complex structure extending the
  parent's unsigned `CellComplex` with `ZMod 2`-valued sign +
  Z/2-coherence parity theorem"
- `dependencies`: ["Proofs.SpernerNDimMathlib"]
- `relatedMathlib`: ["Mathlib.AlgebraicTopology.AlternatingFaceMapComplex"]
  with note "categorical-level signed-chain-complex framework, related but
  distinct"
- `status`: "verified" (after S2-A closes its sorries)
- **NOT** claim Tucker's lemma or Borsuk-Ulam unless they are
  actually proved.

## 8. No edits to parent state

This session creates exactly one new file:

```
research/problems/sperner-ndim-mathlib-oq-01-oq-04/sessions/2026-05-12-s01-observe-signed-cellcomplex-tucker-borsukulam.md
```

No edits to `proofs/Proofs/SpernerNDimMathlib.lean`,
`proofs/Proofs/SpernerNDimMathlibOQ01.lean`,
`src/data/proofs/sperner-ndim-mathlib-oq-01/meta.json`, any
`research/problems/sperner-ndim-mathlib-oq-01/*.md`, or any
sibling gallery entries.

PR is merge-conflict-free against any parallel claim or future S2 ACT.

---

**Time-budget**: claim → push targeted at ≤ 25 min (per researcher-3
tier-B / orphan-fresh fallback patterns).

**Sorry / axiom delta**: 0 / 0 (doc-only).

**Next-session recommendation**: open S2-A
(`SpernerNDimMathlibOQ01OQ04.lean`, `SignedCellComplex` + `signedFC`
+ `signed_door_count_parity`, ~150 LOC, 1 closable sorry). S2-B
(Mathlib bridge) and S2-C (Tucker / Borsuk-Ulam scaffolds) are
natural follow-up sessions, NOT to be bundled into S2-A.
