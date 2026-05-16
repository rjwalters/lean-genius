# S3 PREP — Follow-up design survey for S2-B / S2-C / S2-D (doc-only)

**Researcher**: researcher-6
**Date**: 2026-05-16 (UTC)
**Mode**: Doc-only design-survey PREP. No `.lean` / `meta.json` / `problem.md` / `knowledge.md` / gallery edits. Three files modified:

1. **NEW**: this memo (`research/problems/sperner-ndim-mathlib-oq-01-oq-04/sessions/2026-05-16-s3-prep-followup-design-survey.md`).
2. **REWRITE-HEAD**: `research/problems/sperner-ndim-mathlib-oq-01-oq-04/state.md` — prepend S3 PREP block above the S2-A ACT block; keep slug status COMPLETED (S2-A primary question discharged); refine `Next Action` to point at the recommended S2-C path.
3. **REFRESH**: `src/data/research/problems/sperner-ndim-mathlib-oq-01-oq-04.json` — bump `iteration` 3 → 4, refresh `lastUpdate` + `currentState.focus` + `currentState.nextAction`; **do not** flip `status` (slug remains `completed`; PREP documents follow-up landscape only).

**Predecessors (chronological)**:
- 2026-05-16T04:45Z **S2-A ACT** PR #19454 (researcher-10): `SignedCellComplex` + `signed_interior_doors_sum_zero`, 207 LOC, 0 axioms / 0 sorries, Docker 7744 jobs clean. **MERGED.** Discharges OQ-04.
- 2026-05-15T18:04Z **S2 PREP** PR #19243 (researcher-8): Variant A-ℤ paste-ready skeleton, 7 Mathlib bearers pinned. ZMod-2 vacuity diagnosis. **MERGED.**
- 2026-05-12 **S1 OBSERVE** PR #18325 (researcher-3): initial signed CellComplex sketch (ZMod-2-valued, later diagnosed vacuous). **MERGED.**

**Orthogonality**: this PR is **doc-only**, **status-preserving**. It does NOT:
- edit any `.lean` file (parent or child);
- edit gallery `meta.json` / `index.ts` / `annotations.json`;
- edit `problem.md` / `knowledge.md`;
- create new slugs for S2-B / S2-C / S2-D (those decisions deferred to Seeker / Champion / next-claim agent);
- flip slug `status` from `completed` (the primary OQ-04 question remains discharged; this PREP documents follow-up *landscape* and does not re-open any open question).

---

## §1. Why a packaged design-survey PREP (rather than 3 separate PREPs)

The S2-A ACT (#19454) closed the slug's primary open question (OQ-04: signed CellComplex over ℤ with interior-door cancellation) at 0/0/0 build-verified status. The S2-A session memo and state.md named three follow-up extensions:

| Follow-up | Scope | Est. LOC | Self-contained? |
|---|---|---|---|
| **S2-B** Mathlib bridge | Embed `SignedCellComplex` into Mathlib's `ChainComplex (ModuleCat ℤ) ℕ` (target: relate to `alternatingFaceMapComplex` via `SimplicialObject`) | ~80–150 | No — design space genuinely open (3 framings audited below) |
| **S2-C** Tucker scaffold | Define `AntipodalCellComplex` (vertex involution `ι : V → V`, no fixed points) and state Tucker's lemma over it | ~120 | Yes — direct structural extension; well-defined `Function.Involutive` API |
| **S2-D** Borsuk-Ulam bridge | Topological reduction from antipodal Tucker to continuous Borsuk-Ulam | open | No — requires topological framework; separate slug likely |

Three independent PREPs would (a) inflate process overhead by ≥3× for ~doc-only work, (b) fragment bearer-pin recheck across three files, and (c) miss the shared design constraint (all three live downstream of the same `SignedCellComplex` API surface). A single packaged design-survey PREP is the right granularity: it pins bearers once, surveys the design space coherently, and lets the next-ACT writer pick the most tractable follow-up first (the §8 recommendation: **S2-C**).

This is **not** the standard "fully-discharged-with-Hermit-followups" pattern from `feedback_researcher_postship_pivot_lands_on_fully_discharged_slug_blocked_hermit_followup_ship_packaged_followups_prep`. The follow-ups here are substantive mathematical content (each ~80–150 LOC of new Lean), not 1-line lint sweeps. Closer to a hybrid of the "named substantive next-action" pattern with the "packaged follow-up" framing.

---

## §2. Slug state recap (S2-A discharged; status preserved)

| Metric | Pre-S2-A | Post-S2-A (this PREP's view) |
|---|---|---|
| `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` | (did not exist) | **207 LOC** (one `structure` + 1 `lemma` + 2 `def` + 1 private helper + 1 main `theorem`) |
| Sorries | — | **0** |
| `axiom` declarations | — | **0** |
| Structure-encoded assumptions in `SignedCellComplex` | — | **0** (only field is `sign : Simplex → Fin (d+1) → ℤ` with `sign_pm_one` + `sign_adj` — both *constraints on data*, not hypotheses; per axiom integrity policy, these are *data definitions* whose construction is the user's responsibility, not axioms in the slug's count) |
| Build verify | — | **Docker 7744 jobs clean** (per S2-A session memo; researcher-10) |
| Slug `status` | `formalized`/pre-S2-A | `completed` |
| Slug `phase` | `RESEARCH` | `COMPLETED` |

The S2-A ACT structure (verbatim from `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean`):

```lean
structure SignedCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends CellComplex V d where
  sign : Simplex → Fin (d + 1) → ℤ
  sign_pm_one : ∀ s k, sign s k = 1 ∨ sign s k = -1
  sign_adj : ∀ s k s' k', adj s k = some (s', k') →
    sign s k + sign s' k' = 0

theorem signed_interior_doors_sum_zero (K : SignedCellComplex V d)
    (c : V → Fin (d + 1)) :
    ∑ p ∈ (Finset.univ.filter fun p : K.Simplex × Fin (d + 1) =>
            isDoorAt c K.toCellComplex p.1 p.2 ∧ K.adj p.1 p.2 ≠ none),
        K.sign p.1 p.2 = 0
```

**Status-preservation rationale**: per CLAUDE.md axiom integrity policy and the slug's `problemStatement.formal`, the OQ-04 question reads as a single goal ("prove the signed analog of `interior_doors_even`"). That goal is met by `signed_interior_doors_sum_zero`. The S2-B / S2-C / S2-D extensions go *beyond* OQ-04's scope and are properly tracked as design notes (this PREP) or new slugs (deferred).

---

## §3. S2-B Mathlib bridge — 3-option design space

**Target**: relate `SignedCellComplex V d` to Mathlib's chain-complex infrastructure, ideally factoring through `AlternatingFaceMapComplex.alternatingFaceMapComplex` (`Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean:157`).

**Structural mismatch (the core design tension)**:

| Mathlib `SimplicialObject` | Sperner `CellComplex V d` |
|---|---|
| Functor `SimplexCategoryᵒᵖ ⥤ C` — *all* dimensions present | Top-dim simplices only (each with `d+1` vertices via `K.vertices`) |
| Face maps `δ i : X _⦋n+1⦌ ⟶ X _⦋n⦌` for every `n` | Adjacency `adj : Simplex → Fin (d+1) → Option (Simplex × Fin (d+1))` between top-dim only |
| `∂ = ∑ (-1)^i δᵢ` standard alternating sum | `sign : Simplex → Fin (d+1) → ℤ` user-supplied per-facet ±1 |
| Boundary cancellation `d ≫ d = 0` is automatic via the simplicial identities | `signed_interior_doors_sum_zero` is an indirect cancellation via `Finset.sum_involution` |

The honest reading: Sperner's `CellComplex` is **not** a simplicial object. It models a single-dimensional combinatorial structure (top-dim cells with adjacency on facets), which is genuinely different from Mathlib's graded simplicial / chain-complex framework. Three viable bridges:

### Option A — Direct 2-term `ChainComplex` (recommended for compact statement)

Define a 2-term complex at positions `{d, d-1}` using `ChainComplex.of` (`Mathlib/Algebra/Homology/HomologicalComplex.lean:616`):

```lean
def signedChainComplex (K : SignedCellComplex V d) :
    ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of
    (fun n => match n with
      | 0     => ModuleCat.of ℤ (K.Simplex × Fin (d + 1) →₀ ℤ)  -- (d-1)-facets
      | 1     => ModuleCat.of ℤ (K.Simplex →₀ ℤ)                -- d-simplices
      | _     => ModuleCat.of ℤ PUnit  -- truncated above
    )
    (fun n => ...)  -- d_1 : C_d → C_{d-1}, sign-weighted incidence; d_n = 0 otherwise
    (fun n => ...)  -- d ≫ d = 0
```

- **LOC**: ~80
- **Pros**: avoids the simplicial machinery entirely; the only Mathlib bearers needed are `ChainComplex.of` and `ModuleCat` constructors; `d ≫ d = 0` is trivial since `d_n = 0` for `n ≥ 2`.
- **Cons**: doesn't actually relate to `alternatingFaceMapComplex`; the bridge "to Mathlib" is shallow (just lives in the `HomologicalComplex` namespace).
- **Risk**: index gymnastics (Sperner's natural grading is top = `d`, Mathlib `ChainComplex` indexes from 0; need to either offset or live at positions `{0, 1}`). ~5 LOC of bookkeeping.

### Option B — Full `SimplicialObject` extension + functorial bridge

Build a full `SimplicialObject (ModuleCat ℤ)` from a `SignedCellComplex` by adding lower-dim simplices as quotients of `K.Simplex × (Fin (d+1) → Option (Fin (d+1)))` (face-trace pairs), then invoke `alternatingFaceMapComplex` to get a `ChainComplex (ModuleCat ℤ) ℕ`.

- **LOC**: ~150–200
- **Pros**: the bridge is *real* — the resulting complex genuinely passes through `alternatingFaceMapComplex`. Future work (e.g. Moore complex, normalized chains) is automatic via Mathlib's chain-complex machinery.
- **Cons**: requires non-trivial categorical glue (functor data + naturality + face-degeneracy identities) on a structure (`CellComplex`) that wasn't designed for it. Most of the work is *defining* the lower-dim simplices, which Sperner's API doesn't expose.
- **Risk**: face-degeneracy identities (`δᵢ ∘ δⱼ = δⱼ₋₁ ∘ δᵢ` for `i < j`, etc.) require careful book-keeping; classical sources do this for ordered simplicial complexes but `CellComplex.adj` is not naturally ordered. ~30–50 LOC of identity reasoning.

### Option C — Reformulate cancellation as `d ≫ d = 0` (compact, conceptually honest)

Skip the full chain complex; just state and prove that `signed_interior_doors_sum_zero` factors as a `d ≫ d = 0` identity for a 1-term shift. Concretely: define `∂ : (K.Simplex →₀ ℤ) →ₗ[ℤ] ((K.Simplex × Fin (d+1)) →₀ ℤ)` as the signed-incidence map, then state `(restrict-to-interior) ∘ ∂ = 0` as the *categorical version* of the S2-A theorem.

- **LOC**: ~50
- **Pros**: smallest delta; no `ChainComplex` namespace required (just `LinearMap` and `Finsupp` arithmetic); the categorical reading is honest (`signed_interior_doors_sum_zero` *is* a `d ≫ d = 0` identity in disguise, since the "interior door" predicate is precisely "lives in the image of the symmetrization map").
- **Cons**: doesn't deliver a `ChainComplex` object — only the underlying linear-algebra identity. If downstream users want Mathlib's chain-complex API (homology, Ext, …), they need to also build the `ChainComplex` wrapper.
- **Risk**: minimal — most of the work is already in the S2-A theorem; this is just repackaging.

### Recommendation

**Option A** (direct 2-term `ChainComplex`) is the strongest candidate for the *first* Mathlib-bridge PREP:
- delivers a concrete Mathlib object (a `ChainComplex (ModuleCat ℤ) ℕ`);
- LOC budget is modest (~80);
- the underlying mathematical content (`signed_interior_doors_sum_zero`) is already discharged in S2-A;
- the only new work is the categorical wrapping, which is mechanical.

**Option B** is the right *eventual* target if downstream consumers (Moore complex, homology, Ext) want full Mathlib integration. Defer until a concrete consumer materializes.

**Option C** is the right framing for a *non-bridge* follow-up: it documents the `d ≫ d = 0` shape of the S2-A theorem without committing to a `ChainComplex` object.

---

## §4. S2-C Tucker scaffold — paste-ready skeleton (recommended next ACT)

**Target**: define an antipodal extension of `SignedCellComplex` and state Tucker's lemma. This is the most self-contained follow-up; the structural extension is straightforward, and the statement is well-defined even if the proof is deferred.

### Paste-ready skeleton (~80 LOC, 2 acknowledged sorries on load-bearing existence)

Append to `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` below the existing `signed_interior_doors_sum_zero` theorem:

```lean
namespace AntipodalSigned

variable {V : Type*} [DecidableEq V] {d : ℕ}

/--
An **antipodal signed cell complex**: a `SignedCellComplex` together with
a vertex-level involution `ι : V → V` with no fixed points, satisfying
the sign-flip equivariance `sign(ι ∘ s, k) = -sign(s, k)`.

The classical setting for Tucker's lemma. The involution models the
ℤ/2-equivariance underlying antipodal Sperner / Borsuk-Ulam.
-/
structure AntipodalCellComplex (V : Type*) [DecidableEq V] (d : ℕ)
    extends SignedCellComplex V d where
  ι : V → V
  ι_involutive : Function.Involutive ι  -- `Mathlib/Logic/Function/Basic.lean:874`
  ι_no_fp : ∀ v, ι v ≠ v
  /-- The involution lifts to a simplex-level action: an antipodal-pair simplex
      `iotaSimplex s` whose vertices are `ι ∘ K.vertices s`. -/
  iotaSimplex : Simplex → Simplex
  iotaSimplex_vertices : ∀ s i, vertices (iotaSimplex s) i = ι (vertices s i)
  /-- Sign flips under the involution. -/
  sign_iota : ∀ s k, sign (iotaSimplex s) k = -(sign s k)
  /-- The involution is itself involutive on simplices (consistency). -/
  iotaSimplex_involutive : Function.Involutive iotaSimplex

namespace AntipodalCellComplex

variable {V : Type*} [DecidableEq V] {d : ℕ}

/-- An **antipodal coloring**: a coloring that satisfies `c (ι v) = neg c v`
where `neg : Fin (d+1) → Fin (d+1)` is the "antipodal color" map. For the
standard Tucker formulation, this is the negation in `Fin (d+1)` viewed as
the simplex `Δ^d`. -/
def IsAntipodalColoring (K : AntipodalCellComplex V d)
    (neg : Fin (d + 1) → Fin (d + 1)) (c : V → Fin (d + 1)) : Prop :=
  ∀ v, c (K.ι v) = neg (c v)

/--
**Tucker's lemma** (statement only; proof deferred to S2-C ACT).

For every antipodal coloring of an antipodal cell complex, there exists
a "complementary edge" — a 1-facet whose two endpoints carry antipodal
colors.
-/
theorem tucker_complementary_edge
    (K : AntipodalCellComplex V d)
    (neg : Fin (d + 1) → Fin (d + 1)) (hneg : Function.Involutive neg)
    (hneg_no_fp : ∀ k, neg k ≠ k)
    (c : V → Fin (d + 1)) (h_anti : IsAntipodalColoring K neg c) :
    ∃ (s : K.Simplex) (i j : Fin (d + 1)),
      i ≠ j ∧ c (K.vertices s i) = neg (c (K.vertices s j)) := by
  -- Strategy: invoke `signed_interior_doors_sum_zero` and analyse the
  -- *boundary* contributions. Under the antipodal coloring hypothesis,
  -- interior doors cancel (by S2-A), so any non-trivial signed door count
  -- must be balanced by boundary doors that carry the complementary edge.
  -- The full argument requires (a) a boundary-vs-interior decomposition
  -- and (b) a parity invariant of the door count modulo the involution.
  sorry  -- R5/HIGH: existence-witness via S2-A + parity descent

/--
**Equivariant Sperner** (Tucker, corollary form): the FC-cell count in
an antipodally colored signed cell complex is odd if and only if a
complementary edge exists. (The "only if" is `tucker_complementary_edge`;
the "if" is by parity-counting `signed_interior_doors_sum_zero`.)
-/
theorem signed_fc_count_parity_iff_complementary_edge
    (K : AntipodalCellComplex V d)
    (neg : Fin (d + 1) → Fin (d + 1)) (hneg : Function.Involutive neg)
    (hneg_no_fp : ∀ k, neg k ≠ k)
    (c : V → Fin (d + 1)) (h_anti : IsAntipodalColoring K neg c) :
    (Odd ((Finset.univ.filter fun s : K.Simplex => IsFC c K.toCellComplex s).card))
    ↔ ∃ (s : K.Simplex) (i j : Fin (d + 1)),
        i ≠ j ∧ c (K.vertices s i) = neg (c (K.vertices s j)) := by
  sorry  -- R5/HIGH: derived from S2-A's parity + tucker_complementary_edge

end AntipodalCellComplex
end AntipodalSigned
end Signed
end SpernerAbstract
```

### Risk reduction sketch for the 2 sorries

- **`tucker_complementary_edge`**: classical argument is a descent on the dimension `d`, leveraging `signed_interior_doors_sum_zero` to cancel interior contributions and reading off the parity of boundary doors. Requires an auxiliary `signed_boundary_door_count` lemma (~20 LOC) and a parity argument (`Nat.Odd` ⇒ existence; ~15 LOC). Reduction: invoke S2-A + extract boundary contribution + apply odd-count existence.
- **`signed_fc_count_parity_iff_complementary_edge`**: follows from `tucker_complementary_edge` + the parity-counting lemma already implicit in the parent's `interior_doors_even` (which gives an even count on interior doors). ~10 LOC of bookkeeping.

### LOC budget (S2-C ACT, projected)

- Structure definition: ~30 LOC
- `IsAntipodalColoring` + supporting decidability: ~10 LOC
- `tucker_complementary_edge` (proof): ~60 LOC
- `signed_fc_count_parity_iff_complementary_edge` (proof): ~20 LOC
- **Total: ~120 LOC** (matches the S2-A session memo's estimate).

---

## §5. S2-D Borsuk-Ulam bridge — design only (defer to dedicated slug)

The classical reduction (Tucker ⇒ Borsuk-Ulam) is topological: a continuous antipodal map `f : S^d → ℝ^d` factors through a fine simplicial subdivision of `S^d`, and the existence of a complementary edge (by Tucker) implies the existence of an antipodal point `x ∈ S^d` with `f(x) = f(-x)`.

In Lean, this requires:
- Mathlib's topological framework: `S^d` as `Metric.sphere (0 : EuclideanSpace ℝ (Fin (d+1))) 1`;
- continuous-map machinery: `ContinuousMap.antipodal_eq` (likely needs new development);
- simplicial subdivisions: would need to be developed (no current Mathlib home for the specific shape used).

**Recommendation**: S2-D belongs in a **dedicated slug**, not as a follow-up under `sperner-ndim-mathlib-oq-01-oq-04`. The current slug's scope is combinatorial; the topological reduction is a separate research arc. Suggested slug name (deferred to Seeker / Champion): `borsuk-ulam-via-tucker` or `sperner-ndim-mathlib-oq-02` (if `oq-02` is available; otherwise a sub-OQ of `tucker-lemma`).

---

## §6. Bearer-pin recheck consolidated (lake-SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0)

Re-verified at 2026-05-16T~10:30Z via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<sha>`:

| # | Declaration | Path | Line | Status |
|---|---|---|---|---|
| **For S2-A re-verification (sanity check post-merge):** | | | | |
| 1 | `Finset.prod_involution` (→ `sum_involution` via `@[to_additive]`) | `Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean` | 672–673 | ✓ stable (S2-A used this; 0 drift) |
| 2 | `ZMod.neg_eq_self_mod_two` | `Mathlib/Data/ZMod/Basic.lean` | 944 | ✓ stable (S2 PREP diagnosis bearer; 0 drift) |
| **New pins for S2-B (Option A, direct 2-term `ChainComplex`):** | | | | |
| 3 | `ChainComplex` (abbrev) | `Mathlib/Algebra/Homology/HomologicalComplex.lean` | 151 | ✓ verified |
| 4 | `ChainComplex.of` (constructor) | `Mathlib/Algebra/Homology/HomologicalComplex.lean` | 616 | ✓ verified — sig: `(X : α → V) (d : ∀ n, X (n + 1) ⟶ X n) (sq : ∀ n, d (n + 1) ≫ d n = 0) : ChainComplex V α` |
| 5 | `alternatingFaceMapComplex` (functor, for Option B reference) | `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean` | 157 | ✓ verified — `SimplicialObject C ⥤ ChainComplex C ℕ` |
| 6 | `AlternatingFaceMapComplex.obj` | `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean` | 122 | ✓ verified |
| 7 | `AlternatingFaceMapComplex.objD` (alternating face-sum) | `Mathlib/AlgebraicTopology/AlternatingFaceMapComplex.lean` | 66 | ✓ verified — `∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • X.δ i` |
| 8 | `SimplicialObject` (abbrev) | `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean` | 52 | ✓ verified — `SimplexCategoryᵒᵖ ⥤ C` |
| 9 | `SimplicialObject.δ` (face map) | `Mathlib/AlgebraicTopology/SimplicialObject/Basic.lean` | 96 | ✓ verified |
| **New pins for S2-C (Tucker scaffold):** | | | | |
| 10 | `Function.Involutive` | `Mathlib/Logic/Function/Basic.lean` | 874 | ✓ verified |
| 11 | `Function.Involutive.injective` (in namespace block) | `Mathlib/Logic/Function/Basic.lean` | 880–912 | ✓ verified (namespace block) |

**Drift summary**: 0 substantive drift since S2-A's recheck (researcher-10 2026-05-16T04:25Z, same lake SHA). All bearers verified at exact line numbers.

**Note on Option A's `Finsupp`/`ModuleCat` bearers**: deferring full audit to S2-B ACT (those bearers are in `Mathlib/LinearAlgebra/Finsupp/...` and `Mathlib/Algebra/Category/ModuleCat/Basic.lean`; routine API, low drift risk).

---

## §7. Risk inventory across S2-B / S2-C / S2-D

| ID | Risk | Bin | Notes |
|---|---|---|---|
| **R1** | S2-B Option A: index gymnastics (Mathlib `ChainComplex` indexes from 0; Sperner naturally lives at top dim `d`) | **MEDIUM** | ~5 LOC bookkeeping; the right convention is to live at `{0, 1}` with `0 = facets, 1 = simplices` |
| **R2** | S2-B Option B: defining `SimplicialObject` lower-dim simplices from `CellComplex.adj` | **HIGH** | structural; requires categorical glue; deferred to a dedicated S2-B-Option-B PREP if pursued |
| **R3** | S2-C: `iotaSimplex` field on `AntipodalCellComplex` needs to be well-defined (not auto-derived from `ι : V → V`) | **MEDIUM** | requires user to supply a simplex-level involution; the `iotaSimplex_vertices` field ensures coherence; ~5 LOC of bookkeeping |
| **R4** | S2-C: `tucker_complementary_edge` proof requires boundary-vs-interior decomposition | **HIGH** | ~60 LOC; the load-bearing sorry; reduction sketch documented in §4 |
| **R5** | S2-C: parity-of-FC-count argument (the "if" direction of `signed_fc_count_parity_iff_complementary_edge`) | **MEDIUM** | follows from S2-A + interior_doors_even (parent's existing theorem); ~10 LOC |
| **R6** | S2-D: requires new topological infrastructure (continuous antipodal maps, fine subdivisions) | **HIGH** | scope blocker — should be a dedicated slug, not a follow-up under this slug |
| **R7** | Slug status integrity: shipping a PREP on a `completed` slug risks confusion if `phase` is changed | **LOW** | mitigated by §2 status-preservation rationale + JSON refresh that keeps `status: completed` |
| **R8** *(INFRA)* | Host disk pressure / Docker daemon health | **INFRA** | this PREP is doc-only ⇒ unaffected; S2-C ACT will need ~1 GB free + responsive Docker (currently 6.9 Gi avail, daemon responsive on `docker ps` but `docker info Server:` empty — may be partially degraded) |

---

## §8. Recommended sequencing (next ACT = S2-C)

**Recommendation**: next ACT (whether by next claim-random or a dedicated claim) should target **S2-C** (Tucker scaffold), because:
- the structural extension (`AntipodalCellComplex`) is well-defined with all bearers pinned (R3 MEDIUM only);
- the paste-ready skeleton in §4 already isolates the 2 sorries on the load-bearing existence theorems;
- the LOC budget is moderate (~120 LOC) and self-contained;
- the dependency surface is just `SignedCellComplex` (S2-A) + `Function.Involutive` (Mathlib, ~5 LOC of API).

**S2-B (Mathlib bridge) deferred** because:
- Option A is "shallow" — adds a `ChainComplex` wrapper without delivering substantive new content;
- Option B is "deep" but requires non-trivial categorical glue (R2 HIGH);
- the right time to ship the bridge is when a downstream consumer (Moore complex, derived category use, Ext computation) materializes.

**S2-D (Borsuk-Ulam) deferred to a dedicated slug** per §5.

**Sequencing decision-tree**:
1. If next claim lands here AND host infra recovers (disk ≥30 GB, Docker responsive) → ship **S2-C ACT** using §4's paste-ready skeleton.
2. If next claim lands here AND host infra still constrained → ship a **PREP-2** narrowing R4 (the `tucker_complementary_edge` load-bearing sorry) into a concrete proof sketch.
3. If next claim lands here AND the slug status has been altered by an intermediate agent → run STATE-SYNC absorbing the intermediate change before proceeding.

---

## §9. Host infra snapshot + ACT-readiness gate

**Snapshot (2026-05-16T~10:35Z)**:

| Metric | Value | Status |
|---|---|---|
| `df -h /System/Volumes/Data` capacity | 100% | **RED** (≤10 Gi avail trigger) |
| `df -h /System/Volumes/Data` avail | 6.9 Gi | **RED** |
| `docker info` Client | 29.4.1, desktop-linux | green |
| `docker info` Server: section | empty (truncated by client connect-mode?) | **AMBER** — may be partially degraded |
| `docker ps` | exits cleanly (0s) | green |
| `gh -R rjwalters/lean-genius pr list --search "sperner-ndim-mathlib-oq-01-oq-04"` | 0 open | green |
| `git log --oneline -1 main -- proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` | `ecb47b35601 ... S2-A ACT ... (#19454)` | green (verified merge SHA) |

**8-item ACT-readiness gate for S2-C** (the recommended next ACT):

| # | Gate | Status |
|---|---|---|
| 1 | Mathematical statement clear | **GREEN** — Tucker's lemma statement is classical; encoding in §4 is straightforward |
| 2 | Parent-proof structural adaptability | **GREEN** — `signed_interior_doors_sum_zero` is the load-bearing primitive; available on main |
| 3 | Mathlib API verified at SHA | **GREEN** — bearers #10/#11 in §6 |
| 4 | Paste-ready skeleton present | **GREEN** — §4 ~80 LOC w/ 2 acknowledged sorries |
| 5 | Risk inventory + mitigations | **GREEN** — R3/R4/R5 in §7, with reduction sketches in §4 |
| 6 | Predecessor available on main | **GREEN** — S2-A PR #19454 merged at `ecb47b35601` |
| 7 | Load-bearing helper discharged or skeletoned | **AMBER** — 2 sorries on existence theorems (`tucker_complementary_edge`, `signed_fc_count_parity_iff_complementary_edge`); reduction sketches present but not paste-ready |
| 8 | Docker reachable + disk ≥30 Gi avail | **RED (INFRA-ONLY)** — daemon partially degraded + 6.9 Gi avail; ACT will need `./proofs/scripts/docker-build.sh Proofs.SpernerNDimMathlibOQ01OQ04` to verify |

**Verdict**: 6/8 GREEN substantive + 1 AMBER (gate 7, mitigable by a PREP-2 sketch-elaboration cycle) + 1 RED (gate 8, INFRA-ONLY, blocks S2-C ACT but not this S3 PREP). Ready for S2-C ACT *after* disk recovery and a PREP-2 paste-ready elaboration of the 2 sorries.

---

## §10. Files touched + NOT touched + honest scope

**Touched (3 files)**:

1. **NEW**: `research/problems/sperner-ndim-mathlib-oq-01-oq-04/sessions/2026-05-16-s3-prep-followup-design-survey.md` (this file, ~450 LOC).
2. **REWRITE-HEAD**: `research/problems/sperner-ndim-mathlib-oq-01-oq-04/state.md` — prepend S3 PREP block above S2-A ACT block; refine `## Follow-up sessions (NOT bundled into S2-A)` to point at this PREP for design; iter `3` → `4`; `Phase` unchanged (stays `COMPLETED`); add `Next Action: S2-C ACT (Tucker scaffold) per §4/§8`.
3. **REFRESH**: `src/data/research/problems/sperner-ndim-mathlib-oq-01-oq-04.json` — `currentState.iteration` 3 → 4; `currentState.focus` updated to "Follow-up design survey (S3 PREP) packaging S2-B/C/D design space; slug remains COMPLETED"; `currentState.nextAction` "S2-C ACT (Tucker scaffold) per S3 PREP §4 paste-ready skeleton — disk-recovery + PREP-2 sorry-elaboration prerequisites"; `lastUpdate` refreshed.

**NOT touched** (status-preservation discipline):

- `proofs/Proofs/SpernerNDimMathlibOQ01OQ04.lean` (S2-A body preserved verbatim)
- `proofs/Proofs/SpernerNDimMathlib.lean` (parent unchanged)
- `src/data/proofs/sperner-ndim-mathlib-oq-01-oq-04/{meta.json, index.ts, annotations.json}` (gallery preserved)
- `research/problems/sperner-ndim-mathlib-oq-01-oq-04/problem.md` (problem statement preserved)
- `research/problems/sperner-ndim-mathlib-oq-01-oq-04/knowledge.md` (knowledge base preserved; new design notes live in this session memo, not in the knowledge file)
- Any sister-slug state (`sperner-ndim-mathlib*`, `borsuk-ulam`, `tucker*`)
- The JSON's `status: completed` field — **preserved**; this PREP is *additive design context*, not a status downgrade

**Honest confidence**:
- §3 (S2-B 3-option design space): **medium-high** — Option A is straightforward; Option B is structurally hard but the difficulty is documented; Option C is repackaging only.
- §4 (S2-C paste-ready skeleton): **medium** — the structure definition and statement are clean; the 2 sorries are genuine work, but the reduction sketches are realistic.
- §5 (S2-D deferral to dedicated slug): **high** — the topological reduction is genuinely a different research arc.
- §6 (bearer recheck): **high** — all 11 bearers verified via `gh api` at exact SHA.
- §7 (risk inventory): **high** — risks binned conservatively; INFRA risk explicit.
- §8 (recommendation): **medium-high** — S2-C is the obvious next step on tractability + LOC grounds; the decision-tree handles the uncertain branches.

---

## Appendix: PR title + commit message

**PR title**: `research(sperner-ndim-mathlib-oq-01-oq-04): S3 PREP — packaged follow-up design (S2-B/S2-C/S2-D) w/ bearer pins + 3-option Mathlib-bridge audit + S2-C paste-ready skeleton (doc-only)`

**Commit message body**:
> S2-A ACT (PR #19454, merged 2026-05-16T04:45Z) discharged the slug's primary OQ-04 question with 207 LOC / 0 axioms / 0 sorries / Docker 7744 jobs clean. State.md head named three follow-up extensions (S2-B Mathlib bridge / S2-C Tucker scaffold / S2-D Borsuk-Ulam bridge).
>
> This PR packages design context for those follow-ups as a single doc-only S3 PREP (no `.lean` / gallery / meta / problem / knowledge edits; slug `status: completed` preserved):
>
> - 3-option audit for S2-B (direct 2-term `ChainComplex` / full `SimplicialObject` extension / `d ≫ d = 0` repackaging) w/ LOC budgets + pros/cons + recommendation (Option A);
> - paste-ready ~80-LOC Lean skeleton for S2-C (`AntipodalCellComplex` structure + `tucker_complementary_edge` statement + `signed_fc_count_parity_iff_complementary_edge` corollary) w/ 2 acknowledged sorries on load-bearing existence theorems (R4/R5);
> - S2-D deferred to dedicated slug (topological reduction is a different research arc);
> - 11-bearer pin recheck at lake-SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0): 0 drift since S2-A; bearers for `ChainComplex.of` / `alternatingFaceMapComplex` / `SimplicialObject` / `Function.Involutive` verified at exact line numbers;
> - 8-marker risk inventory + S2-C ACT-readiness gate (6/8 GREEN substantive + 1 AMBER on sorry-elaboration + 1 RED on host disk INFRA-ONLY).
>
> Recommendation: next ACT → S2-C (Tucker scaffold) per §4 paste-ready skeleton, gated on (a) host disk recovery (currently 6.9 Gi avail / 100% capacity) and (b) a PREP-2 elaboration of the two R4/R5 existence sorries.
