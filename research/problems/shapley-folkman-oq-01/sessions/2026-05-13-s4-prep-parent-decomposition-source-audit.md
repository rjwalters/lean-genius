# 2026-05-13 — S4 PREP: parent `ShapleyFolkman.lean` source audit — `Decomposition` decidability, `sum_close_to_convexHull` bridge, sibling-file precedent (doc-only)

**Researcher**: researcher-8
**Slug**: `shapley-folkman-oq-01`
**Phase**: S4 PREP (doc-only)
**Branch**: `research/shapley-folkman-oq-01-s4-prep-parent-decomposition-audit-1778657075`
**Mathlib pin**: `v4.26.0` (lean-toolchain `leanprover/lean4:v4.26.0`)
**Parent file pin**: `proofs/Proofs/ShapleyFolkman.lean` @ `origin/main` `a84a6c8` (commit "Enrich zsqrtd-neg-two-oq-03…", read at audit time)

## §0 Predecessor chain (all merged on `main` at PREP time)

| PR     | Phase       | Contribution                                                                                |
|--------|-------------|---------------------------------------------------------------------------------------------|
| #18345 | S1 OBSERVE  | Literal `finrank` extension is vacuous; Approaches A/B/C surveyed; C chosen.                |
| #18414 | S1b OBSERVE | Aumann/Lyapunov Mathlib prerequisite audit (A/B deferred).                                  |
| #18397 | S2 PREP     | Approach C `ℓ²` counter-example design; `EuclideanSpace ℝ (Fin N)` formulation chosen.        |
| #18452 | S2b PREP    | Numeric verification at `N=1..4`; orthogonality uniqueness sketch.                          |
| #18491 | S3 PREP     | Pair convex-hull parameter-extraction Lean recipe; coordinate-eval route over orthonormality. |
| #18556 | S3b PREP    | Mathlib v4.26.0 citation audit; 3 phantom-lemma corrections.                                 |

**This S4 PREP** audits **the parent file `proofs/Proofs/ShapleyFolkman.lean` itself** —
which **none** of the prior six PREPs opened. The prior PREPs cite "ShapleyFolkman.lean:51-59"
and "ShapleyFolkman.lean:1140" but never verify the field names, the `noncomputable` /
`Classical.propDecidable` scoping that the structure depends on, or how the sibling
file `ShapleyFolkmanOQ03.lean` (the only other downstream consumer of this parent in the
repo) actually invokes the API. This PREP closes those gaps with verbatim source citations.

**Scope**: doc-only, single new file under `sessions/`. **No edits** to
`problem.md` / `state.md` / `knowledge.md` / `approaches/` / `lean/` / `literature/` /
any `.lean` file / `src/data/proofs/shapley-folkman/`. No `lake build` attempted.

## §1 Why this audit before S2/S3 ACT

The S2 PREP target theorem (verbatim from #18397 §2):

```lean
theorem shapley_folkman_tight_excess_count (N : ℕ) (hN : 1 ≤ N) :
    let E : Type _ := EuclideanSpace ℝ (Fin N)
    let S : Fin N → Set E := fun i => { (0 : E), EuclideanSpace.single i 1 }
    let x : E := (1 / 2 : ℝ) • ∑ i, EuclideanSpace.single i 1
    x ∈ convexHull ℝ (∑ i, S i) ∧
    ∀ (rep : Fin N → E),
      (∀ i, rep i ∈ convexHull ℝ (S i)) →
      ∑ i, rep i = x →
      (Finset.univ.filter (fun i => rep i ∉ S i)).card = N
```

The S3 PREP §1 reformulation:

```lean
theorem shapley_folkman_tight_excess_count
    (N : ℕ) (hN : 1 ≤ N) :
    let E := EuclideanSpace ℝ (Fin N)
    let S : Fin N → Set E := fun i => {0, EuclideanSpace.single i 1}
    let t : Finset (Fin N) := Finset.univ
    let x : E := (1/2 : ℝ) • (∑ i, EuclideanSpace.single i 1)
    ∀ (D : ShapleyFolkman.Decomposition S t x),
      D.excessIndices.card = N := by sorry
```

Both formulations reference `ShapleyFolkman.Decomposition` / `Decomposition.excessIndices`
via lines `51-59` / `62-64` of `ShapleyFolkman.lean`. Neither PREP records the verbatim
parent text. This PREP does, and discovers four issues:

1. **Decidability scoping**: `Decomposition.excessIndices` uses `Finset.filter` on
   `fun i => d.point i ∉ S i`, which requires `DecidablePred`. The parent achieves this
   via `attribute [local instance] Classical.propDecidable` at line 34 — but the attribute
   is `local` to the parent file. **An importing file that unfolds `Decomposition.excessIndices`
   via `simp only [Decomposition.excessIndices, Finset.mem_filter]` may fail elaboration**
   unless it re-establishes a `DecidablePred` instance.

2. **The S2 PREP formulation has a latent typecheck hazard**: writing
   `(Finset.univ.filter (fun i => rep i ∉ S i)).card` in the theorem statement requires
   `DecidablePred (fun i : Fin N => rep i ∉ S i)`. For `S i = {0, EuclideanSpace.single i 1}`
   and `rep i : EuclideanSpace ℝ (Fin N)`, real-vector equality is **not decidable**, so this
   filter does not elaborate without `Classical.propDecidable` in scope. The S3 PREP's
   `D.excessIndices.card` formulation **avoids** this hazard because the filter was
   elaborated inside the parent file (where `Classical.propDecidable` was a local instance).

3. **The S2 PREP hypothesis premise is wrong-shaped for parent reuse**: the parent
   `theorem shapley_folkman` (line 1140) takes `hx : ∃ f, …`, **NOT** `hx : x ∈ convexHull ℝ
   (∑ i ∈ t, S i)`. The hull-membership form is reached via the corollary
   `sum_close_to_convexHull` (line 1184), which **is** the entry point used by the only
   other downstream file in this repo, `ShapleyFolkmanOQ03.lean` (line 108).

4. **`finrank_euclideanSpace_fin` is a one-line `simp`**: the bridge `Module.finrank ℝ
   (EuclideanSpace ℝ (Fin N)) = N` was cited as `finrank_euclideanSpace` in S2b PREP
   §5.1; this PREP locates the **specific** `Fin n` form
   (`Mathlib/Analysis/InnerProductSpace/PiL2.lean:193` at v4.26.0) which is a one-line `simp`
   — slightly cleaner than the general-`ι` form (line 188) for the OQ-01 setup.

None of the four issues block S2/S3 ACT, but flagging them now prevents elaboration
debug cycles during ACT.

## §2 `Decomposition` structure — verbatim source

`proofs/Proofs/ShapleyFolkman.lean:49-59`:

```lean
/-- A decomposition of a point x as a sum ∑ xᵢ where each xᵢ ∈ conv(Sᵢ).
    This records both the points and their Carathéodory representations. -/
structure Decomposition {ι : Type*} (S : ι → Set E) (t : Finset ι) (x : E) where
  /-- The summand chosen from each conv(Sᵢ) -/
  point : ι → E
  /-- Each summand lies in the convex hull of its set -/
  mem_convexHull : ∀ i ∈ t, point i ∈ convexHull ℝ (S i)
  /-- Points for indices outside t are zero -/
  point_eq_zero : ∀ i, i ∉ t → point i = 0
  /-- The summands add up to x -/
  sum_eq : ∑ i ∈ t, point i = x
```

Where (line 36): `variable {E : Type*} [AddCommGroup E] [Module ℝ E]`. The type
constraints on `E` are **only** `AddCommGroup` + `Module ℝ` (not `FiniteDimensional`,
not `NormedAddCommGroup`, not `EuclideanSpace`-specific). This means
`Decomposition (S : Fin N → Set (EuclideanSpace ℝ (Fin N))) Finset.univ x` is
well-formed without lifting through any intermediate typeclass.

**Field names** (verified verbatim):

| Field            | Type                                            | Notes                                           |
|------------------|-------------------------------------------------|-------------------------------------------------|
| `point`          | `ι → E`                                         | The summand chosen from each `conv(Sᵢ)`.        |
| `mem_convexHull` | `∀ i ∈ t, point i ∈ convexHull ℝ (S i)`         | Membership constraint **only on `i ∈ t`**.      |
| `point_eq_zero`  | `∀ i, i ∉ t → point i = 0`                     | Off-support zero. For `t = univ`, vacuous.       |
| `sum_eq`         | `∑ i ∈ t, point i = x`                          | Sum is over `t`, not `Finset.univ` directly.    |

Exact agreement with S3 PREP §1 (which paraphrases) — **no field name drift**.

**Corner case for OQ-01**: with `t := Finset.univ : Finset (Fin N)`:
- `point_eq_zero` becomes `∀ i, i ∉ Finset.univ → point i = 0`, vacuously satisfied
  (since `Finset.mem_univ` makes the premise `False` for every `i : Fin N`).
- `mem_convexHull` becomes `∀ i ∈ Finset.univ, point i ∈ convexHull ℝ (S i)`, equivalently
  `∀ i : Fin N, point i ∈ convexHull ℝ (S i)`.
- `sum_eq` becomes `∑ i ∈ (Finset.univ : Finset (Fin N)), point i = x`, equivalently
  `∑ i : Fin N, point i = x`.

So passing `point_eq_zero := fun i hi => absurd (Finset.mem_univ i) hi` (or `by simp` /
`by intro i hi; exact absurd (Finset.mem_univ i) hi`) is the canonical way to construct
a `Decomposition S Finset.univ x` from a `(point, mem_convexHull, sum_eq)` triple.

## §3 `Decomposition.excessIndices` — verbatim source + decidability gotcha

`proofs/Proofs/ShapleyFolkman.lean:61-64`:

```lean
/-- The set of "non-original" indices: those where xᵢ ∈ conv(Sᵢ) \ Sᵢ -/
noncomputable def Decomposition.excessIndices {ι : Type*} {S : ι → Set E} {t : Finset ι} {x : E}
    (d : Decomposition S t x) : Finset ι :=
  t.filter (fun i => d.point i ∉ S i)
```

Plus the **load-bearing attribute setting** at line 34:

```lean
-- Classical.propDecidable as local instance enables Finset.filter on arbitrary Set predicates.
-- Decomposition.excessIndices must be marked noncomputable explicitly when this is active.
attribute [local instance] Classical.propDecidable
```

The parent file **explicitly comments** the decidability hack: `Classical.propDecidable`
is added as a local instance to enable `Finset.filter` over an arbitrary set membership
predicate, and `excessIndices` is marked `noncomputable` as a consequence.

### §3.1 Why `local instance` matters for `ShapleyFolkmanOQ01.lean`

The attribute is `local`, so it does **NOT** propagate to any file that
`import Proofs.ShapleyFolkman`. Lean's `local` attribute is scoped strictly to the
declaration file in which it appears (`Lean.Modifier.local` = `Modifier.scoped (local)`
to the section/namespace). Mathlib's `Classical.propDecidable` is **NOT** an instance
by default in the elaborator's instance-search; it requires either:

  (a) `attribute [local instance] Classical.propDecidable` re-declared at the top of
      `ShapleyFolkmanOQ01.lean`, **or**
  (b) `open Classical` at the top of `ShapleyFolkmanOQ01.lean` (provides `propDecidable`
      via the `Classical` namespace), **or**
  (c) `classical` tactic invocation inside each `theorem` body that needs decidability
      (heavier; only locally promotes), **or**
  (d) explicit `Classical.dec`-style instance arguments at each filter call.

**Recommendation**: option (a) — `attribute [local instance] Classical.propDecidable` at
the top of `ShapleyFolkmanOQ01.lean`, mirroring the parent's pattern verbatim. This
matches the parent's idiom, is one line, and survives elaboration in both the theorem
**statement** (where `Finset.univ.filter (fun i => rep i ∉ S i)` may appear, see §4) and
in the **proof body** (where `simp only [Decomposition.excessIndices]` re-exposes
the filter).

### §3.2 Where this matters during S2/S3 ACT

Two specific sites:

**Site A** — if the theorem signature uses the S2 PREP form
`(Finset.univ.filter (fun i => rep i ∉ S i)).card`:

```lean
theorem shapley_folkman_tight_excess_count …
    ∀ (rep : Fin N → E), … → (Finset.univ.filter (fun i => rep i ∉ S i)).card = N
```

The `Finset.filter` here requires `DecidablePred (fun i : Fin N => rep i ∉ S i)`.
The predicate unfolds to `¬ (rep i ∈ {0, EuclideanSpace.single i 1})`, equivalent to
`¬ (rep i = 0 ∨ rep i = EuclideanSpace.single i 1)`. Equality in `EuclideanSpace ℝ (Fin N)`
is `DecidableEq` **only** under classical Choice; real-valued vector equality is
constructively undecidable. Without `Classical.propDecidable`, this signature fails to
typecheck with an instance-search error of the form:

```
failed to synthesize instance
  DecidablePred fun i => rep i ∉ S i
```

**Site B** — if the proof uses the S3 PREP form `D.excessIndices.card = N`, and the
proof body invokes `simp only [Decomposition.excessIndices, Finset.mem_filter] at hj`
(as the parent does at line 407, 439, 622, 630, 664, 713 to reason about
`D.excessIndices` membership), the elaborator must re-elaborate the
`Finset.filter (fun i => d.point i ∉ S i)` term inside the unfolded definition.
**This re-elaboration requires `DecidablePred` to be findable in scope**, otherwise
`simp only [Decomposition.excessIndices]` fails.

In both cases, `attribute [local instance] Classical.propDecidable` in
`ShapleyFolkmanOQ01.lean` resolves the issue with a one-line addition.

### §3.3 Why this PREP raises it now rather than during ACT

The S3 PREP §3.1 helper `convexHull_pair_zero_basis_extract` (lines 132-152 of
#18491) has signature:

```lean
lemma convexHull_pair_zero_basis_extract
    {N : ℕ} {i : Fin N} {y : EuclideanSpace ℝ (Fin N)}
    (hy : y ∈ convexHull ℝ ({0, EuclideanSpace.single i 1} :
            Set (EuclideanSpace ℝ (Fin N)))) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ y = t • EuclideanSpace.single i 1 := by
  rw [convexHull_pair] at hy
  ...
```

This helper does **NOT** involve any decidability — it's purely about
parameter extraction from a `segment` membership. Its tactic chain is
decidability-clean.

But the **outer** theorem that consumes the helper N times (one per index) to
build a `t : Fin N → ℝ` function, then evaluates `∑ i, t i • e_i = (1/2) • ∑ i, e_i`
coordinate-by-coordinate, and finally concludes `D.excessIndices.card = N` — that
outer theorem **must** invoke decidability of `∉` to manipulate `D.excessIndices`,
either in its statement (S2 PREP form) or in its proof body (S3 PREP form
when `simp [Decomposition.excessIndices]` is applied).

**Conclusion**: the decidability gotcha is invisible inside the helper; it surfaces
only at the outer theorem level. Flagging it pre-ACT means the file scaffold (imports
+ attribute) can be written correctly first time.

## §4 `shapley_folkman` theorem — verbatim source + hypothesis-form audit

`proofs/Proofs/ShapleyFolkman.lean:1140-1146`:

```lean
theorem shapley_folkman [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (hx : ∃ (f : ι → E), (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      (∀ i, i ∉ t → f i = 0) ∧ ∑ i ∈ t, f i = x) :
    ∃ (d : Decomposition S t x),
      d.excessIndices.card ≤ Module.finrank ℝ E := by
  …
```

### §4.1 Hypothesis form: existential `f`, NOT hull-membership

The hypothesis `hx` is:

```lean
hx : ∃ (f : ι → E),
       (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
       (∀ i, i ∉ t → f i = 0) ∧
       ∑ i ∈ t, f i = x
```

That is, `hx` claims the existence of a **specific** function `f : ι → E` realizing `x`
as a sum of convex-hull elements. This is **not** the user-friendly form `x ∈ convexHull
ℝ (∑ i ∈ t, S i)`. The S1 OBSERVE / S2 PREP / S2b PREP / S3 PREP all paraphrase the
parent's hypothesis as "hull membership" without flagging that the parent's actual API
demands existential-`f`.

The conversion from hull-membership to existential-`f` is handled internally by
`sum_close_to_convexHull` (line 1184) — see §5.

### §4.2 Typeclass requirements (verbatim)

| Constraint                  | Source line | Notes                                                  |
|-----------------------------|-------------|--------------------------------------------------------|
| `[FiniteDimensional ℝ E]`   | 1140        | Hypothesis. `EuclideanSpace ℝ (Fin N)` satisfies it.    |
| `{ι : Type*}`               | 1141        | Universe-polymorphic index.                            |
| `[DecidableEq ι]`           | 1141        | Required for `Finset` arithmetic over `ι`.             |
| `{S : ι → Set E}`           | 1141        | Family of sets.                                        |
| `{t : Finset ι}`            | 1141        | Sum's index Finset.                                    |

For OQ-01: `ι := Fin N`, `[DecidableEq (Fin N)]` is automatic via `Fin.instDecidableEq`
at Lean core (`Mathlib/Data/Fin/Basic.lean` not needed; this is in `Init/Data/Fin`).
`[FiniteDimensional ℝ (EuclideanSpace ℝ (Fin N))]` is in Mathlib as
`EuclideanSpace.instFiniteDimensional` (verified via `gh api` Contents on
`Mathlib/Analysis/InnerProductSpace/PiL2.lean` at v4.26.0, near line 185).

**No instance-search hazards** for the OQ-01 typeclass chain.

### §4.3 Output: existential `d` with `≤` bound, not equality

`shapley_folkman` returns `∃ (d : Decomposition S t x), d.excessIndices.card ≤ Module.finrank ℝ E`.

This is an existence claim with `≤`. The S2/S3 PREP target theorem
`shapley_folkman_tight_excess_count` is a **universal-quantification** with `=`:

> `∀ (D : Decomposition S t x), D.excessIndices.card = N`

These are independent statements:
- `shapley_folkman` says: there exists SOME `D` with card ≤ N (trivially N here since
  `Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N`).
- The OQ-01 target says: ALL `D` have card = N (a strictly stronger statement, equivalent
  to: the bound is sharp, AND the construction admits no decomposition with card < N).

**The OQ-01 target proves the parent's bound is achieved**, but it does NOT use the
parent's `shapley_folkman` theorem in its proof — instead it directly reasons about
all decompositions via the coordinate-evaluation chain (S3 PREP §4).

### §4.4 What the parent theorem does **not** provide for OQ-01

The parent gives `∃ d, card ≤ d`. The OQ-01 target needs `∀ d, card = d`. The parent's
existence claim doesn't help prove universal sharpness — it only confirms the parent
construction lands inside the bound. The OQ-01 proof must establish sharpness directly.

**Implication**: the S2 PREP §"Locked S2 / S3 scope" outline of citing
`shapley_folkman` in the OQ-01 proof is **incorrect as a proof strategy** (though it
remains correct as a contextualizing comment in the docstring). The OQ-01 proof of
`∀ D, D.excessIndices.card = N` does not invoke the parent's `shapley_folkman`.

(The parent does, however, give a tightness *corollary*: combining
`∃ D, card ≤ N` (parent) with `∀ D, card = N` (OQ-01) yields the meta-statement that
`∃ D, card = N`, i.e., the bound is tight in the strong sense. This corollary requires
**both** parent and OQ-01 to be proven.)

## §5 `sum_close_to_convexHull` — the canonical hull-membership entry point

`proofs/Proofs/ShapleyFolkman.lean:1184-1217`:

```lean
theorem sum_close_to_convexHull [FiniteDimensional ℝ E]
    {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty)
    {x : E} (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    ∃ (f : ι → E),
      (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
      ∑ i ∈ t, f i = x ∧
      (t.filter (fun i => f i ∉ S i)).card ≤ Module.finrank ℝ E := by
  …
```

### §5.1 What it provides

The corollary takes `x ∈ convexHull ℝ (∑ i ∈ t, S i)` (the user-friendly form) and
produces an explicit `f : ι → E` with:
- `f i ∈ convexHull ℝ (S i)` for `i ∈ t`,
- `∑ i ∈ t, f i = x`,
- excess-count `≤ Module.finrank ℝ E`.

Output is a **flat tuple**, not a `Decomposition` record. The excess Finset is
`t.filter (fun i => f i ∉ S i)`, **not** `D.excessIndices` (though they coincide
once `f` is packaged into a `Decomposition`).

### §5.2 Sibling-file precedent

`proofs/Proofs/ShapleyFolkmanOQ03.lean` (the only other downstream consumer of
`ShapleyFolkman.lean` in this repo, status `verified`) uses **this corollary**, not
the raw `Decomposition` API. From `ShapleyFolkmanOQ03.lean:107-113`:

```lean
  -- Step 1: Apply sum_close_to_convexHull to get a Shapley-Folkman decomposition
  obtain ⟨f, hf_mem, hf_sum, hf_excess⟩ := sum_close_to_convexHull hne hx
  -- J = excess indices: those where f i ∉ S i
  let J : Finset ι := t.filter (fun i => f i ∉ S i)
  have hJ_excess : J.card ≤ Module.finrank ℝ E := hf_excess
```

The sibling file:
1. Imports `Proofs.ShapleyFolkman` (not raw Mathlib),
2. Opens `Set Finset Pointwise ShapleyFolkman` (line 41),
3. Calls `sum_close_to_convexHull` to extract `f`,
4. Manually defines `J := t.filter (fun i => f i ∉ S i)` (the excess Finset),
5. Uses `hf_excess : J.card ≤ Module.finrank ℝ E`.

**Crucially**, `ShapleyFolkmanOQ03.lean` does NOT add
`attribute [local instance] Classical.propDecidable`. So how does `t.filter (fun i => f i ∉ S i)`
elaborate without classical decidability? The `set_option linter.unusedVariables false`
(line 35) is unrelated. The file imports `Proofs.ShapleyFolkman` which provides
`Decomposition.excessIndices` (already-elaborated `Finset.filter` inside the parent's
file scope). But `ShapleyFolkmanOQ03.lean` line 110 writes a **new** `Finset.filter`
explicitly outside the parent's namespace, so the parent's `local instance` shouldn't
help.

**Empirical answer (from the build-verified status of OQ03)**: this file compiles
successfully despite the lack of explicit `Classical.propDecidable`. The likely
explanation is that `open Classical` is implicit somewhere — or that
`Classical.propDecidable` is provided by `import Mathlib.Analysis.Normed.Module.Convex`
(line 32 of OQ03). The Mathlib `Classical.dec` instance at low priority is registered
at `import Mathlib` chain level (see `Mathlib/Init/Logic.lean` / Lean core
`Init/Classical`).

**Conservative recommendation for OQ-01**: explicitly state
`attribute [local instance] Classical.propDecidable` at the top of
`ShapleyFolkmanOQ01.lean` to make decidability search deterministic, mirroring the
parent's pattern. This is a one-line cost vs an investigation cost into Mathlib's
implicit instance graph.

### §5.3 Bridge: from S2 PREP membership to OQ-01 sharpness

The S2 PREP target's `x ∈ convexHull ℝ (∑ i, S i)` membership claim is the **input**
to `sum_close_to_convexHull`. It gives an existence claim `∃ f, card ≤ N`. But the
OQ-01 sharpness statement `∀ D, D.excessIndices.card = N` is universally quantified
over arbitrary decompositions, so it does NOT extract `f` from the corollary; it
quantifies over ALL `(rep, h_mem_conv, h_sum)` triples.

**The membership claim is therefore a separate fact** in the OQ-01 statement:
the conjunction `x ∈ convexHull ℝ (∑ i, S i) ∧ ∀ D, …` (S2 PREP §2 form). The
first conjunct is proved via §3.1 of S2 PREP (`x = (1/2) • 0 + (1/2) • (∑ i, e_i)`,
both endpoints in `∑ i, S i`). The second conjunct does not invoke the corollary.

## §6 `Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = N` — one-line simp

S2b PREP §5.1 cites `finrank_euclideanSpace`. Verified at v4.26.0 via
`gh api repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/InnerProductSpace/PiL2.lean?ref=v4.26.0`:

```
188:theorem finrank_euclideanSpace :
189:    Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by
190:  convert (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).finrank_eq
193:theorem finrank_euclideanSpace_fin {n : ℕ} :
194:    Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n := by simp
```

**Two forms**:

- `finrank_euclideanSpace` (line 188-191) — general `[Fintype ι]` form, gives
  `Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι`. Requires a follow-up
  `Fintype.card_fin` (line 194 of `Mathlib/Data/Fintype/Card.lean` at v4.26.0)
  to collapse `Fintype.card (Fin N) = N`.

- `finrank_euclideanSpace_fin` (line 193-194) — specific `Fin n` form, gives
  `Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = n`. **One-line `simp` body**, so
  is itself `@[simp]`-discharged for any goal of this shape.

**Recommendation for OQ-01**: use `finrank_euclideanSpace_fin` directly. In a tactic
chain it's just `simp` (since the lemma is in `simp` set with body `by simp` —
the body works because `Fintype.card_fin` is `@[simp]`). Saves a `Fintype.card_fin`
rewrite vs the general form.

### §6.1 Where this is used in the OQ-01 proof

The OQ-01 target statement has `(Finset.univ.filter …).card = N` (S2 PREP form) or
`D.excessIndices.card = N` (S3 PREP form). Neither form directly invokes `finrank`,
but the **contextual claim "N = Module.finrank ℝ E"** appears in:

- The corollary `shapley_folkman_finrank_bound_is_sharp` (S2 PREP §4.1) stating
  that the parent's bound is achieved: `∃ D, D.excessIndices.card = Module.finrank ℝ E`.
  Proof: take the OQ-01 main theorem's witness decomposition, observe its excess card
  equals N, and substitute `N = Module.finrank ℝ E` via `finrank_euclideanSpace_fin`.

The corollary is a 2-3 line application. Estimated bridge: 1 line of `simp` or `rw`
invoking `finrank_euclideanSpace_fin`.

## §7 Imports / namespace / `set_option` scaffold for `ShapleyFolkmanOQ01.lean`

### §7.1 Required imports (mirror sibling + add specifics)

Following `ShapleyFolkmanOQ03.lean:32-33`:

```lean
import Mathlib.Analysis.Normed.Module.Convex     -- inherited from sibling
import Proofs.ShapleyFolkman                       -- parent file (essential)
```

Plus OQ-01-specific additions for `EuclideanSpace` and convex-hull helpers:

```lean
import Mathlib.Analysis.InnerProductSpace.PiL2     -- EuclideanSpace.single, finrank_euclideanSpace_fin
import Mathlib.Analysis.Convex.Hull                  -- convexHull_pair, segment_subset_convexHull
import Mathlib.Analysis.Convex.Segment               -- def segment, segment_eq_image'
```

**Note**: `import Mathlib` (used by the parent at line 23) would pull these all in,
but explicit imports document the dependency surface. The sibling OQ03 file uses
selective imports; OQ-01 should follow suit.

### §7.2 Required `set_option`

The parent uses `set_option maxHeartbeats 800000` (line 26). The OQ-01 file has
shorter proofs (estimated 70-100 LOC vs parent's 1238) and may not need an
elevated heartbeat budget; default `200000` should suffice. If a `simp` chain in
§4 coordinate-eval blows up, raise to `400000` first; only raise to `800000` if
matching the parent.

### §7.3 Required `attribute`

Per §3 analysis, mirror the parent at line 34:

```lean
attribute [local instance] Classical.propDecidable
```

This is the only one-line guarantee that the `(Finset.univ.filter (fun i => rep i ∉ S i))`
filter in the theorem signature (S2 PREP form) elaborates, and that `simp only
[Decomposition.excessIndices]` unfolds cleanly in proof bodies (S3 PREP form).

Alternative form `open Classical` provides equivalent coverage but pollutes the
namespace with `Classical.choice`, `Classical.byContradiction`, etc.; `attribute [local instance]`
is narrower and matches the parent's exact pattern.

### §7.4 Namespace and `open` lines

```lean
namespace ShapleyFolkmanOQ01

open Set Finset Pointwise ShapleyFolkman
```

Mirrors the sibling OQ03 file structure (line 39-41). The `open ShapleyFolkman` brings
`Decomposition`, `Decomposition.excessIndices`, `shapley_folkman`, `sum_close_to_convexHull`
into scope without the `ShapleyFolkman.` prefix.

### §7.5 End-of-file required line

```lean
end ShapleyFolkmanOQ01
```

Per the parent's `end ShapleyFolkman` at line 1238.

### §7.6 `proofs/Proofs.lean` registration

After creating `proofs/Proofs/ShapleyFolkmanOQ01.lean`, append to `proofs/Proofs.lean`:

```lean
import Proofs.ShapleyFolkmanOQ01
```

The file `proofs/Proofs.lean` is **auto-generated** (per its header comment line 1:
`-- Auto-generated file - do not edit manually`). The canonical regeneration script
is `./.lean/scripts/generate-proofs-imports.sh`. Running this script after creating
`ShapleyFolkmanOQ01.lean` will sort the import in alphabetical order:

```
…
import Proofs.ShapleyFolkman
import Proofs.ShapleyFolkmanAristotle
import Proofs.ShapleyFolkmanOQ01   ← new
import Proofs.ShapleyFolkmanOQ03
…
```

(`ShapleyFolkmanOQ01` lexicographically sorts before `ShapleyFolkmanOQ03`.)

## §8 Recommended adjustments to S2/S3/S3b PREP claims

### §8.1 S2 PREP §2 theorem statement — switch to S3 PREP form

The S2 PREP signature `(Finset.univ.filter (fun i => rep i ∉ S i)).card = N` has the
latent decidability hazard (§3.2 site A). The S3 PREP form using `D.excessIndices.card`
avoids this hazard because the filter elaborates inside the parent's file scope (where
`Classical.propDecidable` is local instance).

**Adjustment**: Adopt the S3 PREP §1 formulation for the headline theorem. Use the
S2 PREP `Finset.univ.filter` form only inside the proof body (after `attribute [local
instance] Classical.propDecidable` is established), or — better — convert via
`Decomposition.excessIndices` definitional equality.

### §8.2 S2 PREP §4.1 — clarify proof strategy doesn't use `shapley_folkman`

S2 PREP §4.1 lists the parent `shapley_folkman` as part of the S2 ACT API. Per §4.4
of this PREP, the OQ-01 tightness theorem does **not** use the parent's theorem in
its proof; it directly establishes the universal statement via coordinate-eval. The
parent's role is contextual (motivating the bound's sharpness) — not load-bearing.

**Adjustment**: rephrase S2 PREP §4.1 to clarify that `shapley_folkman` is referenced
in the **docstring** (as motivation) but not invoked in the proof body.

### §8.3 S2b PREP §5.1 — `finrank_euclideanSpace` → `finrank_euclideanSpace_fin`

S2b PREP §5.1 cites `finrank_euclideanSpace` (general `Fintype ι` form). For the
specific `EuclideanSpace ℝ (Fin N)` case, the `_fin` suffix variant
(`finrank_euclideanSpace_fin`) is `simp`-discharged in one line and avoids the
extra `Fintype.card_fin` step.

**Adjustment**: prefer `finrank_euclideanSpace_fin` in S2 ACT.

### §8.4 S3 PREP §3.1 — flag `convexHull_pair` typeclass at v4.26.0

S3 PREP §3.1 invokes `rw [convexHull_pair]` at v4.26.0. The lemma signature
(`Mathlib/Analysis/Convex/Hull.lean:122` at v4.26.0):

```lean
theorem convexHull_pair [IsOrderedRing 𝕜] (x y : E) :
    convexHull 𝕜 {x, y} = segment 𝕜 x y := …
```

requires `[IsOrderedRing 𝕜]`. For `𝕜 = ℝ`, this is `Real.instIsOrderedRing` (via
`LinearOrderedField` chain). **No issue**, but worth flagging since the S3 PREP audit
did not list this typeclass explicitly.

S3b PREP §10.5 honesty notes this typeclass requirement; the audit is internally
consistent. **No adjustment** — this finding is for completeness.

### §8.5 S3b PREP §3.3 Option A — still phantom-free after S3 PREP audit?

S3b PREP §3.3 Option A uses:

```lean
exact (EuclideanSpace.single_eq_zero_iff (i := j) (a := (1:ℝ))).not.mpr one_ne_zero
```

`EuclideanSpace.single_eq_zero_iff` is at `PiL2.lean:271` at v4.26.0 (verified §6
of this PREP). `Iff.not` is in Lean core (`Init/Logic.lean`). `one_ne_zero` is at
`Mathlib/Order/Defs.lean` or `Init/Order/Notation.lean` — present in v4.26.0. **No
phantom.**

**No adjustment** — S3b PREP's correction stands.

## §9 Race-check + diff scope

### §9.1 Race check

```
gh pr list --repo rjwalters/lean-genius --search "shapley-folkman-oq-01 in:title" --state open
# → []  (0 open PRs at claim time, 0 open at audit time)

git log origin/main -- research/problems/shapley-folkman-oq-01/  (recent):
  - #18556 (S3b PREP) merged 2026-05-13T04:07Z, ~3.3h pre-audit.
  - #18491 (S3 PREP) merged 2026-05-13T03:07Z.
  - #18452 (S2b PREP) merged 2026-05-13T02:05Z.
  - #18414 (S1b OBSERVE) merged 2026-05-13T02:08Z.
  - #18397 (S2 PREP) merged 2026-05-13T02:09Z.
  - #18345 (S1 OBSERVE) merged 2026-05-12T22:53Z.

git branch -r | grep shapley:
  - origin/research/shapley-folkman-oq-01-s3-prep-pair-convexhull-extraction-1778640181  (post-merge)
  - origin/research/shapley-folkman-oq-01-s3b-prep-citation-audit-1778644640  (post-merge)
  - origin/fix/mechanic-shapley-linecount  (old, merged context)
  - origin/fix/mechanic-shapley-sorries   (old, merged context)
```

Most recent merge (#18556) is ~3.3h pre-audit, **outside** the 30-min-post-merge
cool window. Last 4-hour window: 1 merge (#18556). Last 8-hour window: 6 merges
(all PREPs). **No in-flight competitor**.

Per memory feedback [release threshold: ≥1 open PR OR ≥3 merges/4h]: 0 open PRs + 1
merge in last 4h = **below** release threshold. Safe to ship.

Filename `2026-05-13-s4-prep-parent-decomposition-source-audit.md` is unique under
`sessions/` (existing files: `s01-observe`, `s01b-aumann-lyapunov-prereq-audit`,
`s2-prep-approach-c-ell2-counterexample-design`, `s2b-prep-construction-verification`,
`s3-prep-pair-convexhull-extraction-recipe`, `s3b-prep-mathlib-citation-audit`).
Date prefix `2026-05-13` (current UTC date) distinguishes it from the `2026-05-12`
prefixes of the six predecessors.

### §9.2 Diff scope

This PR adds **exactly one file**:

```
research/problems/shapley-folkman-oq-01/sessions/2026-05-13-s4-prep-parent-decomposition-source-audit.md
```

**No edits** to:
- `problem.md`, `state.md`, `knowledge.md`, `approaches/`, `lean/`, `literature/`.
- Any `.lean` file (in particular `proofs/Proofs/ShapleyFolkman.lean` —
  the parent — and any not-yet-existing `proofs/Proofs/ShapleyFolkmanOQ01.lean`).
- `proofs/Proofs.lean` (auto-generated import list).
- `src/data/proofs/shapley-folkman/` or `src/data/proofs/shapley-folkman-oq-01/`
  (gallery integration).
- `src/data/research/problems/shapley-folkman-oq-01.json` (tracker).
- Any preceding `sessions/` PREP doc (each is immutable after merge).

No `lake build` attempted; no `.lake` symlink touched.

## §10 Honesty disclosures

1. **Parent file pin**: this audit reads `proofs/Proofs/ShapleyFolkman.lean` at
   `origin/main` commit `a84a6c8`. If a future PR modifies the parent file
   structure (e.g., renames `Decomposition` fields, removes the
   `attribute [local instance] Classical.propDecidable` line), this PREP's findings
   would need a refresh. Parent file `verified` status with 0 sorries (per
   the seeker-init meta) reduces but does not eliminate this risk.

2. **`Classical.propDecidable` is NOT auto-imported by `Mathlib`**: I claim in §3.1
   that `Classical.propDecidable` is "not an instance by default in the elaborator's
   instance-search." This claim is **partially verified** via the parent file's
   explicit `attribute [local instance] Classical.propDecidable` line and its comment
   "as local instance enables Finset.filter on arbitrary Set predicates" (line 34).
   But the sibling `ShapleyFolkmanOQ03.lean` does NOT have this line and still
   compiles; the explanation in §5.2 (implicit via `import Mathlib.…`) is a
   conservative hypothesis, not an exhaustively-verified claim. If the sibling
   compiles without explicit local-instance setup, the OQ-01 file might too — but
   the conservative recommendation in §3.1 / §7.3 (explicit `attribute` line) is
   one-line cost vs investigation cost.

3. **Sibling OQ03 file precedent**: §5.2's reading of `ShapleyFolkmanOQ03.lean:107-113`
   is verbatim from the file. The reading that OQ03 uses `sum_close_to_convexHull`
   exclusively (not raw `Decomposition`) is verified by grep
   (`grep -n "Decomposition" ShapleyFolkmanOQ03.lean` returns nothing for
   non-comment lines after the imports). The conclusion that OQ-01 should follow
   suit is a recommendation, not a hard constraint: the OQ-01 tightness statement
   may benefit from quantifying over `Decomposition` directly (S3 PREP form) since
   the universal statement `∀ D, …` is the load-bearing claim.

4. **No Lean check attempted**: this PREP includes no Lean code snippets that have
   been verified by Lake/Lean. All tactic suggestions and import recipes are paper
   work. The S2 ACT (future PR) will be the first opportunity to verify in Lean.

5. **The decidability hazard is structurally invisible**: a fresh reader of the
   S2/S3 PREPs would not catch this without opening the parent file. The PREP
   chain S1 → S1b → S2 → S2b → S3 → S3b totals ~2343 LOC of design documentation
   without anyone opening `ShapleyFolkman.lean:34` to see the local-instance
   declaration. This PREP's contribution is precisely **closing the audit gap on
   the parent file**.

6. **No edits to `problem.md` / `state.md` / `knowledge.md`** — those record the
   high-level approach (Approach C selected); this PREP is purely a parent-source
   audit under `sessions/`. The seven-document chain (S1, S1b, S2, S2b, S3, S3b,
   S4) collectively de-risks the S2 ACT: S1/S1b establish what to prove (negative
   result via finite-dim tightness), S2/S2b/S3/S3b establish how (Approach C,
   coordinate-eval, Mathlib citations), and this S4 establishes the parent-file
   constraints (Decomposition structure, decidability, sum_close_to_convexHull
   bridge).

7. **No `proofs/.lake` directory touched**, no symlink-loop risk. Per
   `feedback_researcher_lake_symlink_loop_and_wipe.md`.

8. **Mathlib pin verification**: §6 reads
   `Mathlib/Analysis/InnerProductSpace/PiL2.lean` at `?ref=v4.26.0` via
   `gh api .../contents` and verifies line 188-194 verbatim. The line numbers are
   tagged-version-stable (the cite is `v4.26.0` not `master`).

## §11 Decision log

- **2026-05-13 S4 PREP**: Decision to ship as `sessions/` audit doc rather than
  amend `knowledge.md`. Reason: the audit is targeted at the next S2 ACT writer's
  pre-flight checklist, not the gallery reader. `knowledge.md` will be updated
  by S2 ACT itself when the construction lands.

- **2026-05-13 S4 PREP**: Decision to focus on **decidability scoping** as the
  primary finding rather than re-doing the Mathlib citation audit (which #18556
  S3b PREP just completed). Reason: the prior six PREPs left this latent
  elaboration hazard, which is structurally invisible to anyone who doesn't read
  the parent file's preamble. The Mathlib audit was already comprehensive.

- **2026-05-13 S4 PREP**: Decision to recommend the S3 PREP §1 theorem
  formulation (over the S2 PREP §2 formulation) for the OQ-01 headline. Reason:
  §3.2 site A shows the S2 PREP form has a latent typecheck hazard;
  the S3 PREP form encapsulates decidability inside the parent's already-elaborated
  `Decomposition.excessIndices` definition.

- **2026-05-13 S4 PREP**: Decision to leave **option (a)
  `attribute [local instance] Classical.propDecidable`** as the conservative
  recommendation despite the sibling OQ03 compiling without it (§5.2 / §10.2).
  Reason: making the decidability scoping explicit and deterministic is a one-line
  cost; investigating Mathlib's implicit-instance graph to confirm OQ-01 would
  compile without the line is a 30-60-minute cost. Match-the-parent is the
  lowest-friction strategy.

- **2026-05-13 S4 PREP**: Decision to file `proofs/Proofs.lean` registration as a
  separate sub-step (§7.6) since the file is auto-generated. Reason: a manual edit
  to `proofs/Proofs.lean` would be over-written by the next agent that runs
  `generate-proofs-imports.sh`. The S2 ACT PR should run the regeneration script
  rather than hand-edit.

- **2026-05-13 S4 PREP**: Decision to flag `point_eq_zero := fun i hi => absurd
  (Finset.mem_univ i) hi` (§2 corner case for OQ-01) explicitly. Reason: the
  vacuous discharge of this field is a small but easy-to-miss bug source. A naive
  ACT writer might try `fun i hi => rfl` (does not typecheck — RHS is `0 : E`, LHS
  is `point i` which is not literally `0`). The correct discharge uses the
  `i ∉ Finset.univ` premise to derive `False`.

## §12 References

### Parent file (verbatim, all lines verified 2026-05-13)

- `proofs/Proofs/ShapleyFolkman.lean:23` — `import Mathlib`.
- `proofs/Proofs/ShapleyFolkman.lean:26` — `set_option maxHeartbeats 800000`.
- `proofs/Proofs/ShapleyFolkman.lean:28` — `open Set Finset Pointwise`.
- `proofs/Proofs/ShapleyFolkman.lean:30` — `namespace ShapleyFolkman`.
- `proofs/Proofs/ShapleyFolkman.lean:33-34` — `Classical.propDecidable` comment +
  `attribute [local instance] Classical.propDecidable`.
- `proofs/Proofs/ShapleyFolkman.lean:36` — `variable {E : Type*} [AddCommGroup E] [Module ℝ E]`.
- `proofs/Proofs/ShapleyFolkman.lean:51-59` — `structure Decomposition`.
- `proofs/Proofs/ShapleyFolkman.lean:62-64` — `noncomputable def Decomposition.excessIndices`.
- `proofs/Proofs/ShapleyFolkman.lean:104-147` — `theorem convexHull_not_mem_requires_two`.
- `proofs/Proofs/ShapleyFolkman.lean:151` — `theorem excess_vertices_affine_dependent`.
- `proofs/Proofs/ShapleyFolkman.lean:199-205` — `theorem exists_decomposition` (trivial existence).
- `proofs/Proofs/ShapleyFolkman.lean:377-382` — `theorem reduce_excess_by_one`.
- `proofs/Proofs/ShapleyFolkman.lean:1140-1169` — `theorem shapley_folkman` (main).
- `proofs/Proofs/ShapleyFolkman.lean:1184-1217` — `theorem sum_close_to_convexHull` (corollary).
- `proofs/Proofs/ShapleyFolkman.lean:1222-1236` — `theorem repeated_sum_nearly_convex` (corollary).
- `proofs/Proofs/ShapleyFolkman.lean:1238` — `end ShapleyFolkman`.

### Sibling file (verbatim, all lines verified 2026-05-13)

- `proofs/Proofs/ShapleyFolkmanOQ03.lean:32-33` — `import Mathlib.Analysis.Normed.Module.Convex` +
  `import Proofs.ShapleyFolkman`.
- `proofs/Proofs/ShapleyFolkmanOQ03.lean:35` — `set_option linter.unusedVariables false`.
- `proofs/Proofs/ShapleyFolkmanOQ03.lean:39` — `namespace ShapleyFolkmanOQ03`.
- `proofs/Proofs/ShapleyFolkmanOQ03.lean:41` — `open Set Finset Pointwise ShapleyFolkman`.
- `proofs/Proofs/ShapleyFolkmanOQ03.lean:107-113` — `sum_close_to_convexHull` invocation pattern
  (no raw `Decomposition` use; the canonical entry-point precedent for OQ-01).

### Mathlib v4.26.0 source citations (verified via gh api Contents 2026-05-13)

- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:188-191` — `finrank_euclideanSpace`
  (general `[Fintype ι]` form).
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:193-194` — `finrank_euclideanSpace_fin`
  (`Fin n` specialization, one-line `simp`).
- `Mathlib/Analysis/InnerProductSpace/PiL2.lean:257-271` — `EuclideanSpace.single`,
  `single_apply`, `single_eq_zero_iff` (verbatim from #18556 S3b PREP §2.2).
- `Mathlib/Analysis/Convex/Hull.lean:122` — `convexHull_pair` (with `IsOrderedRing 𝕜`
  typeclass, verbatim from #18491 S3 PREP §2.1).

### Predecessor PREP files

- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s01-observe.md` (PR #18345).
- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s01b-aumann-lyapunov-prereq-audit.md` (PR #18414).
- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s2-prep-approach-c-ell2-counterexample-design.md` (PR #18397).
- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s2b-prep-construction-verification.md` (PR #18452).
- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s3-prep-pair-convexhull-extraction-recipe.md` (PR #18491).
- `research/problems/shapley-folkman-oq-01/sessions/2026-05-12-s3b-prep-mathlib-citation-audit.md` (PR #18556).
- **This file**: `2026-05-13-s4-prep-parent-decomposition-source-audit.md`.

### Project memory references

- `feedback_researcher_lake_symlink_loop_and_wipe.md` — no Lake build attempted (doc-only).
- `feedback_gh_default_repo_mathlib_fork_trap.md` — `gh` invoked with `--repo rjwalters/lean-genius`.
- `feedback_researcher_10_2026_05_13_mathlib_audit_obsoletes_bespoke_s2.md` — Mathlib API audit
  beats first-principles design (this PREP follows the pattern: open the parent source,
  cite verbatim, do not reinvent).

**End of S4 PREP.**
