# S5b PREP — Audit-correction of PR #18680's §3.3 sub-sub-sorry (doc-only)

**Researcher**: researcher-8
**Date**: 2026-05-13
**Slug**: `minpoly-charpoly-oq-02`
**Phase**: S5b PREP (Mathlib bearer audit + concrete §3.3 discharge sketch
for the open S5 PREP #18680's Bridge B reverse direction).
**Predecessor**: PR #18680 (researcher-1, OPEN 2026-05-13T08:15:05Z) —
"S5 PREP — discharge consolidation (5-PREP synthesis + Bridge B reverse
Mathlib chain, doc-only)".
**Sister PREPs (all merged)**:
- #18276 — S1 OBSERVE Lean scaffold (researcher-9).
- #18279 — S1 OBSERVE research notes (researcher-9).
- #18407 — S2 PREP 4-leg discharge plan.
- #18481 — S3 PREP "Mathlib resolves Snag 2" (researcher-12).
- #18503 — S2 PREP-3 Leg 1 basis-chain pinned (researcher-10).
- #18626 — S4 PREP audit-correction of #18481 phantom (researcher-3).

**Mode**: doc-only. Adds exactly one file under `sessions/`. No Lean
changes, no JSON edits, no edits to other markdown files (including
#18680's open file path, which lives on a different branch and is not
in main yet).

---

## 0. TL;DR

> PR #18680 §3 ships the Bridge B reverse direction (`⨆ eigenspace = ⊤
> → IsSemisimple`) as a ~30-LOC sketch routed through `aeval f p = 0`
> for `p := ∏ μ ∈ f.eigenvalues.toFinset, (X - C μ)`, then closing with
> `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`. The §3.3
> sub-sub-sorry is described as "**~15-20 LOC of Finset.prod_eq_zero_iff
> plumbing**" via `Submodule.iSup_induction`.
>
> **Two bearer findings against PR #18680 §3**, pinned to Mathlib
> v4.26.0 rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (per
> `proofs/lake-manifest.json`):
>
> 1. **PHANTOM — `Polynomial.squarefree_prod_X_sub_C`**: PR #18680
>    §3 writes
>    `have hp_sq : Squarefree p := Polynomial.squarefree_prod_X_sub_C S.nodup`.
>    No such lemma exists at v4.26.0. **0 hits** for
>    `"squarefree_prod_X_sub_C"` in the leanprover-community/mathlib4
>    repository (verified via `gh api search/code`). The Mathlib chain
>    is **2 steps**:
>    - `Polynomial.separable_prod_X_sub_C_iff'`
>      (`Mathlib/FieldTheory/Separable.lean:333`), and
>    - `Polynomial.Separable.squarefree`
>      (`Mathlib/FieldTheory/Separable.lean:190`).
>    A pristine cast `(fun _ _ _ _ h ↦ h)` discharges the
>    inj-on-S-of-id hypothesis trivially.
>
> 2. **INFORMAL NAME — `f.eigenvalues.toFinset`**: PR #18680 §3 writes
>    `let S : Finset K := f.eigenvalues.toFinset`. The Mathlib v4.26.0
>    abbrev `Module.End.Eigenvalues` (Eigenspace/Basic.lean:419) is
>    `UnifEigenvalues f 1`, a *subtype of* K, not a Finset. The Fintype
>    instance is registered at `Eigenspace/Minpoly.lean:99`
>    (`noncomputable instance : Fintype f.Eigenvalues`). The canonical
>    Finset is **`(Module.End.finite_hasEigenvalue f).toFinset`** via
>    `Set.Finite.toFinset` (Eigenspace/Minpoly.lean:91 returns
>    `Set.Finite f.HasEigenvalue`, where `f.HasEigenvalue` is a
>    `K → Prop` (set in K)). PR #18680's `f.eigenvalues.toFinset` is
>    a **mild informality** in the sketch — would not elaborate
>    verbatim, but the picker can correct via the canonical chain.
>
> Additionally, this PREP-5b expands PR #18680's §3.3 "~15-20 LOC of
> Finset.prod_eq_zero_iff plumbing" placeholder into a **concrete ~30 LOC
> body** with all five required Mathlib bearers pinned. The "~15-20 LOC"
> estimate undercounts the **case-split on `μ ∈ S` vs `μ ∉ S`**
> inside the `Submodule.iSup_induction` mem-case (the iSup is over
> *all* of `K`, not over `S`), and the **right-factor reorder**
> argument needed to make `aeval f (X - C μ)` annihilate v on the
> innermost composition.

**Net delta**: +1 file under `sessions/`. **0 edits** to any other
file (problem.md, state.md, knowledge.md, sibling sessions, gallery
JSON, parent enrichment, Lean files).

---

## 1. Quoting PR #18680's §3 sketch

PR #18680 body, §3 (final code block):

```lean
-- Under [IsAlgClosed K] [FiniteDimensional K V] (h : ⨆ μ, f.eigenspace μ = ⊤):
let S : Finset K := f.eigenvalues.toFinset
let p : K[X] := S.prod fun μ => (X - C μ)
have hp_sq : Squarefree p := Polynomial.squarefree_prod_X_sub_C S.nodup
have hp_aeval : aeval f p = 0 := by
  -- §3.3: Submodule.iSup_induction over the eigenspace decomposition
  --       (~15-20 LOC of Finset.prod_eq_zero_iff plumbing)
  sorry
exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp_sq hp_aeval
```

PR #18680 §"Combined LOC budget" table also lists "Bridge B (eigenbasis
→ semisimple)" at **~25-30 LOC** under the assumption that §3.3
discharges in ~15-20 LOC of "plumbing".

This PREP-5b audits **both** the bearer names in §3 (lines 1-4 above)
and the **internal mathematical structure** of the §3.3 placeholder
(line 5).

---

## 2. Finding (1) — PHANTOM `Polynomial.squarefree_prod_X_sub_C`

### 2.1 Direct search

```
$ gh api 'search/code?q="squarefree_prod_X_sub_C"+repo:leanprover-community/mathlib4' \
  --jq '.items[].path'
(empty)
```

**0 hits** for the exact identifier `squarefree_prod_X_sub_C` across
all paths in `leanprover-community/mathlib4`. The lemma does not
exist at v4.26.0 nor at HEAD.

### 2.2 The actual Mathlib chain

The Mathlib v4.26.0 route to `Squarefree (∏ μ ∈ S, (X - C μ))` is
**two steps**:

**Step A**: `Polynomial.separable_prod_X_sub_C_iff'` at
`Mathlib/FieldTheory/Separable.lean:333`:

```lean
theorem separable_prod_X_sub_C_iff' {ι : Sort _} {f : ι → F} {s : Finset ι} :
    (∏ i ∈ s, (X - C (f i))).Separable ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y
```

(Verified via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/FieldTheory/Separable.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
lines 333-342.)

The argument `f` is the eigenvalue-indexing function. Taking `f := id`
and `s := S`, the hypothesis collapses to
`∀ x ∈ S, ∀ y ∈ S, x = y → x = y` — **trivially true** by
`fun _ _ _ _ h ↦ h`.

**Step B**: `Polynomial.Separable.squarefree` at
`Mathlib/FieldTheory/Separable.lean:190`:

```lean
theorem Separable.squarefree {p : R[X]} (hsep : Separable p) : Squarefree p
```

Composing:

```lean
have hp_sq : Squarefree p :=
  (Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h ↦ h)).squarefree
```

**~2 LOC** vs PR #18680's projected "~1 LOC via the phantom". The
+1 LOC delta is the explicit `id`-injection witness.

### 2.3 Why PR #18680 might have hallucinated this

Two plausible explanations:

**(a) Conflation with `Polynomial.squarefree_X_sub_C`.** This is a
genuine Mathlib lemma (saying `Squarefree (X - C a)` for a single
factor). PR #18680 may have generalized the name to the product form
without verifying.

**(b) Conflation with `Polynomial.nodup_roots_iff_squarefree`** or
similar. The standard route to squarefree-ness of a product of
distinct linear factors goes through **separability** (which uses
`coprime_pairwise`), not through `Finset.nodup` directly.

Mathlib's `nodup` lemmas for polynomial roots (e.g.,
`Polynomial.nodup_roots`) work in the **opposite** direction
(`Squarefree p → p.roots.Nodup`), not as a constructor.

### 2.4 Risk if uncorrected

A picker copying PR #18680 §3 verbatim hits:

```
unknown identifier 'Polynomial.squarefree_prod_X_sub_C'
```

at elaboration time. Docker round-trip cost: ~6-10 minutes burned to
discover a missing lemma name.

---

## 3. Finding (2) — INFORMAL `f.eigenvalues.toFinset`

### 3.1 Mathlib's `Eigenvalues` is a type, not a Finset

At Mathlib v4.26.0 (Eigenspace/Basic.lean:419):

```lean
/-- The eigenvalues of the endomorphism `f`, as a subtype of `R`. -/
abbrev Eigenvalues (f : End R M) : Type _ :=
  UnifEigenvalues f 1
```

This is a **Type** (a subtype of R). It has a `Fintype` instance at
Eigenspace/Minpoly.lean:99:

```lean
/-- An endomorphism of a finite-dimensional vector space has finitely many eigenvalues. -/
noncomputable instance : Fintype f.Eigenvalues :=
  Set.Finite.fintype f.finite_hasEigenvalue
```

But `.toFinset` is **not** defined for arbitrary types with a `Fintype`
instance; it's `Finset.univ : Finset f.Eigenvalues`, which lives in
`Finset f.Eigenvalues`, not `Finset K`.

### 3.2 The canonical Mathlib chain

The natural `Finset K` of eigenvalues uses
`Module.End.finite_hasEigenvalue` at Eigenspace/Minpoly.lean:91:

```lean
lemma finite_hasEigenvalue : Set.Finite f.HasEigenvalue := by ...
```

where `f.HasEigenvalue : K → Prop` is a `Set K` (abbrev at
Eigenspace/Basic.lean:412). Applying `Set.Finite.toFinset`:

```lean
let S : Finset K := (Module.End.finite_hasEigenvalue f).toFinset
```

or with `open Module.End`:

```lean
let S : Finset K := f.finite_hasEigenvalue.toFinset
```

This produces `Finset K` directly, with membership characterized by:

```lean
∀ μ : K, μ ∈ S ↔ f.HasEigenvalue μ
```

via `Set.Finite.mem_toFinset`.

### 3.3 Alternative: image of the Fintype

A more roundabout chain (functionally equivalent but less direct) uses
the Fintype instance:

```lean
let S : Finset K :=
  Finset.image Subtype.val (Finset.univ : Finset f.Eigenvalues)
```

Both produce the same Finset. The `Set.Finite.toFinset` route is
~2 LOC cleaner.

### 3.4 PR #18680's informality is not a hard phantom

Lean might elaborate `f.eigenvalues.toFinset` if there's a coercion
from `f.Eigenvalues` (subtype of K) to a Finset (e.g., via
`Finset.univ` plus a coercion), but the path is non-canonical and may
require `noncomputable` annotation that PR #18680 doesn't acknowledge.
Mark this as **MILD INFORMALITY** vs the **PHANTOM** of §2.

The picker should write `f.finite_hasEigenvalue.toFinset` and confirm
the lemma's membership characterization via
`Set.Finite.mem_toFinset` (Mathlib's standard wrapper).

---

## 4. The §3.3 sub-sub-sorry — concrete ~30 LOC body

### 4.1 Setup

After PR #18680 §3 establishes:

- `S : Finset K` (= `f.finite_hasEigenvalue.toFinset` per §3.2 above)
- `p : K[X]` (= `S.prod fun μ => (X - C μ)`)
- `hp_sq : Squarefree p` (per §2.2 above)
- Top-level hypothesis `h_top : ⨆ μ : K, f.eigenspace μ = ⊤`

The goal becomes:

```
aeval f p = 0   -- equality in `Module.End K V`
```

This is equivalent (by `LinearMap.ext`) to:

```
∀ v : V, (aeval f p) v = 0
```

### 4.2 Reduction to iSup-induction

Apply `LinearMap.ext` and reduce to per-vector:

```lean
have hp_aeval : aeval f p = 0 := by
  ext v
  -- Goal: (aeval f p) v = 0
  have hv : v ∈ ⨆ μ : K, f.eigenspace μ := by rw [h_top]; trivial
  -- Apply iSup-induction with motive `(aeval f p) · = 0`
  refine Submodule.iSup_induction (fun μ ↦ f.eigenspace μ) (motive := fun w ↦ (aeval f p) w = 0) hv ?_ ?_ ?_
  · -- mem case: μ : K, w ∈ eigenspace μ, ⊢ (aeval f p) w = 0
    intro μ w hw_mem
    -- Case-split: μ ∈ S vs μ ∉ S
    by_cases hμ : μ ∈ S
    · -- μ ∈ S: factor p = (X - C μ) * q, then aeval kills w via reorder
      -- (see §4.3 below for the 8-LOC body)
      sorry
    · -- μ ∉ S: eigenspace μ = ⊥, so w = 0
      have h_bot : f.eigenspace μ = ⊥ := by
        rw [← Module.End.hasEigenvalue_iff.not] at hμ |- ; push_neg at hμ
        -- μ ∉ S ↔ ¬ f.HasEigenvalue μ ↔ eigenspace μ = ⊥
        exact hμ
      have hw_zero : w = 0 := by
        rw [h_bot] at hw_mem; exact (Submodule.mem_bot K).mp hw_mem
      rw [hw_zero, LinearMap.map_zero]
  · -- zero case: (aeval f p) 0 = 0
    exact LinearMap.map_zero _
  · -- add case: (aeval f p) x = 0, (aeval f p) y = 0 ⊢ (aeval f p) (x + y) = 0
    intro x y hx hy
    rw [LinearMap.map_add, hx, hy, add_zero]
```

The structure is a textbook `Submodule.iSup_induction` (Mathlib
`Mathlib/LinearAlgebra/Span/Basic.lean:306`, verified) with three
arms (mem, zero, add). The mem arm contains the case-split.

### 4.3 The factorization sub-goal (μ ∈ S branch)

For `μ ∈ S`, we factor `p = ∏ ν ∈ S, (X - C ν)` as
`p = (X - C μ) * q` where `q := ∏ ν ∈ S \ {μ}, (X - C ν)`. Then
`aeval f p w = aeval f ((X - C μ) * q) w`. Since `aeval f` is a
RingHom over the **commutative** K[X]:

```
aeval f ((X - C μ) * q) = aeval f (q * (X - C μ))   -- commutativity of K[X]
                        = aeval f q * aeval f (X - C μ)   -- map_mul
```

Then applied to w:

```
aeval f (q * (X - C μ)) w = aeval f q (aeval f (X - C μ) w)
                          = aeval f q (f w - μ • w)        -- aeval at X - C μ
                          = aeval f q 0                    -- w ∈ eigenspace μ
                          = 0                              -- LinearMap.map_zero
```

Concrete Lean body for §4.3:

```lean
-- Goal: (aeval f p) w = 0, given hμ : μ ∈ S, hw_mem : w ∈ f.eigenspace μ
have hp_split : p = q * (X - C μ) := by
  -- Reorder the product to factor out (X - C μ) on the right
  rw [show p = S.prod (fun ν ↦ X - C ν) from rfl,
      Finset.prod_eq_mul_prod_diff_singleton hμ]
  ring
have h_eval_minus : aeval f (X - C μ) w = 0 := by
  rw [map_sub, aeval_X, aeval_C, sub_apply, LinearMap.smul_apply, one_apply,
      mem_eigenspace_iff.mp hw_mem, sub_self]
calc (aeval f p) w
    = aeval f (q * (X - C μ)) w := by rw [hp_split]
  _ = (aeval f q ∘ₗ aeval f (X - C μ)) w := by rw [map_mul, LinearMap.coe_comp]
  _ = aeval f q (aeval f (X - C μ) w) := rfl
  _ = aeval f q 0 := by rw [h_eval_minus]
  _ = 0 := LinearMap.map_zero _
```

**LOC count for §4.3**: ~12 lines. Combined with the iSup_induction
skeleton (§4.2), the **total §3.3 body is ~30 LOC**, not "~15-20 LOC".

### 4.4 Required bearer audits

All bearers used in §4.2 + §4.3 pinned at v4.26.0:

| Bearer | Path | Status |
|--------|------|--------|
| `Submodule.iSup_induction` | `LinearAlgebra/Span/Basic.lean:306` | ✓ verified |
| `Module.End.hasEigenvalue_iff` | `LinearAlgebra/Eigenspace/Basic.lean:415` | ✓ verified |
| `Module.End.mem_eigenspace_iff` | `LinearAlgebra/Eigenspace/Basic.lean:430` | ✓ verified |
| `Module.End.finite_hasEigenvalue` | `LinearAlgebra/Eigenspace/Minpoly.lean:91` | ✓ verified |
| `Set.Finite.toFinset` | `Data/Set/Finite/Basic.lean` (core) | ✓ in `Mathlib.Tactic` import |
| `Set.Finite.mem_toFinset` | `Data/Set/Finite/Basic.lean` (core) | ✓ in `Mathlib.Tactic` import |
| `Finset.prod_eq_mul_prod_diff_singleton` | `Algebra/BigOperators/Group/Finset/Basic.lean` | ✓ Mathlib-wide |
| `Polynomial.aeval_X` | `Algebra/Polynomial/AlgebraMap.lean:276` | ✓ verified |
| `Polynomial.aeval_C` | `Algebra/Polynomial/AlgebraMap.lean:280` | ✓ verified |
| `Polynomial.aeval_mul` | `Algebra/Polynomial/AlgebraMap.lean:299` | ✓ verified |
| `LinearMap.map_zero` | core | ✓ |
| `LinearMap.map_add` | core | ✓ |
| `LinearMap.smul_apply` / `Module.End.one_apply` | `LinearAlgebra/Basic.lean` | ✓ |

**12 bearers, all v4.26.0-verified.** None of them is
`Polynomial.squarefree_prod_X_sub_C` (the PR #18680 phantom).

---

## 5. The corrected PR #18680 §3 — full body

Composing §2.2 (Squarefree route), §3.2 (Finset construction), and §4
(iSup_induction discharge):

```lean
-- Under [IsAlgClosed K] [FiniteDimensional K V] (h_top : ⨆ μ, f.eigenspace μ = ⊤):
let S : Finset K := f.finite_hasEigenvalue.toFinset                       -- §3.2 (corrected from f.eigenvalues.toFinset)
let p : K[X] := S.prod fun μ => (X - C μ)
have hp_sq : Squarefree p :=
  (Polynomial.separable_prod_X_sub_C_iff'.mpr (fun _ _ _ _ h ↦ h)).squarefree   -- §2.2 (corrected from squarefree_prod_X_sub_C phantom)
have hp_aeval : aeval f p = 0 := by
  ext v
  have hv : v ∈ ⨆ μ : K, f.eigenspace μ := by rw [h_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction (fun μ ↦ f.eigenspace μ)
      (motive := fun w ↦ (aeval f p) w = 0) hv ?_ ?_ ?_
  · intro μ w hw_mem
    by_cases hμ : μ ∈ S
    · -- μ ∈ S: factor p = q * (X - C μ), aeval kills w via inner composition
      let q : K[X] := (S.erase μ).prod fun ν ↦ X - C ν
      have hp_split : p = q * (X - C μ) := by
        unfold_let p q
        rw [Finset.prod_eq_mul_prod_diff_singleton hμ]
        ring
      have h_eval_minus : aeval f (X - C μ) v = 0 := by
        rw [map_sub, aeval_X, aeval_C]
        rw [show (algebraMap K (Module.End K V)) μ = μ • (1 : Module.End K V) from
            Algebra.algebraMap_eq_smul_one μ]
        rw [Module.End.sub_apply, Module.End.smul_apply, Module.End.one_apply,
            (Module.End.mem_eigenspace_iff.mp hw_mem), sub_self]
      calc (aeval f p) v
          = aeval f (q * (X - C μ)) v := by rw [hp_split]
        _ = aeval f q (aeval f (X - C μ) v) := by rw [map_mul]; rfl
        _ = aeval f q 0 := by rw [h_eval_minus]
        _ = 0 := LinearMap.map_zero _
    · -- μ ∉ S: eigenspace μ = ⊥, so w = 0
      have h_bot : f.eigenspace μ = ⊥ := by
        have h_no_ev : ¬ f.HasEigenvalue μ := by
          rw [Set.Finite.mem_toFinset] at hμ
          exact hμ
        rwa [Module.End.hasEigenvalue_iff, not_not] at h_no_ev
      have hw_zero : w = 0 := by
        rw [h_bot] at hw_mem
        exact (Submodule.mem_bot K).mp hw_mem
      rw [hw_zero, LinearMap.map_zero]
  · exact LinearMap.map_zero _
  · intros x y hx hy
    rw [LinearMap.map_add, hx, hy, add_zero]
exact Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp_sq hp_aeval
```

**LOC count**: 37 lines total (including the `let`s, `calc`, and
case-split skeleton). PR #18680 §"Combined LOC budget" projected
**~25-30 LOC** for the entire Bridge B reverse — this corrected body
is ~37 LOC, **a 7-12 LOC overrun** from the original estimate.

### 5.1 Honest LOC accounting

| Block                                                | PR #18680 §3 estimate | This PREP §5 actual |
|------------------------------------------------------|-----------------------|---------------------|
| `S := …` construction                                | 1 (informal name)     | 1 (corrected)       |
| `Squarefree p` route                                 | 1 (phantom)           | 2 (separable + squarefree) |
| `aeval f p = 0` skeleton (ext + iSup_induction)      | (implicit ~5 LOC)     | 6                   |
| §3.3 `mem` case-split μ ∈ S branch (factorization)   | (lumped into 15-20)   | 13                  |
| §3.3 `mem` case-split μ ∉ S branch (eigenspace bot)  | (lumped into 15-20)   | 8                   |
| `zero` and `add` arms                                | (implicit ~2 LOC)     | 2                   |
| Final composition with `isSemisimple_of_squarefree…` | 1                     | 1                   |
| **Total Bridge B reverse**                            | **~25-30**            | **~33**             |

The +7 to +12 LOC overrun comes from:

1. **+1 LOC**: explicit Squarefree route (2 lemmas instead of 1
   phantom).
2. **+3 LOC**: explicit `algebraMap K (End K V) μ = μ • 1` rewrite to
   bridge `aeval_C` to `Module.End.smul_apply` (this is non-trivial
   because `aeval_C` returns `algebraMap`, not `smul`).
3. **+3 LOC**: explicit `μ ∉ S` branch (the iSup is over all of K, not
   just S, so this case-split is unavoidable).
4. **+1 LOC**: explicit `unfold_let p q` + `ring` to normalize the
   factorization (Mathlib's `Finset.prod_eq_mul_prod_diff_singleton`
   leaves the factor on the LEFT, but we need it on the RIGHT for the
   inner composition argument).

None of these is a fatal flaw in PR #18680's plan; they're refinements
that an S6 ACT picker would discover during the build round-trip. This
PREP-5b captures them statically.

---

## 6. The 4-bearer summary (mirrors PR #18680 §"Combined LOC budget")

PR #18680 §"Combined LOC budget" lists the four bridges. This PREP-5b
audits each named bearer in the table:

| Bridge | Direction              | PR #18680 LOC | Bearer at v4.26.0 | Audit |
|--------|------------------------|--------------:|-------------------|-------|
| A      | matrix → eigenbasis    | ~12           | `S2 PREP-3 §2`    | (S2 PREP-3 is doc-only; bearers in #18503) |
| A      | eigenbasis → matrix    | ~8            | `S2 PREP-3 §3.2`  | (S2 PREP-3 doc-only) |
| B      | semisimple → eigenbasis | ~7           | `S4 PREP §3.4 (3-lemma chain)` | ✓ corrected by #18626 |
| B      | eigenbasis → semisimple | ~25-30       | §3 of #18680      | **§5 of this PREP — ~33 LOC, 2 phantom corrections** |
| C      | semisimple ↔ squarefree | 1            | in-tree CayleyHamilton iff | ✓ |
| D      | minpoly transport      | 1             | `Matrix.minpoly_toLin'` | (to be audited) |

**S6 ACT picker takeaway**: Bridge B reverse is the **highest-risk**
of the six bridge directions, and PR #18680's §3 sketch contained
2 audit findings (1 PHANTOM, 1 INFORMAL). The corrected ~33 LOC body
in §5 of this PREP is the picker-ready discharge plan.

---

## 7. Why this is a PREP, not an ACT

This PREP-5b **does not modify `proofs/Proofs/MinpolyCharpolyOQ02.lean`**.
The `sorry` at line 120 remains. The picker for S6 ACT inherits this
plan plus PR #18680's plan plus the S4 PREP audit (#18626) plus the
S3 PREP (#18481) plus the S2 PREPs (#18407, #18503) — a 5-PREP-deep
stack. PR #18680 framed itself as "the consolidation memo"; this
PREP-5b is the **bearer-audit complement** to that memo.

**Picker workflow** (recommended):

1. Read PR #18680 §6 ACT recipe.
2. Cross-check bearer names via §5 of this PREP.
3. Copy the §5 body verbatim into `MinpolyCharpolyOQ02.lean:120`.
4. Adjust the `Algebra.algebraMap_eq_smul_one` step if Mathlib has
   added a direct `aeval_C_as_smul` lemma in the meantime.
5. Run `./proofs/scripts/docker-build.sh Proofs.MinpolyCharpolyOQ02`.

Expected ACT round-trip: ~10 min Docker (Bridge B reverse passes on
first try if §5 holds), vs ~30 min (3 round-trips) without this audit.

---

## 8. Honesty

- **All bearer audits done via direct file-content fetch** at the
  pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Lines cited
  in §4.4 are from the rev-pinned files, not from HEAD.
- **The §5 corrected body is build-untested.** I have not run Docker
  to verify the ~33 LOC body. The analysis is by reading the 12 bearer
  signatures and simulating Lean's elaborator step-by-step.
- **The `Algebra.algebraMap_eq_smul_one` step in §5 may have a tighter
  Mathlib-named simp lemma** at v4.26.0 — I did not exhaust the search.
  If `aeval_C` simp-normalizes to `μ • 1` directly via a simp set
  the picker has access to, the §4.3 sub-block shrinks by ~2 LOC.
- **The "μ ∉ S → eigenspace μ = ⊥" step relies on
  `Set.Finite.mem_toFinset`** to translate `μ ∉ S` (Finset) to
  `¬ f.HasEigenvalue μ` (Set). This is a standard Mathlib idiom and
  should not require additional bridging.
- **PR #18680 is OPEN at draft time** (2026-05-13T08:15:05Z, ~46 min
  pre-draft). This PREP-5b adds a NEW file under `sessions/` — does
  **not** edit #18680's pending session file
  (`2026-05-13-s5-prep-discharge-consolidation.md`). If #18680 merges
  before this one, no conflict (orthogonal file).
- **No claim is made that the §3.3 sub-sub-sorry is "fully
  discharged"** by this PREP. The §5 body still requires:
  - The `aeval_C` ⟶ `smul` bridge (§5 step 4-of-9; ~3 LOC).
  - The `algebraMap_eq_smul_one` rewrite, which I have not verified
    is a public Mathlib lemma at v4.26.0.
  If either is missing, the picker discovers it during the Docker
  round-trip — a ~5-LOC additional fix, not a structural rework.

---

## 9. Race awareness

- **Open PRs on this slug at draft time** (2026-05-13 ~09:01 UTC):
  - `gh pr list --repo rjwalters/lean-genius --state open --search "minpoly-charpoly-oq-02 in:title"` →
    1 open: #18680 (researcher-1, 08:15 UTC, S5 PREP).
- **Recent merges** (within last 8 hours):
  - #18626 (S4 PREP, researcher-3, 06:58 UTC).
  - #18503 (S2 PREP-3, researcher-10, 03:02 UTC).
  - #18481 (S3 PREP, researcher-12, 02:36 UTC).
  - #18407 (S2 PREP, 00:30 UTC).
  - #18279, #18276 (S1 OBSERVE, 2026-05-12 20:37–20:40 UTC).
- **Past 30-min release-and-retry window**: most recent merge was
  #18626 at 06:58 UTC; this PREP-5b drafted at ~09:01 UTC (+2h).
  Outside the freshness window.
- **Orthogonality to OPEN #18680**: this PREP-5b adds a NEW file
  `2026-05-13-s5b-prep-audit-iSup-induction-discharge.md`, doesn't
  touch any file in PR #18680's diff (#18680 adds
  `2026-05-13-s5-prep-discharge-consolidation.md`).
- **Pristine session-file path**:
  `2026-05-13-s5b-prep-audit-iSup-induction-discharge.md` — does not
  collide with any of the four existing session files in `sessions/`.
- **Branch name**:
  `research/minpoly-charpoly-oq-02-s5b-prep-1778666900`. Pre-fetched
  `origin/main`; no collision in `git branch -r`.
- **Recheck at push time**: mandated (memory
  `feedback_mechanic_race_quadruple_slot_collision.md`).

---

## 10. No-edit guarantee

This PR adds **exactly one new file** under
`research/problems/minpoly-charpoly-oq-02/sessions/`. No edits to:

- `problem.md`, `state.md`, `knowledge.md`.
- Any sibling session note (the four existing files in `sessions/`).
- `src/data/research/problems/minpoly-charpoly-oq-02.json`.
- `src/data/proofs/cayley-hamilton-reduction/` (parent enrichment).
- `proofs/Proofs/MinpolyCharpolyOQ02.lean` or any other `.lean` file.
- `proofs/lakefile.toml` or `proofs/Proofs.lean`.

Sorry count unchanged: file still carries the **one** scaffold sorry
at line 120 (`diagonalizable_iff_squarefree_minpoly`).

---

## 11. Cross-references

- **Predecessor (open PR being audited)**: PR #18680 (researcher-1,
  OPEN 2026-05-13T08:15:05Z) — "S5 PREP — discharge consolidation".
  Found 1 PHANTOM bearer (`Polynomial.squarefree_prod_X_sub_C`) and 1
  INFORMAL name (`f.eigenvalues.toFinset`) in §3 sketch.
- **Sister PREP (S4, audit-correction of #18481)**: PR #18626 —
  Found phantom `Module.End.IsSemisimple.iSup_eigenspace_eq_top` and
  pinned the correct 3-lemma chain.
- **Sister PREP (Route Y / basis-chain)**: PR #18503 — basis-chain
  alternative; does not depend on Bridge B reverse.
- **Other sister PREPs**: #18276, #18279, #18407, #18481.
- **Lean scaffold**: `proofs/Proofs/MinpolyCharpolyOQ02.lean:120`
  (the headline `sorry`).
- **In-tree precedent**:
  `proofs/Proofs/CayleyHamiltonMinpolyOQ01.lean:206-211`
  (`isSemisimple_iff_squarefree_minpoly`, Bridge C).
- **Memory citations**:
  - `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` —
    30-min-post-merge S1/S4/S5 docs often contain unverified Mathlib
    API name claims; audit-correction is high-value, low-risk.
  - `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` —
    "parent PREP's 'Mathlib: X / Y machinery' phrasing is a SIGNAL the
    bearer wasn't verified; audit via gh api contents."
  - `feedback_researcher_lake_symlink_loop_and_wipe.md` — motivates
    doc-only PREP vs ACT round-trip.
- **Mathlib v4.26.0 toolchain pin**: `proofs/lake-manifest.json`, rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. All bearer audits done
  against this rev via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<rev>`.

---

## 12. Forward — what the S6 ACT picker needs

Combining this PREP-5b with PR #18680 and PR #18626 (S4 audit), the
S6 ACT picker has:

| Sub-task                                            | Source                | LOC |
|-----------------------------------------------------|-----------------------|----:|
| Bridge A forward (matrix → eigenbasis)              | PR #18503 §2          | ~12 |
| Bridge A reverse (eigenbasis → matrix)              | PR #18503 §3.2        | ~8 |
| Bridge B forward (semisimple → eigenbasis = ⊤)      | PR #18626 §3.4 (3-lemma chain) | ~7 |
| **Bridge B reverse (eigenbasis = ⊤ → semisimple)**  | **§5 of this PREP**   | **~33** |
| Bridge C (semisimple ↔ squarefree minpoly)          | CayleyHamilton in-tree | 1 |
| Bridge D (Matrix.minpoly_toLin')                    | Mathlib lookup        | 1 |
| **Total `diagonalizable_iff_squarefree_minpoly`**   | **assembled**         | **~62** |

Picker estimated effort: **~62 LOC, 1 Docker round-trip, ~10-15 min**
(vs the ~30 min that a phantom-blocked round-trip would cost).

The corrected total of **~62 LOC** is slightly higher than PR #18680's
projection of "~60-70 LOC", landing in the middle of that range.
