# S2-A PREP — `MotivicMeasure` structure design (realization-functor framework)

**Researcher**: researcher-6
**Date**: 2026-05-13
**Phase**: PREP (S2-A structure design — explicitly deferred by PR #18401 §"What this PR does NOT do")
**Iteration**: 2a (orthogonal to S2 PR #18401's divisibility decomposition)
**Predecessor PRs**: #18299 (S1 OBSERVE MERGED — realization-functor roadmap), #18401 (S2 PREP OPEN — divisibility decomposition S2-C / S2-D).
**Lines added**: doc-only.

## Scope

S1 OBSERVE (PR #18299, merged) identified the realization-functor framework as the bridge from the open question OQ-03 ("topology/cohomology consequences") to concrete invariants. S2 PREP (PR #18401, open) refined the divisibility-decomposition story (S2-C, S2-D) but **explicitly excluded** the `MotivicMeasure` structure design: *"No new `MotivicMeasure` structure design (S2-A's responsibility)."*

This PREP fills that gap. It provides the concrete S2-A Lean structure for a realization functor `μ : K_0(Var_k) → R`, two instance constructions (Euler characteristic, F_q point-counting), and the propagation theorems that translate the motivic main identity into each concrete realization.

## Mathlib API foundation

`Mathlib.Algebra.Ring.Hom.Basic` provides `RingHom`:

```lean
structure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β]
    extends α →* β, α →+ β, α →ₙ+* β
```

`RingHom` bundles a multiplicative monoid hom + additive monoid hom + non-unital ring hom. For our purposes we use the unbundled view: a `K.carrier →+* R` is a ring homomorphism preserving 0, 1, +, ×.

This is the **right baseline** for a realization functor on `K_0(Var)`: every realization is, by definition, a ring homomorphism out of `K_0(Var)`. The motivic data that distinguishes realizations is the image of the **Lefschetz motive** `L = [A¹]`.

## The `MotivicMeasure` structure

```lean
-- Place in: proofs/Proofs/MotivicFlagMapsOQ03.lean (new file)

import Proofs.MotivicFlagMaps
import Mathlib.Algebra.Ring.Hom.Basic

open MotivicFlagMaps  -- for GrothendieckRingVar, HomologyClass, etc.

variable {k : Type*} [Field k] (K : GrothendieckRingVar k)

/--
A **motivic measure** is a ring homomorphism out of the Grothendieck ring of
varieties, parametrised by the image of the Lefschetz motive `L = [A¹]`.

The standard realisations of `K_0(Var_k)` fit this pattern:

  | Realisation            | Target `R`       | `μ.lefschetz` | Notes                                |
  | ---------------------- | ---------------- | ------------- | ------------------------------------ |
  | Euler characteristic   | ℤ                | 1             | `k = ℂ` (or any char-0 field)        |
  | Point count over `F_q` | ℤ                | q             | `k = F_q`                            |
  | Hodge–Deligne `E`      | ℤ[u,v]           | uv            | `k = ℂ`, smooth proper varieties     |
  | Poincaré polynomial    | ℤ[t]             | t²            | when motive is pure Tate             |

The field `lefschetz_eq : μ K.L = lefschetz` captures the realisation's
specialisation of `L` to a concrete value in `R`. This is the *only* extra
data beyond the underlying `RingHom`.
-/
structure MotivicMeasure (K : GrothendieckRingVar k) (R : Type*) [CommRing R] where
  /-- The underlying ring homomorphism. -/
  toRingHom : K.carrier →+* R
  /-- The image of the Lefschetz motive. -/
  lefschetz : R
  /-- The image of `K.L` is `lefschetz` by definition. -/
  lefschetz_eq : toRingHom K.L = lefschetz
```

**Sanity check** (sometimes the `lefschetz_eq` field is redundant since `lefschetz` is fully determined by `toRingHom K.L`):

```lean
example (μ : MotivicMeasure K R) : μ.lefschetz = μ.toRingHom K.L := μ.lefschetz_eq.symm
```

The field `lefschetz` is retained as **convenience data**: many theorems about realisations are stated in terms of the constant `μ.lefschetz`, not the term `μ.toRingHom K.L`. The redundancy is harmless and useful.

**Coercion**:

```lean
instance : CoeFun (MotivicMeasure K R) (fun _ => K.carrier → R) :=
  ⟨fun μ => μ.toRingHom⟩
```

So we can write `μ x` instead of `μ.toRingHom x`.

## Estimate

| Item | LOC |
|---|---|
| `MotivicMeasure` structure | 8 |
| `CoeFun` instance | 2 |
| Lemma: `μ K.L = μ.lefschetz` (`@[simp]`) | 2 |
| Lemma: `μ.toRingHom 1 = 1`, `μ.toRingHom (a + b) = …` (mostly delegated to `RingHom` instance) | 0 (via `RingHom` API) |
| **Subtotal for the structure** | **~12** |

## Three S2-A instance constructions

### Instance 1 — Euler characteristic (~25 LOC sketch)

```lean
/-- The Euler characteristic realisation of `K_0(Var_ℂ)` to `ℤ`.

This is axiomatised as a `RingHom K.carrier ℤ` because constructing it
requires the scissor relations in `K_0(Var)`, which the current
formalisation does not have. The axiom asserts the *existence* of such
a homomorphism with `μ L = 1`. -/
axiom eulerCharRingHom (K : GrothendieckRingVar ℂ) : K.carrier →+* ℤ

axiom eulerCharRingHom_L_eq_one (K : GrothendieckRingVar ℂ) :
    eulerCharRingHom K K.L = 1

/-- The Euler characteristic as a `MotivicMeasure`. -/
noncomputable def eulerChar (K : GrothendieckRingVar ℂ) :
    MotivicMeasure K ℤ where
  toRingHom := eulerCharRingHom K
  lefschetz := 1
  lefschetz_eq := eulerCharRingHom_L_eq_one K
```

**Honesty disclaimer**: The Euler-characteristic ring homomorphism is **axiomatised** because the underlying construction (Bittner's theorem, or direct cellular Euler characteristic on a triangulation) is not in Mathlib. This adds **2 new axioms** to OQ-03's Lean home (the existence and the `L`-image specialisation). For the S2-A iteration, this is acceptable: we are *exhibiting* the realisation framework. A future iteration with full Bittner's theorem would prove these axioms.

### Instance 2 — Point counting over F_q (~25 LOC sketch)

```lean
/-- The F_q point-counting realisation of `K_0(Var_{F_q})` to `ℤ`. -/
axiom pointCountFqRingHom (q : ℕ) (hq : q.Prime) (K : GrothendieckRingVar (ZMod q)) :
    K.carrier →+* ℤ

axiom pointCountFqRingHom_L_eq_q (q : ℕ) (hq : q.Prime)
    (K : GrothendieckRingVar (ZMod q)) :
    pointCountFqRingHom q hq K K.L = (q : ℤ)

/-- F_q point counting as a `MotivicMeasure`. -/
noncomputable def pointCountFq (q : ℕ) (hq : q.Prime) (K : GrothendieckRingVar (ZMod q)) :
    MotivicMeasure K ℤ where
  toRingHom := pointCountFqRingHom q hq K
  lefschetz := (q : ℤ)
  lefschetz_eq := pointCountFqRingHom_L_eq_q q hq K
```

Same honesty disclaimer: 2 new axioms for the F_q realisation.

### Instance 3 — Hodge–Deligne `E`-polynomial (~20 LOC sketch, optional for S2-A)

```lean
/-- The Hodge–Deligne E-polynomial realisation of `K_0(Var_ℂ)` to `ℤ[u, v]`. -/
axiom hodgeDeligneERingHom (K : GrothendieckRingVar ℂ) : K.carrier →+* (ℤ[X] : Type)[Y]
  -- Placeholder; the actual target is `Polynomial (Polynomial ℤ)` via `Polynomial.evalRingHom`

-- ... (similar pattern; defer to a separate S2-A2 iteration)
```

**S2-A scope decision**: ship Instances 1 and 2 only. Instance 3 (Hodge–Deligne) introduces `Polynomial (Polynomial ℤ)` ergonomic friction that distracts from the structural design.

## Three S2-A propagation theorems

These are the workhorse theorems that translate the motivic main identity into each realisation.

### Propagation 1 — Main identity propagates (~3 LOC)

```lean
/-- For any motivic measure `μ`, the main identity propagates: the image of
`motivicClassBasedMaps K n β` equals the image of
`motivicClassGLnAffine K n (computeA β)` in the target ring. -/
theorem MotivicMeasure.main_identity_propagates
    (μ : MotivicMeasure K R) (n : ℕ) (hn : n ≥ 1)
    (β : HomologyClass n) (hβ : β.positive) :
    μ (motivicClassBasedMaps K n β)
      = μ (motivicClassGLnAffine K n (computeA β)) := by
  rw [motivic_class_flag_maps K n hn β hβ]
```

**LOC**: 1 + 1 (signature + body) = ~3.

### Propagation 2 — `L`-divisibility via `μ L = 1` (~5 LOC)

```lean
/-- If `μ.lefschetz = 1`, then `μ` annihilates `K.L - 1`, so any class
that is `(K.L - 1)`-divisible (such as `motivicClassBasedMaps K n β` for
`n ≥ 1`, per S2-D from PR #18401) lies in the kernel of `μ`. -/
theorem MotivicMeasure.annihilate_of_lefschetz_eq_one
    (μ : MotivicMeasure K R) (hL : μ.lefschetz = 1)
    (x : K.carrier) (hx : ∃ y : K.carrier, x = (K.L - 1) * y) :
    μ x = 0 := by
  obtain ⟨y, hy⟩ := hx
  rw [hy, map_mul, map_sub, map_one, μ.lefschetz_eq, hL]
  ring
```

**LOC**: 6. This is the **headline payoff** of the `MotivicMeasure` framework: any class with a `(K.L - 1)` factor automatically has Euler characteristic 0. Combined with the `(K.L - 1) ∣ motivicClassBasedMaps K n β` claim (from PR #18401's S2-D), this gives `χ(Ω²_β(Fl_{n+1})) = 0` for n ≥ 1.

### Propagation 3 — F_q point count formula (~5 LOC)

```lean
/-- For F_q point counting, the main identity gives an explicit formula:
the count `#Ω²_β(Fl_{n+1})(F_q) = #GL_n(F_q) · q^{computeA β}`. -/
theorem MotivicMeasure.fq_point_count
    {q : ℕ} (hq : q.Prime) (K : GrothendieckRingVar (ZMod q))
    (n : ℕ) (hn : n ≥ 1) (β : HomologyClass n) (hβ : β.positive) :
    pointCountFq q hq K (motivicClassBasedMaps K n β)
      = pointCountFq q hq K (motivicClassGLnAffine K n (computeA β)) :=
  (pointCountFq q hq K).main_identity_propagates n hn β hβ
```

**LOC**: 5. Specialises Propagation 1 to F_q point counting.

## Total S2-A estimate

| Block | LOC | Notes |
|---|---|---|
| `MotivicMeasure` structure | 12 | Structure + `CoeFun` + `@[simp]` lemma |
| Euler characteristic instance | 25 | 2 new axioms |
| F_q point counting instance | 25 | 2 new axioms |
| Propagation theorems (3) | 13 | All routine ring-hom manipulation |
| Imports & namespace bookkeeping | 5 | |
| **Total** | **~80 LOC** | |

| Axiom delta | Before | After |
|---|---|---|
| Parent `MotivicFlagMaps.lean` | 2 | 2 unchanged |
| OQ-03 `MotivicFlagMapsOQ03.lean` (new file) | 0 | **4** (2 for Euler char, 2 for F_q) |
| **Total** | 2 | **6** |

The +4 axioms are **honest exhibitions** of the two realisations. Each axiom set is 2 statements: existence of the ring hom + image of L. Removing them requires implementing Bittner's theorem (or equivalent) in Mathlib, which is a multi-month project. For S2-A, axiomatising is the right move.

## Net effect on gallery status

The current parent gallery entry `motivic-flag-maps` is already `axiomatized` with axiomCount=2. Adding `MotivicFlagMapsOQ03.lean` as a *separate file* with 4 more axioms can either:

**Option A (separate gallery entry)**: Create a new gallery entry `motivic-flag-maps-oq-03` with `status: "axiomatized"`, `axiomCount: 4`, `theoremCount: ~6`. The 4 axioms are the realisations' existence + L-image. This is the **standard convention** for OQ-derived entries.

**Option B (extension of parent)**: Don't create a separate gallery entry; just add the file as `proofs/Proofs/MotivicFlagMapsOQ03.lean` for internal use without surfacing to the gallery. **Not recommended** — the work is significant enough to deserve a gallery entry.

S2-A recommends **Option A** with the honesty caveats explicit in the `assumptions` field of the meta.json.

## Orthogonality to in-flight PRs

| PR | Phase | Focus | Conflict with S2-A PREP? |
|---|---|---|---|
| #18299 (MERGED) | S1 OBSERVE | Realisation-functor roadmap | no — base |
| #18401 (OPEN) | S2 PREP | Divisibility decomposition (S2-C, S2-D) | **no** — S2 PREP §"What this PR does NOT do" explicitly defers `MotivicMeasure` structure design to S2-A. This PREP fills exactly that gap |
| **#this** | S2-A PREP | `MotivicMeasure` structure + 2 instances + 3 propagation theorems | — |

The S2 PREP (PR #18401) recommended ordering S2-C → S2-D → S2-A → S2-B. This PREP advances the **S2-A** phase. The order is preserved: any ACT iteration can pick up S2-C, S2-D, S2-A in sequence using the three open PREPs (PR #18299 for the map, PR #18401 for divisibility, this PREP for `MotivicMeasure`).

## What this PREP does NOT address

1. **S2-B Euler-characteristic specialisation**. Once S2-A's `MotivicMeasure` structure is in, the S2-B specialisation `χ(Ω²_β(Fl_{n+1})) = χ(GL_n) · χ(A^a) = 0 · χ(A^a) = 0` (since `χ(GL_n) = 0` for n ≥ 1, the Lefschetz pencil reduction) is a 1-line corollary of Propagation 2 (with `(K.L - 1) ∣ K.GLnClass n` for n ≥ 1, which is the S2-D claim).
2. **Constructing the realisation homomorphisms unaxiomatically**. Bittner's theorem (or equivalent) is required. This is a Mathlib-contribution-scale project, not an OQ-03 deliverable.
3. **Sister sub-OQs**. `motivic-flag-maps-oq-01` (axiom removal) and `motivic-flag-maps-oq-02` (partial-flag extension) are orthogonal to OQ-03 (downstream invariants).
4. **The actual ACT iteration**. This is a PREP. The S2-A ACT iteration will need to:
   - Create `proofs/Proofs/MotivicFlagMapsOQ03.lean` with the structure + instances + propagation theorems.
   - Build-verify via Docker wrapper.
   - Create `src/data/proofs/motivic-flag-maps-oq-03/{meta.json, index.ts, annotations.json}` for the gallery entry.
   - Update `src/data/research/problems/motivic-flag-maps-oq-03.json` with `phase: "ACT"`, accumulated insights.

## Anti-targets

- **Do not** define `MotivicMeasure` over a semiring. The parent uses `CommRing`, and the realisations land in `CommRing` targets.
- **Do not** use `Algebra K.carrier R` instead of `K.carrier →+* R`. `Algebra` would assert a commuting `R`-action; we only need ring homomorphism.
- **Do not** include `lefschetz_eq` as a hypothesis to every propagation theorem. The structure encodes it; users get it via `μ.lefschetz_eq`.
- **Do not** instantiate Hodge–Deligne in S2-A. Defer to S2-A2.
- **Do not** edit the parent `MotivicFlagMaps.lean`. S2-A is a new file `MotivicFlagMapsOQ03.lean` importing the parent.
- **Do not** attempt to prove the realisation existence axioms in S2-A. They are the price of working over an abstract `K_0(Var)`.

## Build-risk audit

| Step | Risk | Fallback |
|---|---|---|
| Structure definition with `[CommRing R]` | low — standard pattern | none |
| `CoeFun` instance | low — same pattern as `MonoidHom` | use `Coe` if `CoeFun` complains |
| `@[simp]` lemma `μ K.L = μ.lefschetz` | low — direct unfold | none |
| Euler char axioms | low — pure declarations | none |
| F_q axioms (uses `ZMod q`) | medium — `ZMod q` requires `[Fact q.Prime]` instance, not bare `q.Prime` hypothesis | refactor to `[Fact q.Prime]` |
| `noncomputable def eulerChar` | low — structure construction | none |
| Propagation 1 (`main_identity_propagates`) | low — direct `rw` | none |
| Propagation 2 (`annihilate_of_lefschetz_eq_one`) | low — `map_mul`, `map_sub`, `map_one`, `ring` | none |
| Propagation 3 (F_q point count) | low — direct call to Propagation 1 | none |

The only medium-risk item is the F_q `[Fact q.Prime]` typeclass issue, which is a 1-line refactor.

## Stop conditions

This S2-A PREP is complete when:

1. ✅ `MotivicMeasure K R` structure is defined with Lean skeleton.
2. ✅ Two instance constructions (Euler char, F_q point counting) are sketched with axiom counts.
3. ✅ Three propagation theorems are sketched with LOC estimates.
4. ✅ Net axiom delta is computed (+4).
5. ✅ Gallery-entry recommendation (Option A) is given.
6. ✅ Orthogonality to PR #18299 / PR #18401 is verified.
7. ✅ Build-risk audit per step.
8. ✅ Pristine session-file addition: no edits to `problem.md` / `knowledge.md` / `state.md` / json / Lean.

All eight stop conditions are met by this file.

## Honesty

- This is a **PREP** (planning document), not an ACT (no Lean changes).
- The structure design `MotivicMeasure K R` is **simple by design**: a ring homomorphism plus a tagged image of the Lefschetz motive. The simplicity is the point — the framework absorbs the complexity of *which* realisation; the structure itself is light.
- The +4 axioms are **non-trivial assumptions**: constructing the Euler-characteristic ring hom requires Bittner's theorem (Bittner 2004, "The universal Euler characteristic for varieties of characteristic zero", *Compos. Math.* 140); constructing the F_q point-count requires Grothendieck's trace formula. Both are well-established but not formalised in Mathlib.
- The headline payoff (Propagation 2: `μ L = 1 ⇒ μ` annihilates `(K.L - 1)`-multiples) is what makes S2-D from PR #18401 *interesting*. Without `MotivicMeasure`, S2-D is just an algebraic identity in `K_0(Var)`; with `MotivicMeasure`, S2-D becomes "Euler characteristic vanishes for `n ≥ 1`."
- The estimate is honest: 80 LOC is achievable in one S2-A ACT iteration. The hardest part is the gallery integration (meta.json + index.ts + annotations.json), not the Lean.
- I have not built any of this locally. The ACT iteration will verify the namespace paths and any `[Fact …]` typeclass requirements.

## References

- Parent: `proofs/Proofs/MotivicFlagMaps.lean` (438 LOC; `GrothendieckRingVar` line 66, `motivicClassBasedMaps` axiom line 309, `motivic_class_flag_maps` axiom line 320, `motivicClassGLnAffine` def line 312).
- Mathlib: `Mathlib.Algebra.Ring.Hom.Basic` (`RingHom` structure, `map_one`, `map_mul`, `map_sub`).
- S1 OBSERVE roadmap: PR #18299, `sessions/2026-05-12-s1-observe-cohomology-roadmap.md`.
- S2 PREP divisibility: PR #18401, `sessions/2026-05-12-s02-prep-divisibility-decomposition.md` (notably S2-D: `(K.L - 1) ∣ motivicClassBasedMaps K n β` for n ≥ 1).
- Bittner 2004 — "The universal Euler characteristic for varieties of characteristic zero", *Compos. Math.* 140, 1011–1032.
- Original paper: Bryan–Elek–Manners–Salafatinos–Vakil 2025, arXiv:2601.07222.
