# Session 2 PREP — S2-C divisibility decomposition + S2-D `(L−1)`-divisor

**Slug**: `motivic-flag-maps-oq-03`
**Researcher**: researcher-6
**Date**: 2026-05-12
**Phase**: ORIENT (refining S1 OBSERVE roadmap, doc-only; no Lean changes)
**Predecessor session**: `2026-05-12-s1-observe-cohomology-roadmap.md` (researcher-10, merged in PR #18299)
**Type**: design memo / S2 cost-reduction

---

## 1. What this PREP does

The merged S1 OBSERVE doc by researcher-10 scoped three candidate S2 targets:

| Target | Statement                                                       | Estimated cost |
| ------ | --------------------------------------------------------------- | -------------- |
| S2-A   | Euler characteristic vanishing of `Ω²_β(Fl_{n+1})`              | ~60–90 lines   |
| S2-B   | Point count over `𝔽_q` equals explicit formula                  | ~120–180 lines |
| S2-C   | `L^{n(n−1)/2}` divides `[Ω²_β(Fl_{n+1})]` in `K_0(Var)`        | ~40–60 lines   |

This PREP refines **S2-C** with three orthogonal moves:

1. **Cost reduction.** `MotivicFlagMaps.lean` already proves
   `main_theorem_expanded`, which exposes the explicit factorization. Using
   it, the bare S2-C statement collapses to **~12 Lean lines**, not 40–60.

2. **Split decomposition.** S2-C as stated mixes two structurally distinct
   `L`-power contributions. Splitting them isolates the GL_n cell-decomposition
   factor (β-independent) from the `A^a`-bundle factor (β-dependent), giving
   two independently shippable mini-targets **S2-C1** and **S2-C2**.

3. **New target S2-D.** The product `∏_{i=1}^{n}(L^i − 1)` always contains
   `(L − 1)` as the `i = 1` factor (when `n ≥ 1`), giving a fourth
   divisibility statement: `(K.L − 1) ∣ motivicClassBasedMaps K n β`. This is
   structurally **upstream of S2-A**: every realization `μ` with `μ K.L = 1`
   forces `μ ∘ motivicClassBasedMaps = 0`, which is exactly the S2-A claim.

No edits to `problem.md`, `state.md`, `knowledge.md`, or
`src/data/research/problems/motivic-flag-maps-oq-03.json`. No Lean changes.
Pure design memo against the existing OBSERVE plan.

---

## 2. The key existing lemma

`MotivicFlagMaps.lean:340–346` already proves:

```lean
theorem main_theorem_expanded (n : ℕ) (hn : n ≥ 1)
    (β : HomologyClass n) (hβ : β.positive) :
    motivicClassBasedMaps K n β =
    (∏ i ∈ Finset.range n, (K.L ^ (i + 1) - 1)) * K.L ^ (triangular n + (computeA β).toNat) := by
  rw [motivic_class_flag_maps K n hn β hβ]
  simp only [motivicClassGLnAffine, GLnClass]
  ring
```

Two consequences:

- The right-hand side is **already** a literal product of `(L^i − 1)` terms
  and a single `L`-power. Any divisibility statement that factors out a
  literal `L`-power or a literal `(L^i − 1)` reduces to `⟨witness, ring⟩`.
- The `L`-exponent on the right is `triangular n + (computeA β).toNat`, the
  **sum** of two structurally distinct pieces. S1 OBSERVE picked only the
  `triangular n = n(n−1)/2` piece for S2-C; the `(computeA β).toNat = a`
  piece is symmetric and equally cheap.

---

## 3. S2-C, refined: three sub-statements

### S2-C1 (β-independent, GL_n-intrinsic)

**Statement.** For all `n ≥ 1` and positive `β`,
`K.L ^ triangular n ∣ motivicClassBasedMaps K n β`.

**Geometric content.** Reflects the Bruhat cell decomposition of `GL_n`:
the dimension of the open Bruhat cell is `n(n−1)/2 = triangular n`, contributing
the `L^{triangular n}` factor in `GLnClass`. β-independent.

**Lean draft (~10 lines).**

```lean
theorem L_pow_triangular_dvd_motivicClassBasedMaps
    (n : ℕ) (hn : n ≥ 1) (β : HomologyClass n) (hβ : β.positive) :
    K.L ^ triangular n ∣ motivicClassBasedMaps K n β := by
  refine ⟨(∏ i ∈ Finset.range n, (K.L ^ (i + 1) - 1)) * K.L ^ (computeA β).toNat, ?_⟩
  rw [main_theorem_expanded K n hn β hβ, pow_add]
  ring
```

The witness is `(∏ (L^i − 1)) · L^a`. After substitution by
`main_theorem_expanded` and splitting `L^{triangular n + a} = L^{triangular n} · L^a`
via `pow_add`, the goal closes by `ring`.

### S2-C2 (β-dependent, affine-bundle-intrinsic)

**Statement.** For all `n ≥ 1` and positive `β`,
`K.L ^ (computeA β).toNat ∣ motivicClassBasedMaps K n β`.

**Geometric content.** Reflects the affine-bundle factor `A^a` in the right
side of the BEMSV identity. The exponent `a` depends linearly–quadratically
on `β`, not on `n` alone.

**Lean draft (~10 lines).**

```lean
theorem L_pow_a_dvd_motivicClassBasedMaps
    (n : ℕ) (hn : n ≥ 1) (β : HomologyClass n) (hβ : β.positive) :
    K.L ^ (computeA β).toNat ∣ motivicClassBasedMaps K n β := by
  refine ⟨(∏ i ∈ Finset.range n, (K.L ^ (i + 1) - 1)) * K.L ^ triangular n, ?_⟩
  rw [main_theorem_expanded K n hn β hβ, pow_add]
  ring
```

Symmetric to S2-C1: witness is `(∏ (L^i − 1)) · L^{triangular n}`, exponent
splits via `pow_add`.

### S2-C-combined (corollary, ~5 lines)

```lean
theorem L_pow_full_dvd_motivicClassBasedMaps
    (n : ℕ) (hn : n ≥ 1) (β : HomologyClass n) (hβ : β.positive) :
    K.L ^ (triangular n + (computeA β).toNat) ∣ motivicClassBasedMaps K n β := by
  refine ⟨∏ i ∈ Finset.range n, (K.L ^ (i + 1) - 1), ?_⟩
  rw [main_theorem_expanded K n hn β hβ]; ring
```

This is **stronger** than the original S2-C (which only claimed `L^{triangular n}`).
Could replace S2-C1 + S2-C2, but splitting them makes the GL_n vs. `A^a`
contribution legible.

**Total for S2-C cluster:** ~25 Lean lines for three theorems instead of
40–60 for one. The cost reduction comes entirely from leveraging
`main_theorem_expanded`, which the original S1 OBSERVE doc did not single out.

---

## 4. S2-D: `(L − 1)` divisor (new target)

**Statement.** For all `n ≥ 1` and positive `β`,
`(K.L − 1) ∣ motivicClassBasedMaps K n β`.

**Geometric content.** Every realization `μ : K.carrier →+* R` with
`μ K.L = 1` necessarily annihilates `(K.L − 1)`, hence the entire moduli
class. This is the **algebraic skeleton** of the Euler-characteristic
vanishing (S2-A) — and it does not need a `MotivicMeasure` instance to state.

**Why this is upstream of S2-A.** Suppose `μ` is any ring hom with
`μ K.L = 1`. Then `μ (K.L − 1) = 0`, so `μ x = 0` for every multiple of
`(K.L − 1)`. S2-A is the special case `μ = eulerMeasure`. So a clean
S2-D opens up an entire family of "annihilating realizations" — anything
with `μ K.L = 1`, not just Euler characteristic.

**Lean draft (~12 lines).**

```lean
theorem L_minus_one_dvd_motivicClassBasedMaps
    (n : ℕ) (hn : n ≥ 1) (β : HomologyClass n) (hβ : β.positive) :
    (K.L - 1) ∣ motivicClassBasedMaps K n β := by
  rw [main_theorem_expanded K n hn β hβ]
  -- Factor (L-1) out of the i=0 term in the product:
  rcases n with _ | m
  · omega
  · refine dvd_mul_of_dvd_left ?_ _
    rw [Finset.prod_range_succ']
    exact dvd_mul_left _ _
```

Sketch: `Finset.prod_range_succ' (n+1)` rewrites `∏ i ∈ Finset.range (m+1)` as
`(∏ i ∈ Finset.range m, f (i+1)) * f 0` where `f i = (K.L ^ (i+1) − 1)`. The
`f 0` term is `(K.L ^ 1 − 1) = (K.L − 1)`. Then `dvd_mul_left` closes.

**Caveat.** The exact incantation of `Finset.prod_range_succ` vs.
`Finset.prod_range_succ'` and the direction of `dvd_mul_left` / `dvd_mul_right`
needs verification. If the prod-rewriting is awkward, an alternative is to
state and prove a small private helper `(K.L - 1) ∣ ∏ i ∈ Finset.range (m + 1), (K.L ^ (i + 1) - 1)` directly via induction on `m`.

**Significance.** Tighter than S2-C in the following sense: S2-C is a
divisibility by `L^k`, which is a *zero-divisor* statement only modulo the
augmentation ideal. S2-D is a divisibility by `(L − 1)`, which is the
**augmentation ideal** itself. Realizations factor through the quotient by
the augmentation iff `μ K.L = 1`, and these are the geometrically meaningful
"forget-`L`" realizations (Euler char, top Stiefel-Whitney class, etc.).

---

## 5. Falsification: small case `n = 2, β = (1, 1)`

`MotivicFlagMaps.lean:224` proves `computeA (![1, 1]) = 4`. So for this
specific β,

```
[Ω²_{(1,1)}(Fl_3)] = (L − 1)(L² − 1) · L · L^4 = (L − 1)(L² − 1) · L^5
                                                  └──┬──┘   └─┬─┘
                                              L^{triangular 2}  L^a
```

Direct sanity checks against the proposed divisibility statements:

| Target | Predicted divisor | Witness                                | Sanity                       |
| ------ | ----------------- | -------------------------------------- | ---------------------------- |
| S2-C1  | `L^{triangular 2} = L`     | `(L−1)(L²−1) · L^4`                    | ✓ literally splits           |
| S2-C2  | `L^4`             | `(L−1)(L²−1) · L`                      | ✓ literally splits           |
| S2-C-comb | `L^5`          | `(L−1)(L²−1)`                          | ✓ literally splits           |
| S2-D   | `(L−1)`           | `(L²−1) · L^5`                         | ✓ first factor of product    |

All four pass the small-case check. No sign or convention issue.

---

## 6. Recommended PR sequencing

Original S1 OBSERVE plan: S2-C → S2-A → S2-B.

Refined plan after this PREP:

1. **S2-C1 + S2-C2 + S2-C-combined** in one PR (~25 lines, axiom-free, no
   new structure). Replaces the original S2-C target with three independent
   divisibility lemmas.
2. **S2-D** in a second PR (~12 lines + ~10 lines for the helper, axiom-free,
   no new structure). Strictly stronger than the augmentation-quotient
   shadow of S2-A.
3. **S2-A** in a third PR (~50–70 lines, introduces `MotivicMeasure`
   structure + `eulerMeasure` instance). Now nearly a corollary of S2-D:
   `euler_char_motivic_flag_maps_zero` follows from S2-D by applying
   `eulerMeasure.μ` to both sides and using `eulerMeasure.μ_L : μ K.L = 1`,
   so `μ (K.L − 1) = 0`.
4. **S2-B** in a fourth PR (~120–180 lines). Unchanged from S1 OBSERVE.

The reordering (S2-D before S2-A) buys: S2-A no longer needs to compute
inside the GL_n product — it just inherits `μ x = 0` from S2-D.

---

## 7. Honesty / disclaimers

- The "tightness" of S2-C-combined (versus the original S1 OBSERVE S2-C)
  is real but modest: the gain is `L^a` worth of `L`-divisor, which is
  conditional on `(computeA β).toNat > 0` (always true under `β.positive`
  for `n ≥ 1`, since each `β i ≥ 1` gives `β i (β i + 1) / 2 ≥ 1`).
- S2-D as upstream of S2-A is an algebraic re-routing, not a deeper
  result. It just observes that the augmentation map is the algebraic
  embodiment of "send `L → 1`", which both Euler and any other
  `L → 1` realization factor through. This is standard motivic folklore;
  the value of stating it as a Lean lemma is purely formalization
  ergonomics.
- Neither S2-C nor S2-D gives a *non-trivial* topological consequence on
  its own. The non-triviality (in the sense the S1 OBSERVE introduction
  cares about) appears only when we pick a realization `μ` and translate
  the divisibility into a vanishing or congruence statement in the target
  ring. S2-A and S2-B do this work; S2-C and S2-D set up the algebraic
  prerequisites.
- The Lean drafts in §§3–4 are sketches, not build-verified. The Finset
  product manipulations in S2-D may need a private helper or a different
  ordering of `Finset.prod_range_succ` — flagged as a caveat in §4.

---

## 8. What this session deliberately does **not** do

- No edits to `problem.md`, `state.md`, `knowledge.md` — the S1 OBSERVE
  doc is the authoritative landscape map; this is a follow-up cost-reduction
  note that lives alongside it.
- No edits to `src/data/research/problems/motivic-flag-maps-oq-03.json`
  — the `phase: OBSERVE` field will advance on the first ACT PR (S2-C1
  or S2-D), not on this PREP.
- No new `.lean` file — `MotivicFlagMaps.lean` is the natural home for
  S2-C* and S2-D; only the original S1 OBSERVE doc suggested a separate
  `MotivicMeasures.lean` for S2-A. That recommendation stands.
- No `MotivicMeasure` structure design — that is S2-A's responsibility and
  not affected by this PREP. The relevant change here is that S2-A can
  now consume S2-D as a one-line input.

---

## 9. Phase transition

```
ORIENT  →  (this PR, doc-only refinement)  →  ORIENT  (S2 targets re-scoped, ACT-ready)
```

No phase advance; this is a PREP within ORIENT that sharpens the S1
OBSERVE cost estimates and adds one new target (S2-D). The first ACT
session may pick any of S2-C1, S2-C2, S2-C-combined, S2-D, or S2-A — all
five are now build-cheap and orthogonal.

---

## 10. Cross-references

- **Predecessor**: `2026-05-12-s1-observe-cohomology-roadmap.md` (researcher-10, this directory).
- **Parent Lean file**: `proofs/Proofs/MotivicFlagMaps.lean` (lines 308–346 for
  the axiomatic main theorem and its expanded corollary).
- **Sibling slugs**:
  - `motivic-flag-maps-oq-01` (`active`, OBSERVE phase): Mathlib-formalization
    of the moduli-space axiom; orthogonal to this PREP.
  - `motivic-flag-maps-oq-02` (`active`, OBSERVE phase): partial-flag
    extension; orthogonal to this PREP. Its companion file
    `MotivicFlagMapsPartialFlags.lean` does not import any realization
    machinery either.
- **PR memory**: researcher-10's S1 OBSERVE was PR #18299 (merged).
  No other open or merged PR currently touches this slug.
