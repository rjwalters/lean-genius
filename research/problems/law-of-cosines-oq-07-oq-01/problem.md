# Problem: Jordan–von Neumann Converse — Parallelogram Law Implies an Inner Product

**Slug**: law-of-cosines-oq-07-oq-01
**Created**: 2026-07-01T22:11:22-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $E$ be a normed space over $\mathbb{K} \in \{\mathbb{R}, \mathbb{C}\}$ (an `RCLike` field) whose norm satisfies the parallelogram identity

$$
\forall\, x, y \in E,\qquad \lVert x+y\rVert^2 + \lVert x-y\rVert^2 = 2\bigl(\lVert x\rVert^2 + \lVert y\rVert^2\bigr).
$$

Then there exists an inner product $\langle\,\cdot\,,\,\cdot\,\rangle : E \times E \to \mathbb{K}$ making $E$ an `InnerProductSpace 𝕜 E` whose induced norm is exactly the given norm, i.e. $\lVert x\rVert = \sqrt{\operatorname{re}\langle x, x\rangle}$. Concretely, we want the packaged statement

$$
\Bigl(\forall\, x, y,\ \lVert x+y\rVert^2 + \lVert x-y\rVert^2 = 2(\lVert x\rVert^2+\lVert y\rVert^2)\Bigr)
\;\Longrightarrow\; \exists\ \text{(an inner-product structure inducing } \lVert\cdot\rVert\text{)}.
$$

In Lean this is realized by `InnerProductSpace.ofNorm`, which constructs the structure from the parallelogram hypothesis via the polarization identity.

### Plain Language

The parent entry (`law-of-cosines-oq-07`) proves the *easy* direction: every inner-product norm satisfies the parallelogram law. This problem asks for the *converse* — the deep half of the Jordan–von Neumann theorem. If a norm on a real or complex vector space happens to obey the parallelogram law, then the norm secretly comes from an inner product: we can recover that inner product from the norm alone (by the polarization formula) and check that it is genuinely bilinear, symmetric/conjugate-symmetric, and positive-definite, and that it reproduces the norm we started with. The upshot is that "satisfies the parallelogram law" and "is a Hilbert-space (inner-product) norm" are the same condition.

### Why This Matters

This is the intrinsic, coordinate-free characterization of inner-product (Hilbert-space) geometry among all normed spaces: the parallelogram law is precisely the algebraic identity that separates inner-product norms (like $\ell^2$) from all other norms (like $\ell^1$ or $\ell^\infty$, which fail it). Together with the parent entry's easy direction it closes the biconditional and completes the Jordan–von Neumann theorem, converting a classical median/parallelogram identity into a full characterization theorem. Recovering the inner product from the norm via polarization is a template used throughout functional analysis and is the reason Hilbert-space methods apply exactly when this one identity holds.

## Known Results

### What's Already Proven

- Easy direction (inner product ⟹ parallelogram law) — `law-of-cosines-oq-07` (this project) and Mathlib `parallelogram_law_with_norm` (`Mathlib/Analysis/InnerProductSpace/Basic.lean`).
- Jordan–von Neumann converse in Mathlib — `InnerProductSpace.ofNorm` in `Mathlib/Analysis/InnerProductSpace/OfNorm.lean`, tagged there as the "Fréchet–von Neumann–Jordan Theorem", together with the class `InnerProductSpaceable` and `nonempty_innerProductSpace`.
- Original theorem — P. Jordan and J. von Neumann, "On Inner Products in Linear, Metric Spaces", *Annals of Mathematics* 36 (1935).

### What's Still Open

- Packaging the converse as a clean, self-contained theorem *on top of the parent gallery entry* (which currently states only the easy direction), for both $\mathbb{K} = \mathbb{R}$ and $\mathbb{K} = \mathbb{C}$.
- Presenting the biconditional explicitly: a norm is an inner-product norm iff it satisfies the parallelogram law, tying `law-of-cosines-oq-07`'s forward direction to the `ofNorm` converse in one statement.

### Our Goal

Add a Lean theorem (extending the `law-of-cosines-oq-07` development) that takes the parallelogram-law hypothesis and produces a compatible inner product, by invoking `InnerProductSpace.ofNorm`, and record the biconditional against the parent's easy direction. Do it for `RCLike 𝕜` so both the real and complex cases are covered by a single statement.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| law-of-cosines-oq-07 | Parent: proves the easy direction (inner-product norm ⟹ parallelogram law); this problem is its converse | Apollonius/Stewart median identity, `linear_combination`, `NormedAddTorsor` |
| law-of-cosines-oq-04 | Stewart's theorem, the scalar identity of which Apollonius (hence the parallelogram law) is a special case | algebraic side-length identity, `linear_combination` |
| pythagorean-theorem | The parallelogram law generalizes Pythagoras from the right-angle case to arbitrary $x,y$ | inner-product / orthogonality computation |

## Initial Thoughts

### Potential Approaches

1. **Approach A — invoke `InnerProductSpace.ofNorm` directly**: Take the parent's parallelogram law `∀ x y, ‖x+y‖² + ‖x−y‖² = 2(‖x‖²+‖y‖²)`, massage `‖·‖²` into the `‖·‖ * ‖·‖` form that `ofNorm`'s hypothesis expects (`h : ∀ x y, ‖x+y‖*‖x+y‖ + ‖x-y‖*‖x-y‖ = 2*(‖x‖*‖x‖ + ‖y‖*‖y‖)`), and let `InnerProductSpace.ofNorm h` build the structure; conclude the biconditional by pairing with `parallelogram_law_with_norm` for the easy direction.
   - Why it might work: Mathlib already contains the entire hard construction (polarization, additivity, positivity); the only work is matching the hypothesis shape (`sq = mul_self`, `pow_two`/`sq` rewriting) and setting the `RCLike 𝕜` instance.
   - Risk: `ofNorm` is `noncomputable` and yields a *structure/instance*, not a `Prop`; packaging it as a stated theorem may require phrasing via `Nonempty (InnerProductSpace 𝕜 E)` (`nonempty_innerProductSpace`) or `InnerProductSpaceable E` to stay in `Prop`.

2. **Approach B — reconstruct via polarization by hand**: Define the candidate inner product from the norm using the polarization identity (real: $\langle x,y\rangle = \tfrac14(\lVert x+y\rVert^2 - \lVert x-y\rVert^2)$; complex: add the $i$-terms), then verify additivity in the first argument, homogeneity, conjugate symmetry, and positive-definiteness directly from the parallelogram law.
   - Why it might work: It is fully explicit and pedagogically transparent, mirroring the classical Jordan–von Neumann argument.
   - Risk: This essentially re-derives `InnerProductSpaceable.add_left` and the complex `innerProp` lemmas that Mathlib already proves; the additivity step is the delicate part and is not worth redoing unless a self-contained exposition is the point.

### Key Difficulties

- The complex ($\mathbb{C}$) polarization identity is genuinely harder than the real one: additivity of the candidate inner product requires the four-term parallelogram manipulations Mathlib does in `InnerProductSpaceable.add_left`.
- Matching `ofNorm`'s hypothesis exactly: it is stated with `‖·‖ * ‖·‖` rather than `‖·‖ ^ 2`, so the parent's `sq`/`^2` form must be rewritten (`sq`, `pow_two`, `mul_self_eq_...`) before the lemma applies.
- Staying inside `Prop` while producing a `noncomputable` instance: prefer `nonempty_innerProductSpace`/`InnerProductSpaceable` for a stated theorem, and keep the `RCLike 𝕜` typeclass so real and complex are unified.

### What Would a Proof Need?

- Key lemma 1: the parallelogram law from the parent, rewritten into the `mul_self` form `ofNorm` consumes.
- Key lemma 2: `InnerProductSpace.ofNorm` (the construction) and `parallelogram_law_with_norm` (the easy direction, for the biconditional).
- Technical requirements: `variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]`; handling of `noncomputable`; `Nonempty`/`InnerProductSpaceable` packaging.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The hard mathematics (polarization construction, additivity, positive-definiteness) is already fully formalized in Mathlib as `InnerProductSpace.ofNorm`, so the task is largely a wrapper: adjust the hypothesis shape and instantiate.
- Similar "invoke the packaged Mathlib theorem after adjusting the statement form" tasks in this gallery are routinely completed quickly (the parent entry itself is a thin packaging of a Mathlib Euclidean-geometry lemma).
- Available Mathlib tools: `InnerProductSpace.ofNorm`, `InnerProductSpaceable`, `nonempty_innerProductSpace`, `parallelogram_law_with_norm`.

**Estimated Effort**:
- Exploration: a few hours (confirm hypothesis shape and `Prop` packaging).
- If tractable: 1–2 days including gallery integration and the biconditional statement.
- If hard: unlikely; the fallback (hand polarization) is Medium, not open-ended.

## References

### Papers
- P. Jordan and J. von Neumann, "On Inner Products in Linear, Metric Spaces", *Annals of Mathematics* 36 (1935) — original proof that the parallelogram law characterizes inner-product norms.

### Online Resources
- https://math.stackexchange.com/questions/21792/norms-induced-by-inner-products-and-the-parallelogram-law — statement and elementary proof of the converse (cited in the Mathlib source module docstring).

### Mathlib
- `Mathlib/Analysis/InnerProductSpace/OfNorm.lean` — provides `InnerProductSpace.ofNorm` (the Fréchet–von Neumann–Jordan converse), the class `InnerProductSpaceable`, and `nonempty_innerProductSpace`.
- `Mathlib/Analysis/InnerProductSpace/Basic.lean` — provides `parallelogram_law_with_norm` (the easy direction).

## Metadata

```yaml
tags:
  - analysis
  - functional-analysis
  - parallelogram-law
  - inner-product
  - jordan-von-neumann
related_proofs:
  - law-of-cosines-oq-07
  - law-of-cosines-oq-04
  - pythagorean-theorem
difficulty: low
source: gallery-gap
created: 2026-07-01T22:11:22-07:00
```

**Significance**: 6/10
**Tractability**: 7/10
