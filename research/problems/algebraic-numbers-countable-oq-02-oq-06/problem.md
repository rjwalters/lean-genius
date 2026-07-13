# Problem: Solovay's theorem — ZF+DC consistent with all reals Lebesgue measurable

**Slug**: algebraic-numbers-countable-oq-02-oq-06
**Created**: 2026-07-09T16:03:15-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\operatorname{Con}(\mathsf{ZFC} + \exists \text{ inaccessible cardinal})
\;\Longrightarrow\;
\operatorname{Con}\!\bigl(\mathsf{ZF} + \mathsf{DC} + \forall A \subseteq \mathbb{R},\; A \text{ is Lebesgue measurable}\bigr)
$$

Equivalently: there is a model $M$ of $\mathsf{ZF} + \mathsf{DC}$ (the Solovay model) in which every subset of $\mathbb{R}$ is Lebesgue measurable, has the Baire property, and has the perfect set property — hence no Vitali set and no Banach–Tarski paradox exist there. The theorem is a *relative consistency* statement, proved by forcing over a ground model containing an inaccessible cardinal $\kappa$ (the Lévy collapse $\operatorname{Coll}(\omega, {<}\kappa)$ followed by passage to the sub-model $L(\mathbb{R})$ of the generic extension).

### Plain Language

The Axiom of Choice (AC) is what lets mathematicians build "pathological" sets of real numbers that cannot be assigned a length — the Vitali set is the classic example, and the Banach–Tarski paradox exploits the same freedom. Solovay proved in 1970 that if you drop AC and keep only its tame consequence *Dependent Choice* (DC, which is enough for ordinary analysis and sequences), then it is *consistent* that no such pathological set exists at all: every single subset of $\mathbb{R}$ can be measured. So non-measurable sets are not a fact of mathematics — they are an artifact of the full Axiom of Choice. Crucially, the plain fact that $\mathbb{R}$ is uncountable ($\#\mathbb{R} = \mathfrak{c}$, the result formalized in the parent gallery entry) survives untouched in Solovay's world: uncountability needs no AC, whereas non-measurability does.

### Why This Matters

- **Delineates the role of the Axiom of Choice.** Solovay's theorem is the precise dividing line between the parts of real analysis that are "AC-free" (uncountability of $\mathbb{R}$, existence of transcendentals, the entire Borel/analytic measure theory) and the parts that require the full strength of choice (Vitali non-measurable sets, Hausdorff/Banach–Tarski paradoxes, a well-ordering of $\mathbb{R}$).
- **Complements the parent uncountability proof.** The parent entry proves $\mathbb{R}$ is uncountable via cardinal arithmetic, a theorem of plain ZF. Solovay's model shows that adding "every set is measurable" does **not** collapse this — one cannot hope to turn the uncountability argument into a *measure-theoretic* pathology-free contradiction. It answers "which uncountability phenomena require AC?" with a sharp model-theoretic separation.
- **Foundational forcing result.** Together with Cohen's independence of CH (already referenced by the parent), it is one of the landmark applications of forcing, and the inaccessible-cardinal hypothesis it uses is *necessary* (Shelah 1984), making the large-cardinal calibration itself a deep theorem.
- **A grand challenge for formal mathematics.** No forcing argument of this depth has been fully formalized in Lean 4 / Mathlib; even the machinery (Lévy collapse, $L(\mathbb{R})$, random/amoeba forcing) is largely absent, so the problem is a stress test for set-theoretic formalization.

## Known Results

### What's Already Proven

- **Solovay's theorem (Solovay 1970)** — R. M. Solovay, *A model of set-theory in which every set of reals is Lebesgue measurable*, Annals of Mathematics 92 (1970), 1–56. The original result, via the Lévy collapse of an inaccessible.
- **Necessity of the inaccessible (Shelah 1984)** — S. Shelah, *Can you take Solovay's inaccessible away?*, Israel J. Math. 48 (1984), 1–47. Shows the large-cardinal hypothesis cannot be dropped for the "all sets measurable" conclusion (though it can for "all sets have the Baire property").
- **AC $\Rightarrow$ a non-measurable set exists** — Vitali's construction (a transversal of $\mathbb{R}/\mathbb{Q}$) is a theorem of ZFC; Mathlib formalizes it as `MeasureTheory.exists_nonmeasurableSet` / the Vitali set.
- **$\mathbb{R}$ is uncountable in ZF** — the parent gallery entry `algebraic-numbers-countable-oq-02` (`Cardinal.mk_real`, `Cardinal.aleph0_lt_continuum`); no choice is needed.
- **Borel and analytic sets are always measurable** (Lusin, in ZF+DC) — the "tame" part of measure theory that already holds without AC and that Solovay extends to *all* sets in his model.

### What's Still Open

- **Formalization in Lean 4 / Mathlib.** None of Solovay's argument is currently formalized: not the Lévy collapse forcing, not the construction of $L(\mathbb{R})$ in a generic extension, not the measurability transfer. This is the open engineering/mathematical problem.
- **Reusable forcing infrastructure.** Mathlib has no general forcing framework (partial orders of conditions, generic filters, the forcing relation, names, the truth/definability lemmas). Building it — or a bespoke slice sufficient for the Lévy collapse — is the prerequisite bottleneck.
- **A Mathlib theory of $L(\mathbb{R})$ and inner models.** The constructible hierarchy $L$ is not in Mathlib; $L(\mathbb{R})$ even less so.

### Our Goal

Produce a Lean 4 formalization brief and (as far as tractable) a formal *statement* of Solovay's theorem — i.e. define the objects (an inaccessible cardinal, the Lévy collapse forcing $\operatorname{Coll}(\omega,{<}\kappa)$, the sub-model $L(\mathbb{R})^{V[G]}$, "Lebesgue measurable") precisely enough to *state*

> Con(ZFC + inaccessible) → Con(ZF + DC + "all sets of reals are Lebesgue measurable")

and to lay out the proof skeleton. A complete machine-checked proof is a moonshot; a defensible intermediate target is (a) the statement + (b) the ZF-only lemmas that isolate what AC actually buys (Vitali needs AC; uncountability does not), formalized against the parent entry.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| algebraic-numbers-countable-oq-02 | Parent: $\#\mathbb{R} = \mathfrak{c} > \aleph_0$, a ZF theorem that survives in Solovay's model; this problem asks what *additional* structure (non-measurable sets) requires AC | Cardinal arithmetic (`Cardinal.mk_real`, `aleph0_lt_continuum`) |
| lebesgue-measure | Supplies the measure $\lambda$ and the notion of "Lebesgue measurable" that Solovay's model makes universal | Outer measure, Carathéodory measurability, countable additivity |
| continuum-hypothesis | Sibling forcing result (Gödel $L$ / Cohen forcing) — independence of CH is the other landmark forcing application over the same base | Forcing, inner models, generic extensions |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Formalize the statement only (calibration target).**
   Define an inaccessible cardinal, the Lévy collapse poset, generic filters (as an assumption/hypothesis rather than a constructed object), $L(\mathbb{R})$, and "every set of reals is Lebesgue measurable," then state the relative-consistency implication as a theorem about models.
   - Why it might work: statement-level formalization sidesteps building the full forcing machinery; the definitions largely exist in the literature and can be transcribed.
   - Risk: without the underlying model theory in Mathlib, the "statement" risks being vacuous or unfaithful; getting the encoding of *consistency* / *models of ZF* right in Lean is itself subtle.

2. **Approach B — Formalize the AC-isolation lemmas (ZF-only, genuinely tractable).**
   Prove in Lean, working in plain ZF (avoiding `Classical.choice` where possible / tracking its use), the two poles: (i) a well-ordering or a Vitali transversal yields a non-measurable set (uses AC); (ii) $\#\mathbb{R} = \mathfrak{c}$ and the perfect-set property for closed sets need no choice. This produces a rigorous "what AC buys" companion to the parent entry without any forcing.
   - Why it might work: Mathlib already has Vitali sets and Lebesgue measure; the novelty is the careful choice-tracking, which is checkable.
   - Risk: Mathlib is built on classical foundations (`Classical.choice` is an axiom), so "ZF-only" must be simulated by discipline/auditing rather than enforced by the kernel; partial and easy to overclaim.

3. **Approach C — Build a minimal forcing kernel and attack the Lévy collapse.**
   Develop generic filters, names, and the forcing relation for the specific poset $\operatorname{Coll}(\omega,{<}\kappa)$, then formalize the random-real / measurability transfer.
   - Why it might work: it is the only path to the *actual* theorem.
   - Risk: multi-year effort; essentially requires porting a substantial fragment of a set-theory textbook (Kunen, Jech) into Mathlib first.

### Key Difficulties

- **No forcing in Mathlib.** The single largest obstacle: generic extensions, the forcing relation, and its definability/truth lemmas do not exist and are a major project in themselves.
- **Inner models $L$ and $L(\mathbb{R})$ absent.** The target model is a sub-model of a generic extension; neither $L$ nor $L(\mathbb{R})$ is formalized.
- **Encoding relative consistency faithfully.** Statements of the form "Con(T₁) → Con(T₂)" require a Lean-level treatment of first-order theories, models, and provability — bordering on the incompleteness formalization machinery.
- **Classical foundations of Mathlib.** Distinguishing ZF from ZFC inside a library whose kernel already has `Classical.choice` requires manual axiom auditing; the DC-only flavor cannot be enforced natively.
- **Large-cardinal hypothesis.** Defining and using an inaccessible cardinal (and knowing it is necessary, per Shelah) adds set-theoretic weight not present elsewhere in the gallery.

### What Would a Proof Need?

- Key lemma 1: A Mathlib formalization of forcing — posets of conditions, generic filters over a model, names, and the forcing theorem (definability of $\Vdash$ and the truth lemma).
- Key lemma 2: The Lévy collapse $\operatorname{Coll}(\omega,{<}\kappa)$ and its homogeneity/factorization properties, plus the fact that after collapsing an inaccessible, every set of reals in $L(\mathbb{R})^{V[G]}$ is "$\infty$-Borel"/measurable (random-real absoluteness of measurability).
- Key lemma 3: DC holds in $L(\mathbb{R})^{V[G]}$ (so the target model satisfies ZF+DC).
- Technical requirements: a Lean encoding of first-order set theory, models, and relative consistency; an inaccessible-cardinal definition; and a faithful bridge from Mathlib's `MeasureTheory.MeasurableSet`/Lebesgue measure to the internal measurability of the model.

## Tractability Assessment

**Difficulty**: Moonshot

**Justification**:
- Solovay's proof is a deep forcing argument (Annals, 56 pages) requiring an inaccessible cardinal; the machinery it needs (forcing, generic extensions, $L(\mathbb{R})$, random forcing) is essentially absent from Mathlib.
- The closest formalized analogue — independence of CH — has been done only in dedicated systems (e.g. the Flypitch project in Lean 3 formalized the independence of CH), and even that required building forcing from scratch; Solovay's theorem is strictly harder (needs a large cardinal and a measurability transfer).
- Genuinely tractable *sub-targets* exist (Approach B: auditing what AC buys, leveraging Mathlib's existing Vitali set and Lebesgue measure), which is the realistic scope for this entry.

**Estimated Effort**:
- Exploration: days (survey Flypitch, Mathlib's `MeasureTheory` and cardinal libraries, decide statement encoding)
- If tractable (Approach B, AC-isolation companion + faithful statement): weeks
- If hard (full theorem, Approach C): unknown — multi-year, gated on a Mathlib forcing framework

## References

### Papers
- R. M. Solovay, *A model of set-theory in which every set of reals is Lebesgue measurable*, Annals of Mathematics 92 (1970), 1–56 — the original theorem.
- S. Shelah, *Can you take Solovay's inaccessible away?*, Israel J. Math. 48 (1984), 1–47 — necessity of the inaccessible for "all sets measurable."
- T. Jech, *Set Theory* (3rd Millennium ed., Springer 2003), Ch. 26 — textbook exposition of the Solovay model and the Lévy collapse.
- K. Kunen, *Set Theory: An Introduction to Independence Proofs* (North-Holland 1980) — standard reference for forcing and the Lévy collapse.
- J. Han and F. van Doorn, *A formal proof of the independence of the continuum hypothesis* (CPP 2020) — the Flypitch project; closest existing formalization of a forcing-based independence result (Lean 3).

### Online Resources
- https://en.wikipedia.org/wiki/Solovay_model — overview of the theorem, hypotheses, and Shelah's necessity result.
- https://flypitch.github.io/ — Flypitch project (formalized forcing / independence of CH in Lean), the natural infrastructure precedent.

### Mathlib
- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic` — Lebesgue measure on $\mathbb{R}$, the notion made universal in Solovay's model.
- `Mathlib.MeasureTheory.Constructions.NonMeasurable` (Vitali set) — the AC-dependent non-measurable set that Solovay's model eliminates.
- `Mathlib.SetTheory.Cardinal.Continuum` — `Cardinal.mk_real`, `aleph0_lt_continuum`: the ZF-provable uncountability the parent entry uses and that survives in the model.
- `Mathlib.SetTheory.Ordinal.Arithmetic` / cardinal libraries — starting point for defining inaccessible cardinals (no dedicated Solovay/forcing module exists).

## Metadata

```yaml
tags:
  - set-theory
  - real-analysis
  - cardinality
  - cantor
  - research
related_proofs:
  - algebraic-numbers-countable-oq-02
  - lebesgue-measure
  - continuum-hypothesis
difficulty: moonshot
source: user-request
created: 2026-07-09T16:03:15-07:00
```
