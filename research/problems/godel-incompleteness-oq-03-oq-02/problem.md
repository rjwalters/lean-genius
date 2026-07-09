# Problem: The Abstract Lindenbaum Lemma and Independence via Opposing Completions

**Slug**: godel-incompleteness-oq-03-oq-02
**Created**: 2026-07-09T16:43:19-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall\, T : L.\mathrm{Theory},\quad T.\mathrm{IsSatisfiable} \;\Longrightarrow\; \exists\, T' \supseteq T,\ T'.\mathrm{IsComplete}
$$

$$
\text{and} \qquad \mathrm{Independent}\,T\,\varphi \;\Longleftrightarrow\; \exists\, T_1, T_2 \supseteq T,\ T_1.\mathrm{IsComplete} \wedge T_2.\mathrm{IsComplete} \wedge T_1 \models^{b} \varphi \wedge T_2 \models^{b} \neg\varphi.
$$

### Plain Language

The Lindenbaum lemma says that any consistent (satisfiable) set of axioms can be extended to a *complete* theory — one that decides every sentence, proving either it or its negation. This problem asks to establish that lemma inside Mathlib's genuine first-order model theory and then use it to give a completions-based characterization of independence: a sentence $\varphi$ is independent of a theory $T$ exactly when $T$ has two complete extensions that disagree about $\varphi$ — one that proves $\varphi$ and one that proves $\neg\varphi$. This is the "two disagreeing worlds" picture of undecidability, made precise: independence is not just a semantic quirk but the visible splitting of a theory into genuinely different maximal completions.

### Why This Matters

The parent gallery entry (godel-incompleteness-oq-03) already proves that a sentence is independent of $T$ iff both one-sentence extensions $T \cup \{\varphi\}$ and $T \cup \{\neg\varphi\}$ are satisfiable. The Lindenbaum lemma upgrades those two *satisfiable* extensions into two *complete* theories, giving the sharpest possible statement of independence: two maximal, deciding-everything worlds that split on $\varphi$. This completions view is the model-theoretic heart of every independence phenomenon — the Continuum Hypothesis being independent of ZFC (Gödel–Cohen) is exactly the existence of two ZFC-completions deciding CH oppositely. Lindenbaum's lemma is also a standard building block toward the Completeness and Compactness theorems, so formalizing it strengthens the reusable model-theory scaffolding around the incompleteness gallery cluster.

## Known Results

### What's Already Proven

- `independent_iff_satisfiable_both` — `Independent T φ ↔ IsSatisfiable (T ∪ {¬φ}) ∧ IsSatisfiable (T ∪ {φ})`, from the parent entry godel-incompleteness-oq-03 (verified, 0 axioms, 0 sorries)
- `Independent.exists_isComplete_extensions` — the parent already constructs two disagreeing complete extensions $T_1, T_2 \supseteq T$ with $T_1 \models \varphi$, $T_2 \models \neg\varphi$, $T_1 \ne T_2$, built as the complete theories `Th(M), Th(N)` of explicit models — this is the *forward* direction and a special case of what a full Lindenbaum lemma delivers (godel-incompleteness-oq-03 meta.json, originalContributions)
- `FirstOrder.Language.completeTheory.isComplete` — the complete theory of a single structure is complete (Mathlib.ModelTheory.Satisfiability)
- `FirstOrder.Language.Theory.models_iff_not_satisfiable` — the semantic Completeness Theorem, the bridge from unprovability to a model of the negation (Mathlib.ModelTheory.Satisfiability)

### What's Still Open

- The general abstract Lindenbaum lemma stated for an *arbitrary* satisfiable theory $T$ (not merely via one distinguished model): every satisfiable $T$ has *some* complete extension $T' \supseteq T$
- The full equivalence connecting independence to *arbitrary* opposing complete extensions, including the reverse direction (two disagreeing completions $\Rightarrow$ independence)
- Whether Mathlib already exposes a Lindenbaum/maximal-consistent-extension lemma directly, or whether it must be assembled from `completeTheory` of a model plus the Completeness Theorem

### Our Goal

Formalize, against Mathlib's `FirstOrder.Language.Theory`, (1) the Lindenbaum lemma — every `IsSatisfiable` theory admits a complete extension — and (2) the equivalence `Independent T φ ↔ ∃ T₁ T₂ ⊇ T, IsComplete T₁ ∧ IsComplete T₂ ∧ T₁ ⊨ᵇ φ ∧ T₂ ⊨ᵇ φ.not`, thereby extending the parent's satisfiability characterization to a completions characterization. Both should be verified with 0 sorries, matching the parent entry's standard.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| godel-incompleteness-oq-03 | Direct parent: defines `Independent T φ` over real semantics and proves `independent_iff_satisfiable_both` and `Independent.exists_isComplete_extensions` — the forward half of this problem | Mathlib first-order model theory, Completeness Theorem (`models_iff_not_satisfiable`), `completeTheory.isComplete`, model-transfer bridge |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Model-theoretic Lindenbaum via `completeTheory`**: For a satisfiable $T$, take any model $M \models T$ (from `IsSatisfiable`), then set $T' := \mathrm{Th}(M)$, the complete theory of $M$. Then $T \subseteq T'$ (every sentence of $T$ is true in $M$) and $T'$ is complete by `completeTheory.isComplete`. This is exactly the construction the parent already uses for `Independent.exists_isComplete_extensions`, so the Lindenbaum lemma generalizes that pattern.
   - Why it might work: Mathlib's `completeTheory` machinery hands over completeness for free; the parent entry already demonstrates the pattern compiles and is axiom-free.
   - Risk: Extracting a concrete model type from `IsSatisfiable` and discharging `T ⊆ Th(M)` may require careful handling of `Theory.Model` instances and universe bookkeeping.

2. **Approach B — Syntactic Zorn's-lemma Lindenbaum**: Prove the lemma the classical way: order consistent extensions of $T$ by inclusion, verify chains have consistent unions (compactness/finiteness), and apply Zorn to get a maximal consistent — hence complete — extension.
   - Why it might work: This is the textbook route and does not depend on first extracting a model; it mirrors how Mathlib proves several maximality results.
   - Risk: Requires a syntactic consistency notion and a compactness argument for unions of chains; Mathlib's model theory is semantics-first (`⊨ᵇ`), so the finitary consistency plumbing may be heavier than the model route.

### Key Difficulties

- Mathlib exposes semantic consequence `T ⊨ᵇ φ` and satisfiability rather than a syntactic proof system, so "complete extension" must be phrased via `Theory.IsComplete` and `completeTheory` of a model rather than via maximal consistent syntactic sets.
- The reverse direction (two disagreeing completions $\Rightarrow$ independence) must rule out $T$ itself deciding $\varphi$: if $T \models \varphi$ then every complete extension proves $\varphi$, so producing a completion proving $\neg\varphi$ already forces $T \not\models \varphi$ — the argument uses monotonicity of $\models^b$ under theory extension.
- Confirming which pieces Mathlib already provides (a ready-made Lindenbaum lemma vs. only `completeTheory.isComplete`) to avoid reproving library content.

### What Would a Proof Need?

- Key lemma 1: `exists_isComplete_extension` — `T.IsSatisfiable → ∃ T', T ⊆ T' ∧ T'.IsComplete`, via `Th(M)` for a model `M ⊨ T`.
- Key lemma 2: monotonicity of semantic consequence under theory extension — `T ⊆ T' → T ⊨ᵇ φ → T' ⊨ᵇ φ` (needed for the reverse direction).
- Technical requirements: comfort with `FirstOrder.Language.Theory.Model`, `completeTheory`, `models_iff_not_satisfiable`, and the parent entry's `independent_iff_satisfiable_both` to bridge satisfiable extensions to complete ones.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The parent entry already builds two disagreeing complete extensions (`Independent.exists_isComplete_extensions`) with 0 axioms and 0 sorries, so the forward direction and the core construction are demonstrably in reach.
- The generalization to an arbitrary satisfiable theory reuses `completeTheory.isComplete`, an existing Mathlib lemma, plus the already-proven `independent_iff_satisfiable_both`.
- The main new work is the reverse direction and the general Lindenbaum statement, both of which are standard model theory rather than research-grade formalization (unlike the sibling OQ-01, which needs PA arithmetization Mathlib lacks).

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1 week
- If hard: 2–3 weeks

## References

### Papers
- Marker, David — *Model Theory: An Introduction* (2002), GTM 217, Springer — standard reference for the Completeness Theorem, complete theories, and Lindenbaum's lemma, the apparatus this problem formalizes.
- The mathlib Community — *The Lean Mathematical Library: FirstOrder.Language model theory* (CPP 2020, ongoing) — supplies `Theory.IsComplete`, `completeTheory`, and `models_iff_not_satisfiable`.

### Online Resources
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/ModelTheory/Satisfiability.html — Mathlib docs for satisfiability, completeness, and complete theories.

### Mathlib
- `Mathlib.ModelTheory.Satisfiability` — `Theory.IsSatisfiable`, `Theory.IsComplete`, `completeTheory.isComplete`, `models_iff_not_satisfiable`.
- `Mathlib.ModelTheory.Semantics` — the satisfaction relation, `Sentence.realize_not`, `model_union_iff`, `model_singleton_iff`.

## Metadata

```yaml
tags:
  - logic
  - model-theory
  - incompleteness
  - independence
  - first-order-logic
  - completeness-theorem
  - godel
  - peano-arithmetic
  - verified
  - research
related_proofs:
  - godel-incompleteness-oq-03
difficulty: medium
source: open-question
created: 2026-07-09T16:43:19-07:00
```
