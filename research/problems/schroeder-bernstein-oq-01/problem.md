# Problem: Categorical Characterization of the Schroeder-Bernstein Property

**Slug.** `schroeder-bernstein-oq-01`
**Parent.** `schroeder-bernstein` (Wiedijk #25, `Proofs/SchroederBernstein.lean`, 198 LOC, verified, 0 sorries, 0 axioms).
**Source open question.** `meta.openQuestions[0]` of the parent gallery entry:
> Can the Schroeder-Bernstein property be characterized categorically?
> Banaschewski and Brummer (1986) showed it holds in categories with a
> 'retraction condition', but a complete characterization remains open.

## Formal statement

Let $\mathcal{C}$ be a (locally small) category. Say $\mathcal{C}$ has the
**Schroeder-Bernstein property** (SBP) iff for every pair of objects
$X, Y \in \mathrm{Ob}(\mathcal{C})$,

$$
\bigl(\exists\, m : X \hookrightarrow Y \text{ mono}\bigr) \wedge
\bigl(\exists\, n : Y \hookrightarrow X \text{ mono}\bigr)
\;\Longrightarrow\; X \cong Y.
$$

Classical fact (Bernstein 1898): $\mathbf{Set}$ has SBP.
Classical failure (Bumby 1965 for groups; Gowers 1996 for separable Banach
spaces): many concrete categories lack SBP.

**OQ-01.** Identify a "minimal" categorical hypothesis $\Phi(\mathcal{C})$
such that $\Phi(\mathcal{C}) \Rightarrow \mathcal{C}$ has SBP. Banaschewski–
Brummer (1986) gave one sufficient condition (a "retraction"/split-mono
hypothesis). A complete characterization (necessary + sufficient axioms)
remains open in the categorical-foundations literature.

## Mathlib infrastructure map

| Lemma / class | Module | Use |
|---|---|---|
| `CategoryTheory.Category` | `Mathlib.CategoryTheory.Category.Basic` | object-of-discourse |
| `CategoryTheory.Mono` | `Mathlib.CategoryTheory.EpiMono` | monomorphism predicate |
| `CategoryTheory.SplitMono` | `Mathlib.CategoryTheory.EpiMono` | "section" (retraction-condition primitive) |
| `CategoryTheory.Iso` | `Mathlib.CategoryTheory.Iso` | conclusion of SBP |
| `Function.Embedding.antisymm` | `Mathlib.SetTheory.Cardinal.SchroederBernstein` | concrete proof that `Type` has SBP |

**Mathlib gap.** No definition `class HasSchroederBernsteinProperty` exists.
No theorem of the form `[Category C] [SplitMonoCondition C] → HasSBP C`.

## Decomposition into tractable S2 / S3 / S4 steps

### S2 (ACT, target 1 file, ~80 LOC): scaffold a Lean definition

Create `proofs/Proofs/SchroederBernsteinOQ01.lean` with:

```lean
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Iso

namespace SchroederBernsteinOQ01
open CategoryTheory

/-- A category has the **Schroeder-Bernstein property** (SBP) iff every
pair of mutually monic objects is isomorphic. -/
def HasSBP (C : Type*) [Category C] : Prop :=
  ∀ X Y : C, (∃ m : X ⟶ Y, Mono m) → (∃ n : Y ⟶ X, Mono n) → Nonempty (X ≅ Y)

end SchroederBernsteinOQ01
```

### S3 (ACT): concrete witnesses

1. `Type u` has SBP — bridge to `Function.Embedding.antisymm`.
2. Counter-example in `Grp` (groups): the pair $\mathbb{Z}$ and
   $\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}$ have mutual injective homs
   but are non-isomorphic. (Witness existence; classical.)

### S4 (ACT): retraction condition (Banaschewski–Brummer)

State the hypothesis "every mono is a split mono" as a class
`HasSplitMonos C := ∀ X Y (m : X ⟶ Y), Mono m → SplitMono m`, then prove
`HasSplitMonos C → HasSBP C`. The proof reduces to (a) extracting the
sections, (b) showing the composition $s \circ s' : X \to X$ is iso via
mutual sections, (c) lifting to $X \cong Y$.

### S5+ (ANALYSIS / FUTURE): full characterization

Survey the strict generalizations: Trnková 1975 (SBP in concrete
categories), Cantor-Bernstein in toposes (Hyland?), Pradic–Brown (2019)
constructive equivalences. Identify whether a complete characterization
is feasible in Mathlib or merely a "best-known sufficient condition" goal.

## Existing parent connection

The parent file `Proofs/SchroederBernstein.lean` already provides:
- `schroeder_bernstein` (function form)
- `schroeder_bernstein_embedding` (embedding form)
- `schroeder_bernstein_equiv` (equivalence form)
- `cardinal_antisymm` (cardinal form)
- `schroeder_bernstein_set` (set form)

OQ-01 adds a **categorical** form. Cross-reference from `mainTheorems`
and `crossReferences[]` of the parent's `meta.json` deferred to S2/S3 PRs.
