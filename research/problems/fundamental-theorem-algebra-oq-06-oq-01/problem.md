# Problem: Odd-Degree Polynomials over Real-Closed Fields Have a Root

**Slug**: fundamental-theorem-algebra-oq-06-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $R$ be a real-closed field. Then every polynomial $p \in R[X]$ of odd degree has a root in $R$:

$$
\deg p \text{ odd} \;\Longrightarrow\; \exists\, x \in R,\ p(x) = 0.
$$

This generalizes the parent entry's result — every odd-degree polynomial over $\mathbb{R}$ has a real root — from $\mathbb{R}$ to an arbitrary real-closed field.

### Plain Language

Over the real numbers, an odd-degree polynomial must cross zero because it goes from $-\infty$ to $+\infty$ (the intermediate value theorem). Real-closed fields are exactly the ordered fields that behave like $\mathbb{R}$ for the purposes of algebra: they have an order in which every positive element is a square and every odd-degree polynomial has a root. This problem asks to formalize the odd-degree root property in the abstract real-closed setting, rather than relying on the analytic IVT specific to $\mathbb{R}$. In Mathlib the property may hold by definition of `IsRealClosed`, in which case the task is to state it cleanly and connect it to the parent's analytic $\mathbb{R}$-proof as the motivating special case.

### Why This Matters

Real-closed fields (Artin–Schreier theory) are the algebraic abstraction behind the reals, central to model theory (real closed fields are an o-minimal, decidable theory), real algebraic geometry, and the Tarski–Seidenberg principle. Separating the *algebraic* odd-degree root property from the *analytic* IVT clarifies exactly what input the fundamental theorem of algebra needs, and gives a reusable bridge between the gallery's analytic FTA entries and Mathlib's `IsRealClosed`/`RealClosedField` API.

## Known Results

### What's Already Proven

- Parent `fundamental-theorem-algebra-oq-06` (verified): every odd-degree real polynomial has a real root (via the IVT over $\mathbb{R}$).
- Mathlib: real-closed field machinery (`IsRealClosed`, ordered-field square/odd-degree-root axioms), `Polynomial.degree`, `Polynomial.roots`, and the Artin–Schreier development underpinning `Complex` algebraic closure.
- Classical: the Artin–Schreier characterization — an ordered field is real-closed iff positives are squares and odd-degree polynomials have roots.

### What's Still Open

- A Lean statement `∀ (R) [IsRealClosed R] (p : R[X]), Odd p.degree → ∃ x, p.eval x = 0`, and its identification with the defining property (or its derivation from the chosen Mathlib definition).
- The explicit connection back to the parent's $\mathbb{R}$ instance as the canonical example.

### Our Goal

State the odd-degree root property over a real-closed field, prove it from Mathlib's `IsRealClosed` definition (extracting it if it is an axiom, or deriving it from the square/sign-change axioms otherwise), and exhibit $\mathbb{R}$ as an instance recovering the parent result.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fundamental-theorem-algebra-oq-06 | Direct parent; odd-degree real root via IVT | intermediate value theorem |
| fundamental-theorem-algebra-oq-01 | Root entry; FTA over $\mathbb{C}$ | algebraic closure |

## Initial Thoughts

### Potential Approaches

1. **Extract from the `IsRealClosed` definition.** If Mathlib defines real-closed fields with the odd-degree-root axiom (or proves it as a theorem), state the result and discharge it directly, then provide the $\mathbb{R}$ instance.
   - Why it might work: real-closedness is *defined* to include this property in most developments; the work is locating the exact Mathlib lemma and aligning the `degree`/`Odd` phrasing.
   - Risk: Mathlib's chosen axiomatization may phrase real-closedness differently (e.g. via `Complex`-style algebraic closure of $R[i]$), requiring a short derivation.

2. **Artin–Schreier derivation.** If only the square/sign axioms are given, derive the odd-degree root property by induction on degree using sign changes of $p$ between large $\pm$ arguments (an algebraic IVT via the order).
   - Why it might work: mirrors the standard Artin–Schreier proof and stays purely algebraic.
   - Risk: formalizing the order-theoretic sign-change argument abstractly is more involved than reusing a packaged Mathlib result.
