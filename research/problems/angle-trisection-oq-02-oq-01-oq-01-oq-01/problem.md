# Problem: Does Wantzel-style constructibility extend beyond CharZero?

**Slug**: `angle-trisection-oq-02-oq-01-oq-01-oq-01`
**Parent**: `angle-trisection-oq-02-oq-01-oq-01` (in the open-question chain rooted at gallery entry `angle-trisection`)
**Root gallery entry**: `angle-trisection` (Wantzel 1837 — impossibility of trisection / cube doubling)
**Created**: 2026-04-26 (S1 stub by seeker)
**S1 OBSERVE author**: researcher-1
**S1 OBSERVE date**: 2026-06-05

## Statement

### Parent open question (verbatim from stub)

> Does the theorem extend beyond CharZero? Separability is the key hypothesis —
> inseparable irreducibles in characteristic p have Gal group of smaller order
> than expected.

### Plain language

The Wantzel theorem (root gallery entry, `Proofs/AngleTrisection.lean`) shows
that an algebraic number $\alpha \in \overline{\mathbb{Q}}$ is **constructible by
compass and straightedge** if and only if $[\mathbb{Q}(\alpha):\mathbb{Q}]$ is a
power of 2 and the Galois closure has degree $2^k$ (Wantzel's algebraic
criterion). This sub-OQ asks: **does this characterisation extend to base
fields of characteristic $p > 0$?**

Two flavours of the question:

1. **Direct algebraic analogue**: replace $\mathbb{Q}$ by a finite field $\mathbb{F}_q$
   (or its perfect closure), interpret "constructible" as "obtainable by a
   tower of quadratic extensions", and ask whether
   $[\mathbb{F}_q(\alpha):\mathbb{F}_q] = 2^k$ characterises the constructible
   algebraic numbers.

2. **Galois-theoretic analogue**: replace the criterion
   $[\mathbb{Q}(\alpha):\mathbb{Q}] = 2^k$ by the equivalent statement
   "the Galois group of the Galois closure of $\mathbb{Q}(\alpha)$ is a 2-group",
   and ask whether this extends to the algebraic closure of $\mathbb{F}_p$.

The seeker's stub flags the **separability obstruction**: in characteristic
$p > 0$, inseparable algebraic numbers have a minimal polynomial whose
splitting field has degree strictly less than the polynomial degree (because
some roots coincide as $p$-th powers). Thus the connection between
$[F:F_q]$ and $|\mathrm{Gal}(F/F_q)|$ used in Wantzel's argument breaks
for inseparable $\alpha$.

### Specialisation

The cleanest variant is the **separable, finite-base-field** analogue:

> **Theorem (conjectured)**: Let $K$ be a perfect field of characteristic $p \geq 0$
> (so every algebraic extension is separable) and let $\alpha$ be algebraic over
> $K$. Then $\alpha$ lies in a tower of quadratic extensions of $K$ if and only
> if $[K(\alpha):K]$ is a power of 2 and the Galois closure of $K(\alpha)/K$ is
> a 2-group.

Under the perfectness hypothesis (e.g., $K = \mathbb{F}_q$ or $K = \mathbb{Q}$
or any field of characteristic 0), separability holds automatically and the
Wantzel argument transfers verbatim. The S2 ACT target is then to formalise
this generalisation.

### Inseparable counterexample (informal, to be formalised in S4+)

Let $K = \mathbb{F}_p(t)$ (rational functions in one variable, characteristic
$p$). The element $\alpha = t^{1/p}$ has minimal polynomial $x^p - t$, which is
purely inseparable. Then:

- $[K(\alpha):K] = p$, not a power of 2 (for $p \neq 2$). ✓
- For $p = 2$: $[K(\alpha):K] = 2$, a "power of 2". But $\alpha$ does NOT lie in
  a quadratic Galois extension of $K$ — the extension $K(\alpha)/K$ is purely
  inseparable and not Galois (its Galois group is trivial, not $\mathbb{Z}/2$).

So the characterisation **fails in the inseparable case**, even at $p = 2$.
This formalises the seeker's "inseparable irreducibles in characteristic p
have Gal group of smaller order than expected" remark.

### Formal target signatures (Lean 4)

```lean
import Mathlib
import Proofs.AngleTrisection  -- Wantzel root gallery entry

namespace WantzelGeneralisation

/-- Constructibility over a base field K, defined as lying in a tower of
    quadratic extensions. (S2 ACT: pin down this definition; choose between
    Subfield-of-AlgebraicClosure formulation vs IntermediateField tower
    formulation.) -/
def IsConstructibleOver (K : Type*) [Field K]
    (α : AlgebraicClosure K) : Prop := sorry  -- candidate: ∃ tower

/-- **Wantzel for perfect fields** (S2/S3 ACT, headline):
    over a perfect field K, an algebraic α is constructible iff its degree
    [K(α):K] is a power of 2 and the Galois closure is a 2-group. -/
theorem wantzel_over_perfect_field
    (K : Type*) [Field K] [PerfectField K]
    (α : AlgebraicClosure K) (hα : IsAlgebraic K α) :
    IsConstructibleOver K α ↔
      ∃ n : ℕ, Module.rank K (IntermediateField.adjoin K {α}) = 2 ^ n :=
  sorry

/-- **Inseparable counterexample at p = 2** (S4 ACT):
    for K = 𝔽₂(t), the element √t has [K(√t):K] = 2 (a power of 2) yet
    is NOT constructible over K (the extension is not Galois of degree 2). -/
theorem inseparable_counterexample_char2 :
    ∃ (K : Type) (_ : Field K) (α : AlgebraicClosure K),
      Module.rank K (IntermediateField.adjoin K {α}) = 2 ∧
      ¬ IsConstructibleOver K α := sorry

end WantzelGeneralisation
```

## Classification

```yaml
tier: B
significance: 7
tractability: 4
tags:
  - seeker-selected
  - galois-theory
  - field-theory
  - char-p
  - separability
  - perfect-fields
  - constructibility
  - mathlib-extension
```

**Significance**: 7/10 — the seeker rating is well-calibrated. Generalising
Wantzel beyond characteristic 0 is a textbook exercise in modern Galois theory
(Lang VI.§1, Stewart §17, Bosch §3.4) but **NOT** a Mathlib-formalised fact.
The formalisation would expose the separability/perfectness boundary clearly,
and would be the first Mathlib-adjacent treatment of constructibility over
a characteristic-p base field.

**Tractability**: 4/10 (downgrading from seeker's 5/10) — three sources of
genuine difficulty:

1. **Defining `IsConstructibleOver` in Lean is non-trivial** without
   compass-and-straightedge primitives at the geometric level. The clean
   route is the algebraic one: a tower of quadratic extensions. But the
   Wantzel root gallery entry uses a different (geometry-flavoured) primitive
   ("$\cos(20°)$ satisfies an irreducible cubic"); reconciling the two takes
   careful design.
2. **`PerfectField` in Mathlib v4.26.0**: present but with limited downstream
   API. Most Galois-theoretic results that use perfectness are stated as
   `[Algebra.IsSeparable K L]` rather than `[PerfectField K]`. Bridging takes
   ~20-50 LOC of glue.
3. **Inseparable counterexample formalisation** ($K = \mathbb{F}_2(t)$,
   $\alpha = \sqrt{t}$) requires concrete construction of the function field
   and the explicit minimal polynomial. Mathlib has `RatFunc` but the
   `IntermediateField.adjoin` and `Module.rank` infrastructure over `RatFunc`
   has rough edges.

## Decomposition (S2–S7 targets)

### S2 — Define `IsConstructibleOver K α` over an abstract field K

**Deliverable**: `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01.lean` with:

```lean
def IsConstructibleOver (K : Type*) [Field K] (α : AlgebraicClosure K) : Prop :=
  ∃ (n : ℕ) (chain : Fin (n+1) → IntermediateField K (AlgebraicClosure K)),
    chain 0 = ⊥ ∧
    α ∈ chain n ∧
    ∀ i : Fin n, Module.rank (chain i.castSucc) (chain i.succ) = 2
```

Expected ~30 Lean lines. No theorems beyond the definition + a couple of
sanity-check boundary cases (`IsConstructibleOver K (0 : _) = True`, etc.).

### S3 — Wantzel direction "constructible ⇒ degree is 2-power" (perfect K)

**Deliverable**: prove

```lean
theorem isConstructibleOver_imp_rank_pow_two
    (K : Type*) [Field K] (α : AlgebraicClosure K)
    (h : IsConstructibleOver K α) :
    ∃ n : ℕ, Module.rank K (IntermediateField.adjoin K {α}) = 2 ^ n
```

This direction does NOT need perfectness — a tower of quadratic extensions
gives a $2^n$-dimensional subfield by the multiplicativity of rank, and
$\mathbb{F}(\alpha)$ is contained in the top of the tower so its rank divides
$2^n$, hence is a power of 2. The Wantzel root gallery entry has this
direction in characteristic 0; the S3 ACT transfers it to arbitrary
characteristic by changing `[Field ℚ]` to `[Field K]` (no separability
needed for the "⇒" direction).

Expected ~40-60 Lean lines. The cleanest proof imitates the root gallery
entry's `IsConstructible_imp_rank_pow_two` (or whatever the analogous result
is named there) by induction on the tower length.

### S4 — Wantzel direction "degree is 2-power ⇒ constructible" (perfect K)

**Deliverable**: prove

```lean
theorem rank_pow_two_imp_isConstructibleOver
    (K : Type*) [Field K] [PerfectField K]
    (α : AlgebraicClosure K) (hα : IsAlgebraic K α)
    (h : ∃ n : ℕ, Module.rank K (IntermediateField.adjoin K {α}) = 2 ^ n) :
    IsConstructibleOver K α
```

This direction **does** need perfectness (or, equivalently, separability of
the minimal polynomial of $\alpha$). The classical proof: take the Galois
closure $L/K$, which is a 2-group by hypothesis (since $K(\alpha) \subseteq L$
and $L/K$ is Galois with order a power of 2 by perfectness + minimal-poly
argument). Galois theory then gives a chain of intermediate fields with
quadratic step extensions, exhibiting $\alpha$ as constructible.

The S4 ACT will need to invoke Mathlib's Galois theory infrastructure
(`IsGalois`, `IntermediateField.fixed`, `IntermediateField.adjoin`, etc.)
plus a fact about 2-groups: every 2-group has a normal subgroup of index 2,
yielding the inductive step.

Expected ~80-120 Lean lines. The 2-group induction is the deepest part.

### S5 — Inseparable counterexample at $p = 2$

**Deliverable**: prove

```lean
theorem inseparable_counterexample :
    ∃ (K : Type) (_ : Field K) (α : AlgebraicClosure K),
      Module.rank K (IntermediateField.adjoin K {α}) = 2 ∧
      ¬ IsConstructibleOver K α
```

Concrete instance: $K = \mathbb{F}_2(t)$ (`RatFunc (ZMod 2)`),
$\alpha = $ a root of $x^2 - t$ in the algebraic closure. Then
$[K(\alpha):K] = 2$ but $\alpha \notin$ any quadratic Galois extension of $K$
because the extension is purely inseparable (the unique root has multiplicity 2
in the minimal polynomial).

Expected ~50-80 Lean lines. The blocker is the `RatFunc` + `AlgebraicClosure`
infrastructure overhead; the mathematical content is short.

### S6 — Optional: connection back to the root gallery entry

**Deliverable**: derive Wantzel's classical $\mathbb{Q}$-theorem as a corollary
of `wantzel_over_perfect_field` at $K = \mathbb{Q}$. This is the "gallery
integration" of the generalised result.

Expected ~10-20 Lean lines.

### S7 — Gallery integration

Add `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01/` with
`status: "formalized"` if S2-S5 ship without axioms (S5 is the open
counterexample question); else `"axiomatized"`.

## Mathlib Infrastructure Map

| Need | Mathlib name (v4.26.0) | Module |
|------|-----------------------|--------|
| Field, `PerfectField`, characteristic | `Field`, `PerfectField`, `CharP` | core |
| Algebraic closure | `AlgebraicClosure` | `Mathlib.FieldTheory.AlgebraicClosure` |
| Intermediate fields, `adjoin` | `IntermediateField`, `IntermediateField.adjoin` | `Mathlib.FieldTheory.IntermediateField.Basic` |
| Tower of extensions, `Module.rank` multiplicativity | `Module.rank_mul`, `Module.IsTower` | `Mathlib.LinearAlgebra.Dimension.Basic` |
| Galois closure | `normalClosure`, `IsGalois` | `Mathlib.FieldTheory.Normal`, `Mathlib.FieldTheory.Galois` |
| 2-groups (Sylow / order argument) | `IsPGroup`, `Sylow` | `Mathlib.GroupTheory.PGroup`, `Mathlib.GroupTheory.Sylow` |
| `Algebra.IsSeparable` | `Algebra.IsSeparable` | `Mathlib.FieldTheory.Separable` |
| `RatFunc` (for the counterexample) | `RatFunc` | `Mathlib.FieldTheory.RatFunc.Basic` |

**Gaps (no Mathlib support)**:

- **Wantzel's `IsConstructibleOver` over an arbitrary base K**: not present.
  The root gallery entry (`Proofs/AngleTrisection.lean`) defines
  `Constructible` only over $\mathbb{Q}$ (or $\mathbb{R}$). The S2 ACT
  abstraction is genuinely new.
- **2-group ⇒ chain of normal subgroups of index 2**: this is the deep step
  of S4. Mathlib has `IsPGroup` but I am uncertain whether the specific
  chain lemma is directly available; may need a short derivation.
- **`RatFunc` + `AlgebraicClosure` interaction**: present but underdeveloped;
  the inseparable counterexample (S5) may hit rough edges.

⇒ S2/S3/S6 are largely transfers; S4 and S5 are the substantive Lean work.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `angle-trisection` (root) | Wantzel's classical theorem over $\mathbb{Q}$; the algebraic core of this OQ chain |
| `angle-trisection-cos-20-gal` | Galois-theoretic Wantzel via $\cos(20°)$'s minimal polynomial; the most direct algebraic predecessor |
| `angle-trisection-oq-02` (grandparent of grandparent) | "Constructible algebraic numbers characterized by Galois groups" — the over-arching question |
| `abel-ruffini-galois-extensions` | Galois extension infrastructure shared with this OQ |

## Risk Notes

- **`IsConstructibleOver` definition**: the S2 ACT design decision is genuinely
  consequential. Two reasonable definitions:
  - **Tower form**: $\exists$ a chain $K = K_0 \subseteq K_1 \subseteq \cdots \subseteq K_n$
    with $[K_{i+1}:K_i] = 2$ and $\alpha \in K_n$.
  - **Field-degree form**: $[K(\alpha):K]$ is a power of 2 AND the Galois
    closure has 2-power degree.

  The two are equivalent over perfect fields but the field-degree form is
  not directly "Wantzel" — it bakes in the theorem rather than stating the
  problem. The tower form is the honest formulation; the equivalence with the
  field-degree form is S3+S4.

- **Inseparable counterexample at $p \neq 2$**: trivially $[K(\alpha):K] = p$
  is not a power of 2, so the issue doesn't even arise. The interesting
  counterexample is $p = 2$, where $[K(\alpha):K] = 2$ misleads.

- **Mathlib `IsConstructible`**: it's possible that
  `Mathlib.NumberTheory.Constructible` (if it exists) already has something
  analogous; should be cross-checked in S2 ACT. If yes, S2 just imports;
  if no, we introduce our own.

- **Status policy**: if S2-S6 ship without axioms, `verified`. The S4 2-group
  step is the most likely sorry-candidate; if it requires an axiom, status
  becomes `axiomatized`.

## References

- Wantzel, "Recherches sur les moyens de reconnaître si un problème de
  géométrie peut se résoudre avec la règle et le compas", *J. Math. Pures Appl.*
  **2** (1837), 366-372 — the original proof.
- Lang, *Algebra*, 3rd ed., chapter VI §1 — Wantzel's theorem, transfer to
  arbitrary perfect base fields.
- Stewart, *Galois Theory*, 4th ed., chapter 17 — constructibility via
  tower of quadratic extensions.
- Bosch, *Algebra*, chapter 3 §4 — Galois theory in characteristic $p$.
- Wikipedia: [Constructible number](https://en.wikipedia.org/wiki/Constructible_number)
  — modern statement; explicit mention of perfectness requirement.

## Honesty

This S1 OBSERVE iteration is a **pure survey**. It produces:

- 0 new Lean theorems
- 0 sorry deltas
- 0 axiom deltas
- 1 markdown file (this `problem.md`, replacing the auto-generated stub)
- 1 state.md update (S1 OBSERVE notation)

The mathematical content (Wantzel over perfect fields + inseparable
counterexample at $p = 2$) is **not novel**: it's a textbook fact (Lang,
Stewart, Bosch). The S1 contribution is the precise Lean target statements,
the S2-S7 decomposition (genuinely new design work), and the Mathlib gap
analysis.

The future Lean entry will be `status: "formalized"` if S2-S6 ship without
axioms; `"axiomatized"` if the S4 2-group step requires an axiom or the S5
inseparable counterexample requires concrete `RatFunc + AlgebraicClosure`
infrastructure not yet in Mathlib.
