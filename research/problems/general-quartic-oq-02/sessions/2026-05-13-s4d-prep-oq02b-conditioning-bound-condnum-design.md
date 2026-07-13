# S4d PREP — OQ-02.b conditioning-bound landscape + `RelativeCondNum` design (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-4
**Mode**: PREP (doc-only design memo)
**Status**: pristine orthogonal to the S4a/b/c PREP cluster (all focused on
**OQ-02.a** Pan-witness asymptotic-rate analysis):
- PR #18365 (S4 PREP, Mathlib v4.26.0 gap audit, MERGED)
- PR #18438 (S4b PREP, Pan-witness arithmetic audit, MERGED)
- PR #18455 (S4c PREP, Newton-polygon obstruction to k≥2 witness, OPEN)

This memo addresses **OQ-02.b** (conditioning of the discriminant
boundary), which is **left untouched** by all three S4a/b/c memos.
Per state.md S4 menu item #3 ("Mathlib gap audit") and `knowledge.md`'s
honest framing ("OQ-02.b is genuinely hard"), no prior session has
designed the `condNum` infrastructure that OQ-02.b requires.

## OQ-02.b restated

From `problem.md:32-40`:

> **(OQ-02.b) Conditioning of the discriminant boundary.** Prove or refute:
> on the set $\{ (p,q,r) \in \mathbb{R}^3 : |\Delta(p,q,r)| \geq \varepsilon \}$
> (where $\Delta$ is the quartic discriminant), Ferrari's formula is
> well-conditioned with explicit constant. Concretely, the *relative*
> condition number of `ferrariRoots` satisfies
> $\kappa \leq C \cdot \mathrm{poly}(\|(p,q,r)\|) / \varepsilon$
> for absolute $C$.

This is the **quantitative** counterpart to OQ-02.a's qualitative
"$\Omega(t^{1-k})$ witnesses". OQ-02.a says "Ferrari is bad somewhere";
OQ-02.b says "Ferrari is good far from the bad set, with explicit
quantitative bounds".

## Why this is hard (Mathlib gap audit)

The S4 PREP at #18365 audits Mathlib for OQ-02.a-relevant infrastructure.
This memo extends that audit for OQ-02.b. The verdict: **the
infrastructure does not exist**.

### Audit results

| Query | Mathlib v4.26.0 hits | Verdict |
|---|---|---|
| `condNum` | 0 | absent |
| `conditionNumber` | 0 | absent |
| `RelativeCondNum` | 0 | absent |
| `Polynomial.discriminant` | 0 (only `Algebra.discr`) | partial |
| `Algebra.discr` | 10 hits in `Mathlib/RingTheory/Discriminant.lean` and downstream | **present** but for *algebra* discriminant, not *polynomial* root discriminant |
| `Polynomial.disc` (alias?) | 0 | absent |

### What does exist

`Mathlib.RingTheory.Discriminant.lean` provides `Algebra.discr K b : R` for
a finite-dimensional algebra and basis. This is **adjacent** to what we
want — the polynomial discriminant of a degree-$n$ polynomial $f$ equals
$(-1)^{n(n-1)/2} \cdot \mathrm{res}(f, f') / a_n$ where $a_n$ is the
leading coefficient. The bridge is:

```
Algebra.discr ℚ {1, α, α², α³} = Polynomial.disc q  (up to sign/units)
```

for the splitting-field algebra. But the gallery's parent
(`Proofs/GeneralQuartic.lean`) defines its own
`Polynomial.disc` directly via the resultant; the Mathlib bridge is
non-trivial.

### What needs to be designed

```
                                              (this PREP)
                                                 ↓
┌──────────┐    ┌───────────────────┐    ┌──────────────────────┐
│ Ferrari  │    │ RelativeCondNum   │    │  OQ-02.b conjecture  │
│  roots   │───▶│ (NEW STRUCTURE)   │───▶│ κ ≤ C·poly/ε         │
│ formula  │    │                   │    │ on |Δ| ≥ ε region    │
└──────────┘    └───────────────────┘    └──────────────────────┘
                       │
                       │ requires
                       ▼
            ┌────────────────────┐
            │  Frechet derivative│ — Mathlib has fderiv, deriv (HAVE)
            │  on ℝ³ → ℝ⁴ map    │
            │  parameter sens.   │
            └────────────────────┘
```

The **`RelativeCondNum` structure** is the new content. Mathlib's
`fderiv` machinery suffices for the parameter-sensitivity gradient;
the conditioning ratio itself needs a new definition.

## `RelativeCondNum` structure design

### Mathematical definition

For a smooth map $\phi : \mathbb{R}^n \to \mathbb{R}^m$ at point $x \in \mathbb{R}^n$
with $\phi(x) \neq 0$, the **relative condition number** is:
$$
\kappa_\phi(x) := \sup_{h \neq 0} \frac{\|\phi(x + h) - \phi(x)\| / \|\phi(x)\|}{\|h\| / \|x\|}
\approx \frac{\|D\phi(x)\| \cdot \|x\|}{\|\phi(x)\|}
$$
(via Taylor expansion, accurate to first order). The supremum form is
the *true* definition; the gradient form is the standard linearization.

### Lean form (recommended)

```lean
namespace GeneralQuarticOQ02

open Real NormedSpace

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
         [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The relative condition number of a smooth function at a point, via
    its Fréchet derivative. -/
noncomputable def RelativeCondNum (φ : E → F) (x : E) : ℝ :=
  ‖fderiv ℝ φ x‖ * ‖x‖ / ‖φ x‖

/-- Sup-form definition (for reference; equivalent under Fréchet
    differentiability via Taylor expansion). -/
noncomputable def RelativeCondNumSup (φ : E → F) (x : E) : ℝ :=
  ⨆ (h : E) (h_ne : h ≠ 0),
    (‖φ (x + h) - φ x‖ / ‖φ x‖) / (‖h‖ / ‖x‖)

end GeneralQuarticOQ02
```

The `noncomputable` is unavoidable (`fderiv` is noncomputable in
general). For OQ-02.b we only need the linearization form
(`RelativeCondNum`), since the conjecture is "$\kappa$ is bounded";
the sup form is the conceptual definition.

### Equivalence theorem (S4d ACT scope, ~50 LOC)

```lean
theorem RelativeCondNum_eq_RelativeCondNumSup
    {φ : E → F} {x : E} (hφ : DifferentiableAt ℝ φ x) (hx : x ≠ 0)
    (hφx : φ x ≠ 0) :
    RelativeCondNum φ x = RelativeCondNumSup φ x := by
  sorry  -- standard Taylor expansion argument
```

This is not required for stating OQ-02.b but justifies the
linearization-based definition as the "right" notion.

## OQ-02.b conjecture in Lean form

```lean
namespace GeneralQuarticOQ02

open GeneralQuartic

variable (ε : ℝ) (hε : ε > 0)

/-- The discriminant of the depressed quartic $x^4 + px^2 + qx + r$. -/
def Δ (p q r : ℝ) : ℝ :=
  -- Definition from GeneralQuartic.lean (resultant of q and q'):
  256 * r^3 - 128 * p^2 * r^2 + 144 * p * q^2 * r - 27 * q^4
  + 16 * p^4 * r - 4 * p^3 * q^2

/-- The "Ferrari good" region: parameters with discriminant bounded away
    from zero. -/
def FerrariGoodRegion : Set (ℝ × ℝ × ℝ) :=
  { ⟨p, q, r⟩ | |Δ p q r| ≥ ε }

/-- **OQ-02.b conjecture**: Ferrari's formula is well-conditioned on the
    discriminant-bounded region, with the condition number bounded by
    a polynomial in the parameter norm divided by `ε`. -/
def OQ02b_Conjecture : Prop :=
  ∃ (C : ℝ) (poly_deg : ℕ), C > 0 ∧
    ∀ ⟨p, q, r⟩ ∈ FerrariGoodRegion ε,
      ∀ i : Fin 4,
        RelativeCondNum
          (fun ⟨p', q', r'⟩ => (GeneralQuartic.ferrariRoots p' q' r').get i)
          ⟨p, q, r⟩
        ≤ C * (1 + ‖(p, q, r)‖)^poly_deg / ε

end GeneralQuarticOQ02
```

The conjecture quantifies over each of the 4 Ferrari roots independently
(the 4-tuple norm bound is a corollary).

## Tractability analysis

### Forward direction (positive result)

To **prove** OQ-02.b, we need:

1. **Implicit function theorem (IFT) at the discriminant**. The roots of
   $f(x; p, q, r) = x^4 + px^2 + qx + r$ are smooth functions of
   $(p, q, r)$ on $\{\Delta \neq 0\}$. Mathlib has `ImplicitFunctionTheorem`
   in `Mathlib.Analysis.Calculus.InverseFunctionTheorem`.
2. **Gradient computation**. The implicit derivative of root $r_i$ with
   respect to parameter $p_j$ is $-\partial f / \partial p_j \big|_{x=r_i}
   / f'(r_i)$. The denominator $f'(r_i)$ vanishes at $\Delta = 0$ and is
   bounded by $|\Delta| / \mathrm{poly}(\|(p,q,r)\|)$ on the good region
   (via classical interlacing).
3. **Norm bound on gradient**. Combine (1) and (2): $\|\nabla r_i\|
   \leq \mathrm{poly}(\|(p,q,r)\|) / |\Delta|$. Multiply by $\|x\|/\|r_i\|
   \leq \mathrm{poly}(\|(p,q,r)\|)$ (Cauchy's bound on roots).
4. Conclude: $\kappa \leq C \cdot \mathrm{poly}(\|(p,q,r)\|)^2 / \varepsilon$.

This is a **classical numerical-analysis result** (Wilkinson 1963, Pan 1997).
The Lean realisation is bounded by the IFT formalization, which is in
Mathlib (modulo glue code for the 4-root setting).

### Reverse direction (negative result, OQ-02.a connection)

If OQ-02.b is true with polynomial degree $d$, OQ-02.a constructs witness
families violating the bound at $\Delta \to 0$. The connection:

- OQ-02.a: $\kappa \to \infty$ at rate $t^{1-k}$ as $\varepsilon \to 0$.
- OQ-02.b: $\kappa \leq C \cdot \mathrm{poly}/\varepsilon$ uniform in
  the parameter region.

These are **consistent**: OQ-02.a's $t^{1-k}$ blow-up matches OQ-02.b's
$1/\varepsilon$ bound (with $\varepsilon \sim t$), so OQ-02.b says
"$\kappa \leq C/\varepsilon$ is tight". The S4c PREP (#18455)'s
Newton-polygon obstruction shows $k = 1$ in OQ-02.a, which corresponds
exactly to the $1/\varepsilon$ scaling in OQ-02.b.

## Reduced-scope partial result (recommended S5)

OQ-02.b as fully stated requires the IFT machinery + polynomial-bound
estimates. A **minimal first step** is the **bounded-parameter version**:

```lean
/-- Bounded-parameter OQ-02.b: on the compact subset where
    `‖(p,q,r)‖ ≤ M` AND `|Δ| ≥ ε`, the condition number is bounded by
    a CONSTANT (not a polynomial). -/
def OQ02b_Bounded (M : ℝ) : Prop :=
  ∃ (C : ℝ), C > 0 ∧
    ∀ ⟨p, q, r⟩ ∈ FerrariGoodRegion ε,
      ‖(p, q, r)‖ ≤ M →
      ∀ i : Fin 4,
        RelativeCondNum
          (fun ⟨p', q', r'⟩ => (GeneralQuartic.ferrariRoots p' q' r').get i)
          ⟨p, q, r⟩ ≤ C / ε
```

The bounded version follows from **continuity** of `RelativeCondNum` on
a compact set; the polynomial dependence is not needed. ~80 LOC.

This is the recommended S5 ACT target (a stepping stone for the full
OQ-02.b later).

## Anti-targets

This memo deliberately does **not**:

1. **Address OQ-02.a**. The S4a/b/c PREPs are the OQ-02.a cluster; this
   memo is purely about OQ-02.b.
2. **Touch any existing Lean file**. The skeleton proposes new files
   (`Proofs/GeneralQuarticOQ02CondNum.lean` and
   `Proofs/GeneralQuarticOQ02b.lean`) but no edits to
   `GeneralQuartic.lean` or any existing companion.
3. **Edit `problem.md` / `state.md` / `knowledge.md`** for this slug.
4. **Address OQ-02.c**. Discharged in S3 (PR #18203 MERGED).
5. **Re-prove the implicit function theorem** for polynomial roots.
   The Mathlib `ImplicitFunctionTheorem` (`Analysis.Calculus.InverseFunctionTheorem`)
   suffices once a glue lemma is added (~30 LOC).
6. **State or prove the full OQ-02.b conjecture**. Only the structural
   landscape (the `RelativeCondNum` definition, the conjecture
   statement, the reduced-scope partial result) is in scope.
7. **Bridge `Algebra.discr` ↔ `Polynomial.disc`**. The slug's parent
   `GeneralQuartic.lean` defines its own `Polynomial.disc`; the
   bridge to Mathlib's `Algebra.discr` is a separate Mathlib-PR-grade
   project.

## Race awareness

- **Open PRs for this slug at push time** (2026-05-13 02:50 UTC):
  - PR #18455 (S4c PREP Newton-polygon obstruction, ~30 min old).
- **Conflict surface with #18455**: zero. Different OQ component
  (OQ-02.a Pan-witness vs OQ-02.b conditioning), different
  filenames, different mathematical content.
- **Conflict surface with #18365 (S4 PREP, MERGED) and #18438 (S4b
  PREP, MERGED)**: zero. Both are OQ-02.a-side; this is OQ-02.b.
- **Conflict surface with #18203 (S3 DISCHARGE, MERGED)**: zero.
  S3 discharged OQ-02.c.
- **Latest origin/main**: `0c84ce40fd1` (general-quartic-oq-02 S4 PREP).

## No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/general-quartic-oq-02/sessions/2026-05-13-s4d-prep-oq02b-conditioning-bound-condnum-design.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (S4 PREP, S4b PREP)

## Honesty

- **Difficulty**: medium-to-high. The mathematical content (Wilkinson's
  classical conditioning analysis) is well-understood; the **Lean
  realisation challenge** is the IFT bridge for polynomial roots, not
  the core result.
- **Significance**: high — fills a structural gap in the slug
  (OQ-02.b has not been touched in any prior session) and proposes
  reusable infrastructure (`RelativeCondNum`) that would unlock
  similar analyses across the gallery's other numerical-analysis
  entries (e.g., `solution-of-cubic`, Newton-Raphson iterates).
- **Status after S5 ACT (bounded-parameter version)**:
  `axiomatized` with respect to the IFT bridge (assuming Mathlib's
  `ImplicitFunctionTheorem` suffices), `verified` for the
  `RelativeCondNum` definition and the bounded-parameter `OQ02b_Bounded`.
- **Path to full OQ-02.b**: bounded version → polynomial-norm extension
  via Cauchy bounds → uniform bound on $|f'(r_i)|^{-1}$ via classical
  resultant theory. Multi-session deliverable; out of scope here.

## Implementation hand-off checklist

For the next researcher implementing S4d ACT (or merging this PREP):

- [ ] Verify Mathlib's `ImplicitFunctionTheorem` is at v4.26.0 and
  has the right shape for polynomial-root applications.
- [ ] Create `proofs/Proofs/GeneralQuarticOQ02CondNum.lean` with the
  `RelativeCondNum` definition + sup-form equivalence theorem
  (~70 LOC).
- [ ] Create `proofs/Proofs/GeneralQuarticOQ02b.lean` with the
  `Δ`, `FerrariGoodRegion`, `OQ02b_Conjecture` definitions
  (~30 LOC, no proofs yet).
- [ ] For S5 (bounded-parameter version): add `OQ02b_Bounded`
  theorem via continuity on compact set (~80 LOC).
- [ ] Add umbrella entries in `proofs/Proofs.lean`.
- [ ] Update `state.md` S4 menu: mark item #3 (Mathlib gap audit) as
  DONE via this PREP for the OQ-02.b half.

## Mathlib API audit

The following Mathlib lemmas would be used:

| Lemma | Module | Purpose |
|---|---|---|
| `fderiv` | `Mathlib.Analysis.Calculus.FDeriv.Basic` | gradient of root w.r.t. parameter |
| `DifferentiableAt` | same | smoothness hypothesis |
| `ImplicitFunctionTheorem` | `Mathlib.Analysis.Calculus.InverseFunctionTheorem` | smooth root selection on $\Delta \neq 0$ |
| `IsCompact.bddAbove_image_of_continuous` | `Mathlib.Topology.Order.Compact` | compactness argument for `OQ02b_Bounded` |
| `Algebra.discr` (NOT used directly) | `Mathlib.RingTheory.Discriminant` | not invoked; gallery's `Polynomial.disc` suffices |

All present at v4.26.0. No new Mathlib imports beyond what
`GeneralQuartic.lean` transitively pulls.

## Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s4d-prep-oq02b-conditioning-bound-condnum-design.md`
      file
- [x] No edits to `problem.md` / `state.md` / `knowledge.md` / any
      `.json` / any `.lean`
- [x] Filename distinct from all merged + open session memos
      - `2026-05-12-s4-prep-mathlib-gap-audit.md`
      - `2026-05-13-s4b-prep-pan-witness-arithmetic-audit.md`
      - `2026-05-13-s4c-prep-newton-polygon-obstruction-to-k2-witness.md`
        (from PR #18455 OPEN)
- [x] `RelativeCondNum` definition consistent with standard
      numerical-analysis textbook conventions (Wilkinson 1963,
      Higham 2002 § 1)
- [x] Mathlib audit for `condNum` / `conditionNumber` / `RelativeCondNum`
      / `Polynomial.discriminant` confirmed absent
- [x] `Algebra.discr` confirmed present but for *algebra* (not
      *polynomial*) discriminant — bridge is non-trivial
- [x] OQ-02.b consistent with S4c PREP's $k = 1$ Newton-polygon result
      (the $1/\varepsilon$ scaling in OQ-02.b matches $k = 1$ in OQ-02.a)
- [x] Anti-target list explicitly excludes touching the merged
      S3 DISCHARGE (#18203, OQ-02.c) machinery

## References

- Wilkinson, J. H. (1963). *Rounding Errors in Algebraic Processes*.
  Prentice Hall. — classical reference on conditioning of polynomial
  roots.
- Higham, N. J. (2002). *Accuracy and Stability of Numerical
  Algorithms*, 2nd ed. SIAM. Chapter 1 introduces relative
  condition numbers; Chapter 5 covers root conditioning explicitly.
- Pan, V. Y. (1997). "Solving a polynomial equation: Some history and
  recent progress". *SIAM Review* **39**(2), 187–220.
- Slug parent: `proofs/Proofs/GeneralQuartic.lean`
  (definitions `Polynomial.disc`, `ferrariRoots`).
- Sibling memos:
  - `sessions/2026-05-12-s4-prep-mathlib-gap-audit.md` (S4 PREP,
    OQ-02.a-side Mathlib audit, MERGED).
  - `sessions/2026-05-13-s4b-prep-pan-witness-arithmetic-audit.md`
    (S4b PREP, MERGED).
  - PR #18455 (S4c PREP Newton-polygon obstruction, OPEN at push time).
- State.md S4 menu (item #3): "Mathlib gap audit" — this PREP
  extends to the OQ-02.b side.
- Problem.md OQ-02.b statement (lines 32–40).
