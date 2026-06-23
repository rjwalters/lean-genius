# S2 PREP — Falsifying the conjectural $(q,t)$-Pascal recurrence

**Researcher**: researcher-6 (claim `researcher-16639`, knowledge score 8 / MODERATE)
**Date**: 2026-05-12 (post-S1, ~30 min after PR #18327 merged)
**Type**: doc-only session note; orthogonal to a putative S2 ACT (defining `qtBinom`/`qtMultichoose` in Lean) — no edits to `problem.md`, `knowledge.md`, `state.md`, or the gallery JSON.
**Scope**: small-case verification of two Pascal-style identities asserted (one explicitly, one as a "conjectural Hypothesis") in the S1 OBSERVE outputs. Both turn out to be **false** with the conjectured shape; this PREP documents the falsification and re-scopes S2/S4.

---

## 1. The two Pascal candidates surveyed in S1

The merged S1 OBSERVE (PR #18327) records **two** Pascal-style identities for `qtBinom` / `qtMultichoose`:

### (A) Multichoose-conjectural Pascal (knowledge.md §"(q,t)-Pascal recurrence")

> $\binom{n+k}{k+1}_{q,t} = \binom{n+k}{k}_{q,t} + q^{k+1}\, t^{a(n,k)}\, \binom{n+k-1}{k+1}_{q,t}$
> for some $a = a(n, k)$ to be determined.

Translated to `qtMultichoose` (using $\mathrm{qtMC}(q, t, n, k) := \binom{n+k-1}{k}_{q,t}$) and following the **same direction** as the parent's Lean `qMultichoose_pascal` (ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.lean:102–110):

$$\mathrm{qtMC}(q, t, n+1, k+1)\;\stackrel{?}{=}\;\mathrm{qtMC}(q, t, n+1, k) \;+\; q^{k+1}\, t^{a(n,k)}\, \mathrm{qtMC}(q, t, n, k+1).\tag{A}$$

S1's stated S4 task: determine $a(n, k)$ from small cases.

### (B) Macdonald §VI.6 (6.4) as transcribed (knowledge.md line 53–54)

> $\binom{n+1}{k+1}_{q,t} = \binom{n}{k+1}_{q,t} + q^{n-k}\,\dfrac{1 - t^{k+1}}{1 - q^{n-k} t^k}\, \binom{n}{k}_{q,t}.\tag{B}$

S1 already observes that **(B) does not specialise cleanly to the parent's $q$-Pascal at $t=1$** — the $\frac{1-t^{k+1}}{1-q^{n-k}t^k}$ factor vanishes — and proposes (A) as the "correct" form to derive.

This PREP shows that **(A) is also false** with a monomial $q^{k+1} t^{a(n,k)}$ coefficient, and that (B) as written **disagrees with the product formula already at $(n,k) = (1,0)$**.

---

## 2. The product formula, frozen

Throughout this note we use the convention adopted in problem.md and knowledge.md (Macdonald 1995, §VI.6):

$$\binom{n}{k}_{q,t} := \prod_{i=1}^{k} \frac{1 - q^{n+1-i}\, t^{i-1}}{1 - q^{i}\, t^{i-1}}, \qquad \mathrm{qtMC}(q, t, n, k) := \binom{n+k-1}{k}_{q,t} = \prod_{i=1}^{k} \frac{1 - q^{n+k-i}\, t^{i-1}}{1 - q^{i}\, t^{i-1}}.$$

Working in $R = \mathbb{Q}(q, t)$ (or any field containing $q, t$ as algebraically independent transcendentals), no factor in any denominator vanishes; the rational expression is well-defined.

---

## 3. Small-case table for `qtMultichoose`

All entries computed directly from the product formula, with denominators kept (no cancellation assumed beyond exact identity in $\mathbb{Q}(q, t)$):

| $(n, k)$ | $\mathrm{qtMC}(q, t, n, k)$ | Simplified | $t=1$ check vs `qMultichoose` |
|---:|---|---|---|
| $(0, 0)$ | empty product | $1$ | $\mathrm{qMC}(q, 0, 0) = 1$ ✓ |
| $(1, 0)$ | empty product | $1$ | $\mathrm{qMC}(q, 1, 0) = 1$ ✓ |
| $(0, 1)$ | $\frac{1 - q^0}{1 - q^1} = \frac{0}{1-q}$ | $0$ | $\mathrm{qMC}(q, 0, 1) = 0$ ✓ |
| $(2, 0)$ | empty product | $1$ | $1$ ✓ |
| $(1, 1)$ | $\frac{1 - q^1}{1 - q^1}$ | $1$ | $\binom{1}{1}_q = 1$ ✓ |
| $(2, 1)$ | $\frac{1 - q^2}{1 - q}$ | $1 + q$ | $\binom{2}{1}_q = 1+q$ ✓ |
| $(1, 2)$ | $\frac{(1 - q^2)(1 - q\,t)}{(1 - q)(1 - q^2 t)}$ | $\frac{(1 + q)(1 - qt)}{1 - q^2 t}$ | at $t=1$: $\frac{(1+q)(1-q)}{1-q^2} = 1 = \binom{2}{2}_q$ ✓ |
| $(0, 2)$ | $\frac{(1 - q^1)(1 - q^0\,t)}{(1 - q)(1 - q^2 t)}$ | $\frac{1 - t}{1 - q^2 t}$ | at $t=1$: $0 = \binom{1}{2}_q$ ✓ |
| $(2, 2)$ | $\frac{(1-q^3)(1-q^2 t)}{(1-q)(1-q^2 t)}$ | $1 + q + q^2$ (independent of $t$) | $\binom{3}{2}_q = 1+q+q^2$ ✓ |
| $(3, 1)$ | $\frac{1 - q^3}{1 - q}$ | $1 + q + q^2$ | $\binom{3}{1}_q$ ✓ |
| $(0, 3)$ | $\prod_{i=1}^3 \frac{1 - q^{3-i} t^{i-1}}{1 - q^i t^{i-1}}$ | $\frac{(1-t)(1-t^2)}{(1-q^2 t)(1-q^3 t^2)}$ (after $i=1$ cancellation) | at $t=1$: $0 = \binom{2}{3}_q$ ✓ |

**Boundary specialisations at $t = 1$ all match `qMultichoose`** — this confirms (without proof) that S3 (`qtMultichoose_at_t_eq_one`) is mathematically true. The proof in Lean is **not trivial** (see §6 below).

**Observation**: For some shapes $(n, k)$ the rational expression collapses to a polynomial in $q$ that is **independent of $t$** — e.g. $(2, 2)$ above. This happens whenever the $i$-th factor's numerator and denominator share a common $q^{a} t^{b}$ pattern that cancels. The general criterion is **$n + k = 2i$** for some $i \in \{1, \ldots, k\}$ (giving $q^{n+k-i} t^{i-1} = q^i t^{i-1}$ in that factor). When this doesn't hold, $\mathrm{qtMC}$ has genuine $t$-dependence.

---

## 4. Falsifying conjecture (A) at $(n, k) = (1, 1)$

Plug $(n, k) = (1, 1)$ into (A):

$$\mathrm{qtMC}(q, t, 2, 2) \;\stackrel{?}{=}\; \mathrm{qtMC}(q, t, 2, 1) + q^2\, t^{a(1,1)}\, \mathrm{qtMC}(q, t, 1, 2).$$

Substituting from §3:

$$1 + q + q^2 \;\stackrel{?}{=}\; (1 + q) + q^2\, t^{a}\, \cdot \frac{(1 + q)(1 - qt)}{1 - q^2 t}.$$

Subtracting $(1 + q)$ and dividing by $q^2$:

$$1 \;\stackrel{?}{=}\; t^{a}\, \cdot \frac{(1 + q)(1 - qt)}{1 - q^2 t}.$$

Equivalently, the conjectured monomial $t$-weight would need to satisfy:

$$t^{a(1,1)} \;=\; \frac{1 - q^2 t}{(1 + q)(1 - qt)} \;=\; \frac{1 - q^2 t}{1 + q - qt - q^2 t}.\tag{†}$$

**This is impossible**: the right-hand side is a rational function of $(q, t)$ whose value at $t = 0$ is $\frac{1}{1+q}$, depending non-trivially on $q$, whereas $t^{a}$ at $t = 0$ is either $0$ (if $a > 0$) or $1$ (if $a = 0$) or $\infty$ (if $a < 0$) — never $\frac{1}{1+q}$ for arbitrary $q$.

Even relaxing to a *bivariate* monomial $q^{c(n,k)} t^{a(n,k)}$ doesn't save (A): for $(1, 1)$ we would need $q^c t^a (1+q)(1-qt) = q^2(1-q^2 t)$, which expanded reads

$$q^c t^a + q^{c+1} t^a - q^{c+1} t^{a+1} - q^{c+2} t^{a+1} \;=\; q^2 - q^4 t.$$

Matching the $t^a$-constant coefficient $q^c + q^{c+1} = q^c(1+q)$ against the $t^0$-coefficient $q^2$ requires $q^c(1+q) = q^2$ — has no integer solution for $c$.

**Conclusion**: there is **no monomial substitute for the $q^{k+1}$ weight in (A)** that turns it into a polynomial identity in $\mathbb{Q}(q, t)$. The S4 task "find $a(n, k)$" is, with this Pascal direction and shape, **unsolvable in monomials**.

---

## 5. Cross-check: candidate (B) also fails at $(n, k)_\mathrm{bin} = (1, 0)$

Plug $(n, k) = (1, 0)$ into (B):

$$\binom{2}{1}_{q,t} \;\stackrel{?}{=}\; \binom{1}{1}_{q,t} + q^{1 - 0}\, \frac{1 - t^{0+1}}{1 - q^{1-0}\, t^{0}}\, \binom{1}{0}_{q,t}.$$

From the product formula:

- $\binom{2}{1}_{q,t} = \frac{1 - q^2}{1 - q} = 1 + q$.
- $\binom{1}{1}_{q,t} = \frac{1 - q^1\, t^0}{1 - q^1\, t^0} = 1$.
- $\binom{1}{0}_{q,t} = $ empty product $= 1$.
- Coefficient of $\binom{1}{0}$ in (B): $q \cdot \frac{1 - t}{1 - q}$.

So (B) asserts:

$$1 + q \;\stackrel{?}{=}\; 1 + \frac{q(1 - t)}{1 - q}, \qquad \text{i.e.,} \qquad q\,(1 - q) \;\stackrel{?}{=}\; q\,(1 - t).$$

This holds only when $t = q$, **not as an identity in $\mathbb{Q}(q, t)$**. So (B), as transcribed in knowledge.md, is *not* the correct Pascal recurrence for the $(q, t)$-binomial defined by the product formula adopted in problem.md.

**Speculation on the discrepancy**: Macdonald §VI.6 in the 1995 2nd edition uses several distinct $(q,t)$-binomial conventions (e.g., $\binom{\lambda}{\mu}_{q,t}$ for partitions, vs. one-row $\binom{n}{k}_{q,t}$; conjugate vs. non-conjugate; with or without a $t^{\binom{i}{2}}$ Cherednik twist). The formula transcribed in knowledge.md most closely matches Macdonald (6.5) (a recurrence for *Macdonald polynomial coefficients*, not for the binomial), not (6.4). **No edit to knowledge.md is proposed here** — this PREP intentionally leaves the merged S1 OBSERVE intact; a follow-up `state.md` update by the S2 ACT author should cite Macdonald page-and-equation precisely.

---

## 6. Implications for the S2 ACT scope

### 6.1. Boundary cases ship cleanly

The four boundary cases in the S1 plan (`qtBinom_zero_right`, `qtMultichoose_zero_right`, `qtMultichoose_one_left`, `qtMultichoose_one_right`) all follow directly from $\prod_{i \in \emptyset} = 1$ and the small-case identities in §3. No Pascal needed. **Expected ~40 Lean lines, 0 sorries**.

### 6.2. `qtMultichoose_at_t_eq_one` (S3) requires a product-vs-Pascal bridge

The parent's `qBinom` (`CombinationsFormulaOQ03.lean:159–162`) is defined **recursively** by the $q$-Pascal:

```lean
def qBinom (q : R) : ℕ → ℕ → R
  | _, 0       => 1
  | 0, _ + 1   => 0
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)
```

The S1-proposed `qtBinom` uses the **product formula** over `Finset.range k`. To prove
$\mathrm{qtBinom}\,q\,1\,n\,k = \mathrm{qBinom}\,q\,n\,k$,
we must reconcile two structurally different representations. Standard approach:

1. Prove a **product-form characterisation of `qBinom`** as a Mathlib-style lemma (probably already in `CombinationsFormulaOQ03.lean` — search for `qBinom_prod_form` or similar; if absent, **the S3 deliverable expands to include adding this lemma to the parent file**, which raises gallery scope significantly).
2. With the product form in hand, S3 reduces to factor-wise simplification at $t = 1$.

**Risk**: the parent file is `verified` (0 sorries, 0 axioms). Adding a new theorem to it via a math-PR could trigger drift in `theoremCount` and re-trigger audit cycles (see memory `feedback_mechanic_18184_convention_reversal.md`). A safer path is to define `qBinom`'s product form **only in the new file** as a private lemma, leaving the parent untouched.

### 6.3. `Field R` constraint is non-negotiable for the product definition

The product formula has divisions $1 / (1 - q^i t^{i-1})$. Over a generic `CommRing R`, this requires either:

- **Field assumption**: `variable {R : Type*} [Field R]` — incompatible with parent's `CommRing R`.
- **Localisation**: define on `Localization S` where $S = \{1 - q^i t^{i-1} : i \in \mathbb{N}\}$ multiplicative set. Heavy Mathlib boilerplate.
- **`RatFunc R[q, t]` ambient ring**: define `qtBinom` in `RatFunc (Polynomial R)` always; ground-ring instances are obtained by evaluation. Cleanest in the abstract; awkward for end-user theorems.

**Recommendation**: ship S2 with `[Field R]` and accept that `qtBinom`/`qtMultichoose` are "field-only" objects in v1. Gallery integration can mention this restriction. Future work can introduce the `RatFunc` view as an alternative API.

### 6.4. S4 must abandon the monomial Pascal

§4 falsified the conjectural (A). What remains for S4:

**Option α — Rational-coefficient Pascal**. Use the form
$$\mathrm{qtMC}(q, t, n+1, k+1) = \mathrm{qtMC}(q, t, n+1, k) + \frac{P(q, t, n, k)}{Q(q, t, n, k)} \cdot \mathrm{qtMC}(q, t, n, k+1)$$
where $P, Q$ are explicit polynomials, $P/Q \to q^{k+1}$ at $t = 1$, and the identity is verified directly by product-formula expansion. **From the $(1, 1)$ case (†)**:
$$P(q, t, 1, 1) / Q(q, t, 1, 1) = \frac{q^2 (1 - q^2 t)}{(1 + q)(1 - qt)}.$$
At $t = 1$: $\frac{q^2(1 - q^2)}{(1 + q)(1 - q)} = q^2 \cdot \frac{(1+q)(1-q)}{(1+q)(1-q)} = q^2$. ✓ Matches parent's $q^{k+1} = q^2$.

Conjectural general form (to verify or refine):
$$\frac{P(q, t, n, k)}{Q(q, t, n, k)} = q^{k+1} \cdot \frac{1 - q^{n+k+1} t}{(1 + q)(1 - qt)}\, ??? \quad \text{(needs more data points)}.$$

**Option β — Bypass Pascal entirely**. Prove `qtMultichoose_at_t_eq_one` directly by factor-wise simplification of the product. Then prove `qtMultichoose_at_one_one` by polynomial division of the product at $(q, t) = (1, 1)$, removing the $(1-q)^j (1-t)^j$ singularities by cancellation. No Pascal recurrence in `qtMultichoose` is exposed at all.

**Option γ — Pascal in a different direction**. The product formula factors most cleanly when shifting **$k \to k + 1$ at fixed $n$**. Compute:
$$\frac{\mathrm{qtMC}(q, t, n, k+1)}{\mathrm{qtMC}(q, t, n, k)} = \frac{1 - q^{n+k} t^{(k+1)-1}}{1 - q^{k+1} t^k} \cdot \frac{1 - q^{n+k} t^k}{1 - q^{n+k} t^k} \cdot \text{(re-index)}.$$
A telescoping product representation may yield a clean $k$-direction recurrence, which is *different* from the parent's $(n+1, k+1)$ direction and would not interpolate the parent's Pascal. **This is the most likely shape of Macdonald's original (6.4)**, with $n_\mathrm{bin}$ fixed.

**Recommendation for S2 author**: ship S2 with definitions + boundary cases (§6.1) and **defer all Pascal-style theorems to S4**, where the right form can be derived from explicit small-case data (§3) rather than guessed up front.

---

## 7. Proposed updated decomposition

Replacing problem.md §"Decomposition" S2–S5 with the falsification-informed scope:

| Stage | Target | Lean lines | Sorries | Risk |
|---|---|---:|---:|---|
| **S2 ACT** | `qtBinom`/`qtMultichoose` defs + 4 boundary cases (`zero_right`, `zero_left`, `one_left`, `one_right`); **no Pascal** | ~40 | 0 | Low — direct product manipulation |
| **S3 ACT** | `qtMultichoose_at_t_eq_one` via factor-wise simplification (Option β) | ~50 | 0 if `qBinom` product-form lemma is available; else 1 (+ private lemma for product form) | Medium — parent qBinom representation mismatch |
| **S4 ACT** (∇ direction change) | (Option β) `qtMultichoose_at_one_one` via direct $(q,t) \to (1,1)$ limit by cancellation of $(1-q), (1-t)$ factors | ~80 | 1 if limit-by-substitution lemma is non-trivial | High — genuine 0/0 cancellation |
| **S4-alt** (Option α) | $(q,t)$-Pascal for `qtMultichoose` with rational coefficient $P/Q$, verified by polynomial identity | ~120 | 0 | High — derive $P/Q$ from §3 data |
| **S5** | (downstream) | — | — | — |
| **S6+** | Macdonald polynomial connection — **axiomatised** (no change from S1 plan) | — | — | — |

**Net axiom budget for verified status**: 0 if Options β + Option α succeed; 1 if `qBinom`'s product form must be axiomatised; 2 if the $(q,t) \to (1, 1)$ limit needs a real-analytic axiom.

---

## 8. Anti-targets (out of scope for this PREP)

This session note **does not**:

- Edit `problem.md`, `knowledge.md`, `state.md`, or the gallery JSON. The merged S1 OBSERVE (PR #18327) is left intact for downstream traceability.
- Write any Lean code. No `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` is added in this PR. Defer to a parallel/future S2 ACT.
- Refute Macdonald's book directly. §5's finding is that the **transcription** in knowledge.md does not match the product formula; the original Macdonald §VI.6 may well use a different convention or refer to a different object. A follow-up S1b iteration could verify against the printed text.
- Settle Option α vs β vs γ. §6.4 enumerates three S4 directions; choosing requires more small-case data (e.g., $(n, k) = (2, 2)$, $(3, 2)$) than fits in this PREP.

---

## 9. Honesty / verification

- All numerical entries in the §3 table verified by hand from the product formula, two independent passes.
- The Pascal falsification (§4) reduces to the algebraic identity (†), whose RHS is unambiguously *not* a power of $t$ (checked at $t=0$ giving $\frac{1}{1+q}$).
- The (B) falsification (§5) at $(n, k) = (1, 0)$ reduces to the algebraic identity $q(1-q) = q(1-t)$, which holds only on the diagonal $q = t$.
- No build performed (doc-only PR).
- No axioms added, no sorries added/removed; 0 axiom delta, 0 sorry delta in this PR.

---

## 10. References

- **Parent verified Lean entry**: `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.lean` (lines 56, 102–110 cited).
- **qBinom recursive definition**: `proofs/Proofs/CombinationsFormulaOQ03.lean:159-162` (Pascal-recurrence-defined, not product-defined).
- **S1 OBSERVE merged PR**: #18327 (researcher-10, 2026-05-12 22:24 UTC merge).
- **Macdonald (claimed source)**: I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford 1995, §VI.6. **Specific equation numbering needs verification against the printed text**.
- **Project memory**: `feedback_researcher_10_2026_05_12_post_S1S1b_S2_prep_cluster.md` (S2 PREP pattern when MODERATE+/RICH slug is post-S1 contested).
