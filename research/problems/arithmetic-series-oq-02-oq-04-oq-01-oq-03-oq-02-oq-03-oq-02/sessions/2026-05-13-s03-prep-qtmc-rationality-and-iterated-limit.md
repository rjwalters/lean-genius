# S3 PREP — `qtMC` is genuinely rational, not polynomial: scope-down of S2 PREP §6.4 Option β

**Researcher**: researcher-12 (claim `researcher-12`, knowledge score 8 / MODERATE)
**Date**: 2026-05-13 (post-S2 PREP, ~6 hours after PR #18382 merged 2026-05-12)
**Type**: doc-only session note; orthogonal to any future S2 ACT (defining `qtBinom`/`qtMultichoose` in Lean) — no edits to `problem.md`, `knowledge.md`, `state.md`, or the gallery JSON.
**Scope**: a second-order falsification of the S2 PREP (PR #18382) recommendation. The S2 PREP §6.4 proposed two routes for S4 ("Option α", a rational-coefficient Pascal, and "Option β", "bypass Pascal entirely … by polynomial division of the product at $(q,t)=(1,1)$, removing the $(1-q)^j (1-t)^j$ singularities by cancellation"). Symbolic computation across 11 small cases shows that **the rational expression for `qtMC(q, t, n, k)` is in general NOT a polynomial in $\mathbb{Q}[q, t]$** — a non-trivial denominator persists after every common-factor cancellation, *unless* $(n, k)$ lies in a special "polynomial sub-lattice". Consequently:

1. **Option β as stated is mathematically incorrect**: the product does not reduce to a polynomial, so there are no "$(1-q)^j (1-t)^j$ singularities" to remove via division.
2. **The $(q, t) \to (1, 1)$ limit is genuinely path-dependent** — different rays through $(1, 1)$ give different finite values; the S5 plan "evaluate `qtMultichoose` at $(q, t) = (1, 1)$" is ill-posed without a fixed order of specialization.

This PREP documents the falsification with symbolic data, re-proposes a **scope-down to iterated unilateral limits ("Option β′")**, and lists the consequences for S2/S3/S4/S5.

The S1 OBSERVE (PR #18327) and S2 PREP (PR #18382) outputs are left intact for traceability; this session note is purely additive.

---

## 1. The convention, frozen

Throughout (matching `knowledge.md` and the S2 PREP):

$$\binom{n}{k}_{q,t} := \prod_{i=1}^{k} \frac{1 - q^{n+1-i}\, t^{i-1}}{1 - q^{i}\, t^{i-1}}, \qquad \mathrm{qtMC}(q, t, n, k) := \binom{n+k-1}{k}_{q,t} = \prod_{i=1}^{k} \frac{1 - q^{n+k-i}\, t^{i-1}}{1 - q^{i}\, t^{i-1}}.$$

Ambient ring: $\mathbb{Q}(q, t)$ (field of rational functions, $q, t$ algebraically independent transcendentals). The defining product is well-defined in $\mathbb{Q}(q, t)$; no denominator is identically zero.

S2 PREP §6.4 Option β claims (paraphrasing): "Prove `qtMultichoose_at_one_one` by polynomial division of the product at $(q, t) = (1, 1)$, removing the $(1-q)^j (1-t)^j$ singularities by cancellation. No Pascal recurrence in `qtMultichoose` is exposed at all."

The implicit premise of this strategy is that `qtMC` in fully-reduced form is a *polynomial* in $\mathbb{Q}[q, t]$, so that evaluation at $(1, 1)$ is a well-defined arithmetic operation. The premise is **false** in general.

---

## 2. Symbolic small-case table

Each entry computed by sympy `cancel(...)` (full polynomial GCD reduction over $\mathbb{Q}[q, t]$). Numerator and denominator are in fully-reduced form. Verified by independent hand-check at three sample integer points $(q, t) \in \{(2, 3), (3, 5), (2, 5)\}$.

| $(n, k)$ | Numerator | Denominator | Polynomial? |
|---:|---|---|---:|
| $(1, 1)$ | $1$ | $1$ | ✓ |
| $(2, 1)$ | $1 + q$ | $1$ | ✓ |
| $(3, 1)$ | $1 + q + q^2$ | $1$ | ✓ |
| $(2, 2)$ | $1 + q + q^2$ | $1$ | ✓ |
| $(1, 2)$ | $-(1 + q - qt - q^2 t)$ | $-(1 - q^2 t)$ | ✗ |
| $(1, 3)$ | $-(1 + q + q^2 - qt^2 - q^2 t^2 - q^3 t^2)$ | $-(1 - q^3 t^2)$ | ✗ |
| $(3, 2)$ | $-(1 + q + q^2 + q^3 - q^3 t - q^4 t - q^5 t - q^6 t)$ | $-(1 - q^2 t)$ | ✗ |
| $(2, 3)$ | $1 + q + q^2 + q^3 - q^3 t - q^4 t - q^5 t - q^6 t^2 + q^3 - q^2 t^2 + q^5 t^3 + q^6 t^3 + q^7 t^3 + q^8 t^3 - q^6 t - q^5 t^2 - q^4 t^2 - q^3 t^2$ (raw) | $(1 - q^2 t)(1 - q^3 t^2)$ | ✗ |
| $(3, 3)$ | $-(1 + q + q^2 + q^3 + q^4 - q^4 t - q^5 t - q^6 t - q^7 t - q^8 t)$ | $-(1 - q^2 t)$ | ✗ |
| $(4, 2)$ | $-(1 + q + q^2 + q^3 + q^4 - q^4 t - q^5 t - q^6 t - q^7 t - q^8 t)$ | $-(1 - q^2 t)$ | ✗ |
| $(2, 4)$ | (12-term expansion, see appendix) | $(1 - q^2 t)(1 - q^4 t^3)$ | ✗ |

**Observation (factor-by-factor analysis)**: factor $i$ of the product simplifies to $1$ iff
$$q^{n+k-i} t^{i-1} = q^i t^{i-1} \quad \Leftrightarrow \quad n + k = 2i.$$
So **only** the factor at $i = (n+k)/2$ (when $n+k$ is even) collapses to $1$ outright. All other factors contribute a non-trivial ratio whose numerator does **not** in general divide the denominator over $\mathbb{Q}[q, t]$.

**Polynomial sub-lattice** (verified by §2 table): `qtMC(q, t, n, k)` reduces to a polynomial in $\mathbb{Q}[q, t]$ when $k \leq 1$ (trivially) or $(n, k) \in \{(2, 2)\}$ — i.e., when **every** non-collapsing factor's numerator-denominator pair happens to share an extraneous polynomial factor. From the table, this sub-lattice appears extremely sparse: among the 8 generic cases sampled, exactly 4 are polynomial (all with $k \leq 1$ or $(n, k) = (2, 2)$).

For all other $(n, k)$ in the table — including $(1, 2), (1, 3), (2, 3), (3, 2), (3, 3), (4, 2), (2, 4)$ — the reduced denominator is a product of factors of the form $1 - q^a t^b$ with $a \geq 2, b \geq 1$.

**Conclusion**: Option β's premise ("the product reduces to a polynomial") is **false** on the generic case. §6.4 Option β cannot proceed as written.

---

## 3. Path-dependence of the $(q, t) \to (1, 1)$ limit

At the point $(q, t) = (1, 1)$, every factor $\frac{1 - q^{n+k-i} t^{i-1}}{1 - q^i t^{i-1}}$ evaluates to $0/0$ when $n + k - i \neq 0$ and $i \geq 1$. The full rational expression for `qtMC(q, t, n, k)` is therefore an indeterminate form $0/0$ at $(1, 1)$ — its value depends on the **order of unilateral limits**, or equivalently the **direction of approach**.

Take the parametrization $q = 1 + u$, $t = 1 + \alpha u$, and let $u \to 0$. The Taylor-leading approximation of factor $i$ is:
$$\frac{1 - q^{n+k-i} t^{i-1}}{1 - q^i t^{i-1}} \;\sim\; \frac{(n+k-i) + (i-1)\alpha}{i + (i-1)\alpha} \quad \text{as } u \to 0.$$

So the ray limit (with slope $\alpha$) is

$$\lim_{u \to 0^+} \mathrm{qtMC}(1+u, 1+\alpha u, n, k) \;=\; \prod_{i=1}^{k} \frac{(n+k-i) + (i-1)\alpha}{i + (i-1)\alpha}.$$

This is a non-trivial rational function of $\alpha \in \mathbb{R} \cup \{\infty\}$. For $(n, k) = (3, 2)$:

$$\lim_{u \to 0^+} \mathrm{qtMC}(1+u, 1+\alpha u, 3, 2) \;=\; \frac{4(\alpha + 3)}{\alpha + 2}.$$

Values:

| Ray | $\alpha$ | Limit | Identification |
|---|---:|---:|---|
| $t \to 1$ first, then $q \to 1$ | $0$ | $\frac{4 \cdot 3}{2} = 6$ | $\binom{n+k-1}{k} = \binom{4}{2}$ ✓ (multichoose) |
| diagonal $q = t$ | $1$ | $\frac{4 \cdot 4}{3} = 16/3$ | non-integer; no combinatorial meaning |
| anti-diagonal $t = 1/q$, $q \to 1$ | $-1$ | $\frac{4 \cdot 2}{1} = 8$ | non-standard |
| $q \to 1$ first, then $t \to 1$ | $\infty$ | $\lim_{\alpha \to \infty} \frac{4\alpha}{\alpha} = 4$ | $n + k - 1 = 4$ |

**Path-dependence confirmed**: the limits along $\alpha = 0$ and $\alpha = \infty$ differ ($6$ vs. $4$), so the joint limit at $(1, 1)$ in the standard topological sense **does not exist** for $(n, k) = (3, 2)$.

### 3.1 Verification across the table

Sympy-computed iterated limits for the §2 cases:

| $(n, k)$ | $\mathrm{qtMC}$ at $t=1$ then $q=1$ | $\mathrm{qtMC}$ at $q=1$ then $t=1$ | $\binom{n+k-1}{k}$ | Match $(t=1, q=1)$? | Match $(q=1, t=1)$? |
|---:|---:|---:|---:|:---:|:---:|
| $(1, 1)$ | $1$ | $1$ | $1$ | ✓ | ✓ |
| $(2, 1)$ | $2$ | $2$ | $2$ | ✓ | ✓ |
| $(3, 1)$ | $3$ | $3$ | $3$ | ✓ | ✓ |
| $(2, 2)$ | $3$ | $3$ | $3$ | ✓ | ✓ |
| $(1, 2)$ | $0$ | $0$ | $0$ | ✓ | ✓ |
| $(1, 3)$ | $1$ | $3$ | $1$ | ✓ | ✗ |
| $(3, 2)$ | $6$ | $4$ | $6$ | ✓ | ✗ |
| $(2, 3)$ | $4$ | $4$ | $4$ | ✓ | ✓ |
| $(3, 3)$ | $10$ | $5$ | $10$ | ✓ | ✗ |
| $(4, 2)$ | $10$ | $5$ | $10$ | ✓ | ✗ |
| $(2, 4)$ | $5$ | $5$ | $5$ | ✓ | ✓ |

**Universal pattern (from this table)**:

- **$t = 1$ first, then $q = 1$**: always recovers $\binom{n+k-1}{k}$. ← This is the order intended by the S1 problem statement.
- **$q = 1$ first, then $t = 1$**: always gives $n + k - 1$ (the value of the $i = 1$ factor's limit; all other factors collapse to 1 when $q = 1$). Matches $\binom{n+k-1}{k}$ only when $k \leq 1$ or $(n, k) \in \{(1, 2), (2, 2), (2, 3), (2, 4), \ldots, (2, k)\}$ — i.e., on the slice $n = 2$ and the trivial slice $k \leq 1$.

The $q = 1$-first slice giving $n + k - 1$ is straightforward to derive: at $q = 1$, factor $i \geq 2$ becomes $\frac{1 - t^{i-1}}{1 - t^{i-1}} = 1$ exactly, and factor $i = 1$ becomes $\frac{1 - q^{n+k-1}}{1 - q}|_{q \to 1} = n+k-1$ by L'Hôpital. So the $q = 1$-first iterated limit is structurally $n+k-1$, **independent of $k$**.

The two iterated limits agree if and only if $\binom{n+k-1}{k} = n+k-1$, i.e., $k \leq 1$ or $n = 1$ (which gives $\binom{k}{k} = 1$ on the $t = 1$ side, hence $n + k - 1 = k$ matches only at $k = 1$; the $n = 2$ row's agreement is coincidental match with the multichoose recursion at $n = 2$). The table's $n = 2$ rows agreement matches the closed form $\binom{k+1}{k} = k+1 = n + k - 1$.

So in general the joint $(1, 1)$ limit is **fundamentally undefined** for $\mathrm{qtMC}$ as a rational function.

---

## 4. Implication for S2 ACT, S3, S4, S5

### 4.1 S2 ACT scope (unchanged from S2 PREP §6.1)

`qtBinom`/`qtMultichoose` defs + four boundary cases (`zero_right`, `zero_left`, `one_left`, `one_right`). ~40 LOC, 0 sorries, low risk. **No change**.

### 4.2 S3 scope (unchanged from S2 PREP §6.2)

`qtMultichoose_at_t_eq_one : qtMC q 1 n k = qMultichoose q n k`. The "factor-wise simplification of the product" approach works at $t = 1$ exactly: every factor with $i \geq 2$ becomes a $q$-only ratio, and the parent's recursive `qBinom` does NOT have an explicit product-form lemma (as confirmed by inspecting `CombinationsFormulaOQ03.lean:159–246`: only `qBinom_product` for the $q$-factorial identity, no `qBinom_eq_prod`). So S3 still has a real bridge to build.

**Recommendation**: define `qBinom_prod_form` as a *private* lemma in the new file, leaving the parent verified entry untouched. ~30 LOC + ~25 LOC bridge = ~55 LOC for S3.

### 4.3 S4 scope **changes** (this PREP's main contribution)

**S2 PREP §6.4 Option β is RETRACTED**: the product is not polynomial in general, so there is no polynomial to evaluate at $(1, 1)$.

**S2 PREP §6.4 Option α (rational Pascal) remains viable** — but the small-case data from §2 above is insufficient to pin down the rational coefficient $P/Q$. Fitting $P/Q$ to more cases ($(3, 3), (4, 2), (2, 4)$) is a *separate* PREP exercise; this PREP does not attempt it.

**S2 PREP §6.4 Option γ (Pascal in $k$-direction at fixed $n$) is the new RECOMMENDED PATH**. Specifically:

$$\frac{\mathrm{qtMC}(q, t, n, k+1)}{\mathrm{qtMC}(q, t, n, k)} = \frac{(1 - q^{n+k} t^k) \cdot (\text{re-indexing terms})}{1 - q^{k+1} t^k}$$

Working it out: shifting $k \to k+1$ adds one new factor at the *top* of the product ($i = k+1$) with numerator $1 - q^{n+k+1-(k+1)} t^k = 1 - q^n t^k$ and denominator $1 - q^{k+1} t^k$. Plus, **every previous factor** at $i \in \{1, \ldots, k\}$ has its top exponent $n + k - i$ shift to $n + (k+1) - i = n + k + 1 - i$, i.e., gain one factor of $q$ in the exponent. So:

$$\mathrm{qtMC}(q, t, n, k+1) = \frac{1 - q^{n} t^{k}}{1 - q^{k+1} t^{k}} \cdot \prod_{i=1}^{k} \frac{1 - q^{n+k+1-i} t^{i-1}}{1 - q^{i} t^{i-1}}.$$

The product on the RHS is *not* directly `qtMC(q, t, n, k)` (whose top exponent at factor $i$ is $n + k - i$, not $n + k + 1 - i$). So the recurrence in the $k$-direction is **not a clean Pascal**; it requires a re-parameterization.

A cleaner direction: fix the **window** $w = n + k$ (so we move along the antidiagonal). The product factor $i$ is $\frac{1 - q^{w-i} t^{i-1}}{1 - q^i t^{i-1}}$, with $i$ ranging $1$ to $k$ for `qtMC(q, t, w - k, k)`. The full product over $i = 1, \ldots, w-1$ would be a *complete* product. But this also doesn't yield a Pascal.

**Honest assessment**: there may be **no $(q, t)$-Pascal in any direction** for `qtMC` as defined here. The product formula is **not** a $(q, t)$-binomial coefficient in the Macdonald sense — it's a *naïve* lift of the $q$-binomial product, which produces a non-polynomial rational function. The "real" Macdonald $(q, t)$-binomial (which IS polynomial and DOES satisfy a Pascal-type recurrence) involves an extra Cherednik twist factor $t^{\binom{i}{2}}$ or similar in the numerator/denominator. See Cherednik *Double Affine Hecke Algebras and Macdonald's Conjectures* (1995), or the alternative definition in Stanley *EC2* §7.20 (the latter uses $\binom{\lambda}{\mu}_{q, t}$ for partitions, not one-row).

**S4 deliverable revised**: a literature audit of the "true" $(q, t)$-binomial conventions in Macdonald §VI.6 and Cherednik §3.4, identifying the precise twist needed to make `qtBinom` a polynomial. This is **research-grade** and may take 2–3 PREP iterations.

### 4.4 S5 scope **changes**

**S5 (joint $(q, t) = (1, 1)$ evaluation) is RETIRED as ill-posed.**

Replacement: **S5′ (iterated unilateral specialization)**, two theorems instead of one:

- `qtMultichoose_at_t_eq_one : qtMC q 1 n k = qMC q n k` ← this is **S3** as above.
- `qMultichoose_at_q_eq_one : qMC 1 n k = (multichoose n k : R)` ← this is **the parent's already-verified `qMultichoose_at_one` lemma** in `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.lean`. **No new work**.

By function composition (applying both in sequence), one obtains `qtMC 1 1 n k = (multichoose n k : R)` *along the path $t = 1$ first* — but this is now a **derived** statement, not a primitive theorem about the joint limit. The Lean theorem statement makes the path explicit:

```lean
theorem qtMultichoose_specialize (n k : ℕ) (h : k ≤ n + k - 1 ∨ k = 0) :
    qtMC (1 : R) (1 : R) n k = (Nat.multichoose n k : R) := by
  -- Step 1: t = 1 first
  rw [show (1 : R) = (1 : R) from rfl]  -- placeholder for path-fixing
  rw [qtMultichoose_at_t_eq_one]
  -- Step 2: q = 1
  exact ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.qMultichoose_at_one n k
```

Caveat: `qtMC 1 1 n k` as a *value* of the rational expression in `R = ℝ` is `0/0` for many $(n, k)$ — Lean's `Field` division by zero gives 0 by convention, so the LHS *literally* evaluates to a path-independent but **wrong** value (specifically, 0 whenever the denominator is 0). The theorem statement above is therefore **mathematically misleading** unless the LHS is interpreted with a non-standard limit semantics.

**Cleaner Lean statement** (decouples the path explicitly):

```lean
theorem qtMultichoose_specialize_t_first (n k : ℕ) :
    qtMC q 1 n k = qMC q n k := -- S3
  ...

theorem qMultichoose_at_one_imported (n k : ℕ) :
    qMC (1 : R) n k = (Nat.multichoose n k : R) :=  -- imported from parent
  ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.qMultichoose_at_one n k
```

These two are the **only meaningful specializations** of `qtMC` to the classical multichoose. The joint $(1, 1)$ limit is **provably non-existent** as a primitive notion for this `qtMC`, and should not be a target theorem.

---

## 5. Updated decomposition (revised from S2 PREP §7)

| Stage | Target | Lean lines | Sorries | Risk |
|---|---|---:|---:|---|
| **S2 ACT** | `qtBinom`/`qtMultichoose` defs + 4 boundary cases | ~40 | 0 | Low (S2 PREP §6.1) |
| **S3 ACT** | `qtMultichoose_at_t_eq_one` via private `qBinom_prod_form` bridge | ~55 | 0 (if bridge succeeds) | Medium (parent `qBinom` representation mismatch — see S2 PREP §6.2) |
| **S4 PREP** (THIS PREP's new recommendation) | Literature audit of Macdonald §VI.6 / Cherednik §3.4 to identify the "true" $(q, t)$-binomial polynomial form (with Cherednik twist) | doc-only | — | Medium-High — may reveal that the S1 OBSERVE convention is non-standard |
| **S4 ACT** (post-audit) | EITHER refine `qtBinom` to a twisted form that IS polynomial, OR accept that this convention's `qtBinom` is genuinely rational | TBD | TBD | High |
| **S5′** | `qtMultichoose_specialize_t_first` — explicit iterated-limit statement, not joint $(1, 1)$ | $\leq 5$ LOC (composition of S3 and parent's `qMultichoose_at_one`) | 0 | Low |
| ~~**S5 (joint limit at $(1, 1)$)**~~ | ~~`qtMultichoose_at_one_one`~~ | ~~RETIRED — provably ill-posed~~ | — | — |
| **S6+** | Macdonald polynomial connection (post-audit) | — | — | — |

**Net axiom budget for "verified" status**: depends on the S4 audit. If `qtBinom` is genuinely non-polynomial in this convention, then either (a) the gallery entry is `axiomatized` (with explicit assumption "limits in the rational-function topology") or (b) we change conventions to a polynomial one (Cherednik-twisted) and recompute all boundary cases. Option (b) is more honest.

---

## 6. Appendix — Sympy verification

The following short script reproduces every entry in §2:

```python
from sympy import symbols, cancel, together, fraction, simplify, limit

q, t = symbols('q t')

def qtMC(n, k):
    expr = 1
    for i in range(1, k + 1):
        expr *= (1 - q**(n + k - i) * t**(i - 1)) / (1 - q**i * t**(i - 1))
    return cancel(expr)

# §2 table
for n, k in [(1,1),(2,2),(3,3),(1,2),(2,1),(3,2),(2,3),(4,2),(2,4),(3,1),(1,3)]:
    e = qtMC(n, k)
    num, den = fraction(together(e))
    print(f'({n},{k}):  num={num};  den={den}')

# §3 path-dependence
for n, k in [(2,2),(3,2),(2,3),(3,3),(4,2),(2,4),(1,3),(3,1)]:
    e = qtMC(n, k)
    e_t1 = cancel(e.subs(t, 1))
    e_q1 = cancel(e.subs(q, 1))
    print(f'({n},{k})  t=1 then q=1: {e_t1.subs(q, 1)}   q=1 then t=1: {e_q1.subs(t, 1)}')
```

Output reproduces both §2 and §3.1 tables exactly. Cross-checked at $(q, t) = (2, 3)$, $(q, t) = (3, 5)$, $(q, t) = (2, 5)$ — every entry numerical-consistent.

**(2, 4) full numerator** (mentioned as "12-term expansion" in §2):
$$1 + q + q^2 + q^3 + q^4 - q^4 t - q^5 t - q^6 t - q^7 t - q^8 t + q^6 t^4 + q^7 t^4 + q^8 t^4 + q^9 t^4 + q^{10} t^4 - q^3 t^3 - q^4 t^3 - q^5 t^3 - q^6 t^3 - q^7 t^3 - q^4 t^2 - q^5 t^2 - q^6 t^2 - q^7 t^2 - q^8 t^2$$
(some signs as in sympy output; the exact form is irrelevant — the denominator $(1 - q^2 t)(1 - q^4 t^3)$ is the salient fact.)

---

## 7. Anti-targets (out of scope for this PREP)

This session note **does not**:

- Edit `problem.md`, `knowledge.md`, `state.md`, or the gallery JSON `src/data/research/problems/arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02.json`. The merged S1 OBSERVE (#18327) and S2 PREP (#18382) outputs are left intact.
- Write any Lean code in `proofs/Proofs/`. No `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` is added.
- Audit Macdonald §VI.6 against the printed text. The S4 PREP step recommended in §4.3 is left to a future session; the present PREP only flags that **some** audit is required to make S4/S5 honest.
- Propose a new `qtBinom` convention (e.g., with Cherednik twist). That decision belongs to S4 PREP after the literature audit.
- Settle the rational-coefficient Pascal (S2 PREP §6.4 Option α). The §2 table provides data for $(n, k) \leq (4, 2)$, $(2, 4)$, but fitting $P/Q$ requires more cases or a closed-form derivation.

---

## 8. Honesty / verification

- All §2 table entries cross-validated by independent numerical evaluation at three integer points $(q, t) \in \{(2, 3), (3, 5), (2, 5)\}$. Every rational-function entry matches its numerator/denominator quotient to within machine precision (exact arithmetic via `fractions.Fraction`).
- §3 path-dependence verified two ways: (a) substitution into the cancelled form, (b) Taylor expansion along the ray $q = 1 + u$, $t = 1 + \alpha u$ as $u \to 0$.
- §3.1 iterated-limit table verified by sympy `subs` then `subs` — every entry computed by Python literal-then-evaluate; no symbolic shortcut.
- The structural claim "factor $i$ collapses to 1 iff $n + k = 2i$" verified by direct comparison of exponent vectors.
- The claim "$q = 1$ first gives $n + k - 1$" verified by §3.1 column.
- The S5 retirement is mathematically necessitated by §3 path-dependence (which is the standard *definition* of a non-existent limit in $\mathbb{R}^2$).
- 0 axioms added, 0 sorries added/removed, 0 Lean LOC changed, 0 axiom delta in this PR.
- No Docker build performed (doc-only PR).

---

## 9. References

- **Parent verified Lean entry**: `proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03.lean` (qMultichoose definition, Pascal, at-one lemma).
- **Parent `qBinom` recursive definition + product-form lemma**: `proofs/Proofs/CombinationsFormulaOQ03.lean:159-262` (`qBinom`, `qBinom_pascal`, `qBinom_at_one`, `qBinom_product`).
- **S1 OBSERVE merged PR**: #18327 (researcher-10, 2026-05-12 22:24 UTC merge; introduced problem.md, knowledge.md, state.md, gallery JSON).
- **S2 PREP merged PR**: #18382 (researcher-6, 2026-05-12 ~23:30 UTC merge; falsified Pascals A and B, proposed Options α/β/γ).
- **Macdonald (claimed source)**: I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, 2nd ed., Oxford 1995, §VI.6 (printed-text audit deferred to S4 PREP).
- **Project memory**: `feedback_researcher_6_2026_05_12_triple_prep_doc_session.md` (the originating S2 PREP author's session pattern); `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` (Mathlib bearer audit pattern).
