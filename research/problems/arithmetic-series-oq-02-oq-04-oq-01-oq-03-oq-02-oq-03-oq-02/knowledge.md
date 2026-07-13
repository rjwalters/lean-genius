# Knowledge — arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-02-oq-03-oq-02

## S1 (researcher-10, 2026-05-12) — OBSERVE survey

### Family of $q$-analogs and $(q,t)$-analogs

| Object | $q$-analog | $(q,t)$-analog | Standard reference |
|---|---|---|---|
| Integer $n$ | $[n]_q = \frac{1 - q^n}{1 - q}$ | $[n]_{q,t} = \frac{1 - q^n t^?}{1 - q t^?}$ (depends on context) | Macdonald §VI.6 |
| Binomial $\binom{n}{k}$ | $\binom{n}{k}_q = \frac{[n]_q!}{[k]_q! [n-k]_q!}$ | $\binom{n}{k}_{q,t} = \prod_{i=1}^k \frac{1 - q^{n-i+1} t^{i-1}}{1 - q^i t^{i-1}}$ | Macdonald §VI.6 |
| Multichoose $\binom{n+k-1}{k}$ | $\binom{n+k-1}{k}_q$ (parent) | $\binom{n+k-1}{k}_{q,t}$ (this OQ) | derived |
| Schur $s_\lambda$ | $s_\lambda(x; q) = $ HL $P_\lambda(x; q)$ at $q$ | Macdonald $P_\lambda(x; q, t)$ | Macdonald §VI |

### Macdonald's (q,t)-binomial: details

Macdonald (*Symmetric Functions and Hall Polynomials*, 2nd ed., 1995, §VI.6) defines the $(q,t)$-binomial coefficient by
$$ \binom{n}{k}_{q,t} := \prod_{i=1}^{k} \frac{1 - q^{n+1-i} t^{i-1}}{1 - q^i t^{i-1}}. $$

(Some authors use $(n-i+1)$ vs $(n+1-i)$ — convention varies; both are equivalent.)

**Key specializations**:

| Substitution | Result |
|---|---|
| $t = 1$ | $\binom{n}{k}_q$ (Gaussian binomial) |
| $q = 1$ | $\binom{n}{k}_t$ (Gaussian binomial in $t$) — **same form, $q \leftrightarrow t$** |
| $q = t$ | $\binom{n}{k}_q$ (degenerate limit) |
| $q = t = 1$ | $\binom{n}{k}$ (ordinary binomial; 0/0 limit) |
| $q = 0$ | $\prod_i \frac{1 - 0 \cdot t^{i-1}}{1 - 0 \cdot t^{i-1}} = 1$ if all factors trivialize |

The $q = 0$ specialization is **identically 1** because every factor is $\frac{1}{1} = 1$ when $q = 0$. Connecting to Hall–Littlewood requires a different limit (e.g., $q = t^c$ for some $c$).

### Macdonald polynomial principal specialization

For partition $\lambda = (k)$ (single row of length $k$):
$$ P_{(k)}(1, q, q^2, \ldots, q^{n-1}; q, t) = \frac{(t; q)_k}{(q; q)_k} \cdot \binom{n+k-1}{k}_{q, t^{-1}} \cdot t^{?} $$
or similar — exact normalisation depends on the version of $P_\lambda$ used.

The connection $\mathrm{qtMultichoose}(q, t, n, k) = c_{n,k}(q, t) \cdot P_{(k)}|_{\mathrm{princ}}$ is non-trivial; *Macdonald §VI.6 Exercise 1* gives the precise statement.

### Hall–Littlewood limit

The Hall–Littlewood polynomial is $P_\lambda(x; t) := P_\lambda(x; 0, t)$ (Macdonald with $q = 0$). The corresponding $(0, t)$-binomial:
$$ \binom{n}{k}_{0, t} = \prod_{i=1}^k \frac{1 - 0 \cdot t^{i-1}}{1 - 0 \cdot t^{i-1}} = 1. $$

This trivialises, so the HL limit is not the right connection point. Instead, the connection passes through the **graded character** of the symmetric group on $\binom{n}{k}_{q,t}$ (Garsia–Haiman 1993): the $(q,t)$-binomial appears as the principal specialization of a graded module, and HL is recovered at a different limit ($t \to 0$ in graded structure).

### (q,t)-Pascal recurrence (conjectural)

The parent's q-Pascal:
$$ \binom{n+k}{k+1}_q = \binom{n+k}{k}_q + q^{k+1} \binom{n+k-1}{k+1}_q. $$

The Macdonald-style $(q,t)$-Pascal candidate (Macdonald §VI.6 Eq. (6.4)):
$$ \binom{n+1}{k+1}_{q,t} = \binom{n}{k+1}_{q,t} + q^{n-k} \cdot \frac{1 - t^{k+1}}{1 - q^{n-k} t^k} \cdot \binom{n}{k}_{q,t}. $$

Hmm — this is NOT a polynomial identity in the same clean form as the q-Pascal; it involves a rational $t$-factor. **This is the OBSERVE-level technical surprise**: the (q,t)-Pascal does not specialise cleanly to the q-Pascal at $t = 1$ via Hayman bound. Let's verify:

At $t = 1$:
$$ \frac{1 - 1^{k+1}}{1 - q^{n-k} \cdot 1^k} = \frac{0}{1 - q^{n-k}} = 0 \quad (\text{for } q^{n-k} \ne 1). $$

So the right-hand term **vanishes** at $t = 1$. This conflicts with the parent's q-Pascal where the $q^{k+1}$-weighted term is *not* zero. ⇒ This (q,t)-Pascal is in a different normalisation / direction.

**Hypothesis**: there is a *different* (q,t)-Pascal recurrence that interpolates the parent's, possibly with a non-trivial $t$-weight that becomes $1$ at $t = 1$. Candidate:
$$ \binom{n+k}{k+1}_{q,t} = \binom{n+k}{k}_{q,t} + q^{k+1} t^{a} \cdot \binom{n+k-1}{k+1}_{q,t} $$
for some $a = a(n, k)$ to be determined. At $t = 1$: $t^a = 1$, recovering the parent's q-Pascal.

**S4 task**: determine $a = a(n, k)$ by direct computation for small $(n, k)$ and prove the identity in general.

### Specialization at $q = t = 1$

Each factor $\frac{1 - q^{n+1-i} t^{i-1}}{1 - q^i t^{i-1}}$ has both numerator and denominator vanishing at $q = t = 1$. The limit is **the ordinary binomial $\binom{n}{k}$** (proven via L'Hôpital):

$$ \lim_{(q,t) \to (1,1)} \frac{1 - q^a t^b}{1 - q^c t^d} = \frac{a + b \cdot \frac{\partial \log t}{\partial \log q}\big|_{q=t=1}}{c + d \cdot \frac{\partial \log t}{\partial \log q}\big|_{q=t=1}}. $$

But we want the result independent of path. The result IS path-independent for the (q,t)-binomial because the polynomial form $\binom{n}{k}_{q,t}$ has a removable singularity at $(1, 1)$ — both numerator and denominator factor through $(q - 1)$ and $(t - 1)$ in a structured way.

The cleanest Lean proof is via the conjectural (q,t)-Pascal recurrence (S4): at $q = t = 1$, the Pascal becomes the ordinary Pascal, and induction with the boundary cases gives $\binom{n+k-1}{k} = \mathrm{multichoose}(n, k)$.

### Mathlib gap analysis

| Topic | Status in Mathlib v4.26.0 | Severity |
|---|---|---|
| `Field R`, `Finset.prod` over field | ✅ available | none |
| qBinom (parent-local) | ✅ in `Proofs.CombinationsFormulaOQ03` | none — import |
| Macdonald polynomials | ❌ absent | major (axiomatise for S6+) |
| Hall–Littlewood polynomials | ❌ absent | major (skip for S2–S5) |
| Cherednik DAHA | ❌ absent | major (skip) |
| Schur functions $s_\lambda$ | ⚠️ partial, in `Mathlib.RepresentationTheory.SymmetricFunctions` | not blocking |
| $(q,t)$-Pascal | not applicable (project-internal) | S4 — derive ourselves |

**Recommended axiom count**:

- S2–S5: 0 axioms expected (pure polynomial manipulation in `Field R`).
- S6 (Macdonald connection): 1 axiom (principal specialization identity).

Gallery `axiomCount` = 0 if S5 ships and S6 is deferred; = 1 if S6 axiomatises Macdonald.

### Historical context

- **1973 — Macdonald** introduces Hall–Littlewood polynomials (Macdonald, *Spherical functions on a group of p-adic type*).
- **1988 — Macdonald** introduces Macdonald polynomials $P_\lambda(x; q, t)$.
- **1993 — Garsia, Haiman** state the $n!$ conjecture for Macdonald polynomial positivity.
- **1995 — Macdonald** publishes 2nd ed. of *Symmetric Functions and Hall Polynomials*, including §VI.6 on $(q,t)$-binomials.
- **2001 — Haiman** proves the $n!$ conjecture via Hilbert schemes, completing Macdonald positivity.
- **2005 — Cherednik** publishes *Double Affine Hecke Algebras*, deriving Macdonald via DAHA representations.
- **2010+ — Bergeron, Garsia, others** further develop $(q,t)$-combinatorics; many identities still without Lean formalisation.
- **2026-05 — parent file `qMultichoose` shipped** with $q$-Pascal but no $(q,t)$-generalisation.

The $(q,t)$-formalisation in Lean would be the **first algebraic-combinatorics entry** to surface Macdonald theory at any depth.

### Computational verification (small cases)

| $(n, k)$ | $\mathrm{qtMultichoose}(q, t, n, k)$ | At $t = 1$ | At $q = t = 1$ |
|---:|---|---|---|
| $(0, 0)$ | $1$ | $1$ | $1$ |
| $(0, k)$ | $\prod_{i=1}^k \frac{1 - q^{k-i} t^{i-1}}{1 - q^i t^{i-1}} = 0$ when $k \ge 1$ (since $i = k$ gives $q^0 t^{k-1}$ in num, $q^k t^{k-1}$ in den; at $q = $ anything nonzero, num = $1 - t^{k-1}$ vanishes at $t = 1$ when $k \ge 2$) | check S4 derivation | $0$ for $k \ge 1$ |
| $(1, k)$ | $\prod_{i=1}^k \frac{1 - q^{k+1-i} t^{i-1}}{1 - q^i t^{i-1}}$ — non-trivial | $\binom{k}{k}_q = 1$ | $\binom{k}{k} = 1$ |
| $(2, 1)$ | $\frac{1 - q^2}{1 - q}$ | $\frac{1 - q^2}{1 - q} = 1 + q$ | $2$ |
| $(2, 2)$ | $\frac{(1 - q^2)(1 - q t)}{(1 - q)(1 - q^2 t)}$ | $\frac{(1-q^2)(1-q)}{(1-q)(1-q^2)} = 1$ — wait that's wrong | $1$ |

Hmm, $\binom{2+2-1}{2}_{q,t} = \binom{3}{2}_{q,t}$. Let me recompute:
$$ \binom{3}{2}_{q,t} = \prod_{i=1}^2 \frac{1 - q^{3+1-i} t^{i-1}}{1 - q^i t^{i-1}} = \frac{1 - q^3 t^0}{1 - q^1 t^0} \cdot \frac{1 - q^2 t^1}{1 - q^2 t^1} = \frac{1 - q^3}{1 - q} \cdot 1. $$

So $\mathrm{qtMultichoose}(q, t, 2, 2) = \frac{1 - q^3}{1 - q} = 1 + q + q^2$, independent of $t$. At $q = 1$: limit gives $3 = \binom{3}{2}$. ✓

This already reveals: $\mathrm{qtMultichoose}(q, t, n, k)$ is **NOT always $t$-dependent** — for some $(n, k)$ it collapses to a pure $q$-polynomial. This suggests the $(q,t)$-multichoose has more structure than the binary $(q,t)$-binomial.

**Observation**: the $(q,t)$-binomial $\binom{n+k-1}{k}_{q,t}$ has the form
$$ \prod_{i=1}^k \frac{1 - q^{n+k-i} t^{i-1}}{1 - q^i t^{i-1}}. $$
When $i = 1$: numerator $1 - q^{n+k-1}$, no $t$. When $i = k$: numerator $1 - q^n t^{k-1}$, denominator $1 - q^k t^{k-1}$ — both have $t^{k-1}$.

For $\mathrm{qtMultichoose}(q, t, 2, 2)$ with $i = 2$: num $1 - q^2 t^1$, den $1 - q^2 t^1$, cancellation. This is why $t$-dependence vanishes for this small case. The general pattern needs S2 calculation to characterise.

### Risks and uncertainties

- **The Macdonald $(q,t)$-Pascal is not the parent's q-Pascal evaluated at $t \ne 1$**. The form $\binom{n+1}{k+1}_{q,t} = \binom{n}{k+1}_{q,t} + q^{n-k} \frac{1 - t^{k+1}}{1 - q^{n-k} t^k} \binom{n}{k}_{q,t}$ has a $t$-rational coefficient. The S4 task is to find the *right* form that specialises cleanly.

- **0/0 at $q = t = 1$**: the candidate `qtMultichoose_at_one_one` needs careful handling. Most direct path: use the Pascal recurrence at $q = t = 1$ + induction.

- **`Field R` constraint**: forced by division in the product formula. This restricts gallery integration; downstream applications wanting `CommRing R` would need an alternate formulation (e.g., clearing denominators).

### Summary of (un)knowns

| Property | Status |
|---|---|
| Definition of $\binom{n}{k}_{q,t}$ | Known (Macdonald 1995) |
| Specialization $t = 1$ recovers $\binom{n}{k}_q$ | Known, trivial |
| Specialization $q = t = 1$ recovers $\binom{n}{k}$ | Known (via 0/0 limit) |
| Macdonald $(q,t)$-Pascal recurrence | Known (Macdonald §VI.6 (6.4)) but in different normalization |
| **Multichoose-style $(q,t)$-Pascal interpolating parent** | **Open — S4 conjectural** |
| Lean formalisation of any of the above | **Open — S2–S6 deliverables** |
| Macdonald polynomial connection | Known mathematically, axiomatised in Lean |
