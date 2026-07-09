# Problem: Riemann Surface Structure of z^(p/q)

**Slug**: de-moivre-oq-03-oq-02
**Created**: 2026-07-09T16:03:13-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For coprime integers $p, q$ with $q \geq 1$, formalize the Riemann surface $X$ of the multivalued map $z \mapsto z^{p/q}$ on the punctured plane $\mathbb{C}^\ast = \mathbb{C} \setminus \{0\}$. Concretely:

$$
X \;=\; \{(z, w) \in \mathbb{C}^\ast \times \mathbb{C} : w^{q} = z^{p}\}, \qquad \pi : X \to \mathbb{C}^\ast,\ \pi(z,w) = z,
$$

together with the following claims:

1. **Covering.** With $\gcd(p,q)=1$, the projection $\pi$ is a holomorphic $q$-sheeted covering map of $\mathbb{C}^\ast$; every fiber $\pi^{-1}(z)$ has exactly $q$ points, namely $\{\zeta_0 \cdot \omega^k : k = 0,\dots,q-1\}$ with $\zeta_0$ a chosen value of $z^{p/q}$ and $\omega = e^{2\pi i/q}$.

2. **Monodromy.** Analytic continuation of a local branch around the loop $\gamma(t) = z_0 e^{2\pi i t}$ ($t\in[0,1]$) induces the deck transformation $\sigma : (z,w) \mapsto (z, \omega^{p} w)$. The monodromy / deck group is cyclic:
$$
\mathrm{Deck}(X/\mathbb{C}^\ast) \;\cong\; \mathbb{Z}/q\mathbb{Z}, \qquad \sigma \text{ a generator (since } \gcd(p,q)=1).
$$

3. **Branch point.** The origin is the unique branch point: the compactified curve $\overline{X} = \{w^q = z^p\} \subseteq \mathbb{P}^1 \times \mathbb{P}^1$ (or its normalization) has a single point over $z=0$ where the $q$ sheets coalesce, with local model $w = t^{?}$, and $\pi$ is unramified over all of $\mathbb{C}^\ast$.

4. **Genus / global structure.** For $\gcd(p,q)=1$ the (normalized, compactified) curve $w^q = z^p$ is rational — it is parametrized by $z = t^q,\ w = t^p$ — hence biholomorphic to $\mathbb{P}^1$; its function field is $\mathbb{C}(z^{1/q})$, a degree-$q$ cyclic (Kummer) extension of $\mathbb{C}(z)$.

### Plain Language

The expression $z^{p/q}$ does not have a single value: taking a $q$-th root of a complex number gives $q$ different answers. Instead of forcing a choice (a "branch cut"), the natural fix is to glue $q$ copies of the plane together into one connected surface — the *Riemann surface* — on which $z^{p/q}$ becomes a genuine, single-valued function. This problem asks to build that surface in Lean and prove its defining features: it wraps $q$ times around the origin (a $q$-sheeted covering), walking once around $z=0$ cyclically permutes the $q$ values (monodromy of order $q$), the origin is the only place the sheets pinch together (the branch point), and the whole object is the algebraic curve $w^q = z^p$, which for coprime $p,q$ is just a sphere in disguise.

### Why This Matters

- It upgrades the source entry (De Moivre for fractional exponents, which enumerates the $q$ roots pointwise and picks a principal branch) to the *global* geometric object that explains *why* there are $q$ roots and how they interconvert as $z$ moves.
- It is the canonical first nontrivial example in Riemann surface theory — the model for branch points, monodromy, and multivalued algebraic functions.
- Mathlib currently has essentially no theory of Riemann surfaces or monodromy of covering maps over $\mathbb{C}$; even a careful partial formalization (the covering-map + cyclic deck-group core) would be a genuine addition.
- It connects three areas already in the gallery: complex `cpow`/roots of unity, the cyclic group $\mu_q$, and (via the Kummer extension $\mathbb{C}(z^{1/q})/\mathbb{C}(z)$) Galois theory of cyclotomic/radical extensions.

## Known Results

### What's Already Proven

- **De Moivre OQ-03** (this gallery, `de-moivre-oq-03`) — pointwise enumeration of the $q$ roots $\zeta_k = \exp(i(p\theta + 2\pi k)/q)$, their distinctness, the factorization $\zeta_k = \zeta_0\,\omega_k$, and principal-branch consistency via `Complex.cpow`. This is the fiber-level content of claim (1).
- **Classical complex analysis** — the Riemann surface of $z^{p/q}$, its $q$-sheeted branched-cover structure, cyclic monodromy $\mathbb{Z}/q\mathbb{Z}$, and rationality of $w^q = z^p$ for $\gcd(p,q)=1$ are all standard textbook results (Forster, *Lectures on Riemann Surfaces*; Miranda, *Algebraic Curves and Riemann Surfaces*; Needham, *Visual Complex Analysis*). The mathematics is completely settled; only the *formalization* is open.
- **Roots of unity in Mathlib** — the cyclic group structure of $\mu_q$ (`rootsOfUnity`, `Complex.isPrimitiveRoot_exp`) is available.

### What's Still Open

- A Lean formalization of the Riemann surface $X = \{w^q = z^p\}$ as a complex manifold / covering space of $\mathbb{C}^\ast$.
- A formal statement and proof that the deck/monodromy group is cyclic of order $q$ with the explicit generator $(z,w)\mapsto(\omega^p w)$.
- Formal identification of the origin as the unique branch point and (in the compactified/normalized model) the rationality/genus-0 conclusion for $\gcd(p,q)=1$.

### Our Goal

Do not attempt the full complex-manifold apparatus at once. The concrete target scope is:

1. Define $X = \{(z,w) : z \neq 0,\ w^q = z^p\}$ as a subset/structure over $\mathbb{C}^\ast$ and prove fibers have exactly $q$ elements (reusing OQ-03's enumeration and distinctness).
2. Define the sheet-permutation map $\sigma(z,w) = (z, \omega^p w)$, prove it is a fixed-point-free (over $\mathbb{C}^\ast$) automorphism of $X$ over $\mathbb{C}^\ast$, that it has order $q$ (using $\gcd(p,q)=1$), and that $\langle\sigma\rangle \cong \mathbb{Z}/q\mathbb{Z}$ acts simply transitively on each fiber.
3. As a stretch, capture the *analytic* monodromy: continuing $\zeta_0(\theta) = \exp(ip\theta/q)$ as $\theta \to \theta + 2\pi$ sends $\zeta_0 \mapsto \omega^p\zeta_0$, matching $\sigma$.

The manifold/covering topology and the compactification/genus statement (claims 3–4) are explicitly out of the initial scope and flagged as follow-on work.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| de-moivre-oq-03 | Direct parent; supplies fiber enumeration, distinctness, and the $\zeta_k=\zeta_0\omega_k$ factorization that *is* the fiber of $X$ | `Complex.cpow`, `exp`/`log`, `exp_eq_exp_iff_exists_int`, roots of unity |
| de-moivre | Base integer De Moivre; grounds the exponential parametrization $z=e^{i\theta}$ | Euler's formula, induction |
| euler-identity | $e^{i\pi}=-1$; the $q=2$ monodromy $\zeta_1=-\zeta_0$ is its concrete instance | Euler's formula |
| primitive-roots | The generator $\omega^p$ of the cyclic monodromy is a primitive $q$-th root of unity exactly when $\gcd(p,q)=1$ | cyclic group $\mu_q$, primitivity |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Algebraic/set-theoretic core first**: Model $X$ as `{ zw : ℂ × ℂ // zw.1 ≠ 0 ∧ zw.2 ^ q = zw.1 ^ p }`. Prove fiber cardinality $q$ by transporting OQ-03's enumeration; define $\sigma$ and get the cyclic group action via `zpowers`/`Equiv.Perm` and `IsPrimitiveRoot`.
   - Why it might work: reuses a *verified* gallery proof for the hardest analytic input (root count/distinctness); the deck-group part is finite-group + roots-of-unity algebra Mathlib handles well.
   - Risk: this captures the covering *combinatorially* but not the *holomorphic covering-map* structure; a reviewer may want at least local sheet parametrizations to justify calling it a Riemann surface.

2. **Approach B — Covering-space / monodromy via analytic continuation**: Work over $\theta \in \mathbb{R}$ with the explicit branch $\theta \mapsto \exp(ip\theta/q)$ on $\mathbb{C}^\ast$ (or on a fundamental domain), and prove the loop $\theta \mapsto \theta + 2\pi$ realizes the permutation $\zeta_0 \mapsto \omega^p\zeta_0$. Package the monodromy as a homomorphism $\pi_1(\mathbb{C}^\ast) = \mathbb{Z} \to \mathbb{Z}/q\mathbb{Z}$.
   - Why it might work: makes the "monodromy" claim literal and geometric; the loop is a single generator so the homomorphism is determined by one value.
   - Risk: Mathlib's fundamental-group / covering-space API over $\mathbb{C}^\ast$ is thin; may require building continuation machinery from scratch.

3. **Approach C — Rational parametrization for the global picture**: Prove $t \mapsto (t^q, t^p)$ is a bijection (off the origin) onto $X$ and use it as an atlas, giving both connectedness and (in the compactified normalization) rationality/genus 0.
   - Why it might work: turns claims about $X$ into claims about $\mathbb{C}^\ast$ via an explicit map; $\gcd(p,q)=1 \Rightarrow$ injectivity by a Bézout argument.
   - Risk: the honest genus-0 statement needs a normalization/compactification framework Mathlib lacks; best used only for the connectedness/parametrization sub-claims.

### Key Difficulties

- Mathlib has no ready-made "Riemann surface" or complex-manifold-of-a-plane-curve object, nor a monodromy/deck-transformation theory for holomorphic coverings.
- Making "the origin is the unique branch point" precise requires a compactification or normalization of $w^q = z^p$, which is nontrivial to set up formally.
- Bridging the *pointwise* fiber description (OQ-03) with a *global* covering-map statement (local triviality, sheet continuity) is the real conceptual gap.

### What Would a Proof Need?

- Key lemma 1: fiber of $\pi$ over any $z\neq 0$ has exactly $q$ points — transport from `de-moivre-oq-03` root enumeration + distinctness.
- Key lemma 2: $\sigma:(z,w)\mapsto(z,\omega^p w)$ maps $X\to X$, fixes $z$, and $\langle\sigma\rangle$ acts simply transitively on fibers; $\mathrm{ord}(\sigma)=q$ via `IsPrimitiveRoot (ω^p) q` (needs $\gcd(p,q)=1$).
- Key lemma 3 (stretch): analytic continuation of $\exp(ip\theta/q)$ over $\theta\mapsto\theta+2\pi$ equals $\omega^p\cdot(\text{start})$, i.e. the monodromy generator matches $\sigma$.
- Technical requirements: `Mathlib.RingTheory.RootsOfUnity`, `Mathlib.FieldTheory.KummerExtension`, `Complex.cpow`/`exp`/`log`, `IsPrimitiveRoot`, and — for the analytic part — some covering-space/fundamental-group API (currently limited).

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full four-claim program (covering + monodromy + branch point + genus) requires Riemann-surface / complex-manifold infrastructure that Mathlib does not have, so an end-to-end formalization is a Moonshot.
- However, the *core* — fibers have $q$ points and the deck group is cyclic of order $q$ — is genuinely tractable because it reduces to the already-verified `de-moivre-oq-03` enumeration plus finite-group/roots-of-unity algebra that Mathlib supports well (`IsPrimitiveRoot`, `zpowers`, `Equiv.Perm`).
- Similar solved problems: OQ-03 itself (root enumeration/distinctness) is done; Mathlib's Kummer extension theory ($\mathbb{C}(z^{1/q})/\mathbb{C}(z)$ cyclic of order $q$) is present.

**Estimated Effort**:
- Exploration: 2–4 days (map OQ-03 lemmas onto the fiber/deck-group core; survey covering-space API).
- If tractable (core scope only): 1–2 weeks for the covering-cardinality + cyclic-deck-group theorems.
- If hard (analytic monodromy + branch point + genus): unknown; likely blocked on missing Riemann-surface infrastructure.

## References

### Papers
- Abraham De Moivre, *Miscellanea Analytica* / Philosophical Transactions, 1707 — original theorem (integer case).
- Leonhard Euler, *Introductio in analysin infinitorum*, 1748 — exponential form, source of multivaluedness.

### Online Resources
- O. Forster, *Lectures on Riemann Surfaces* — branched coverings, monodromy, deck transformations (Ch. 1, §4–6).
- R. Miranda, *Algebraic Curves and Riemann Surfaces* — the curve $w^q = z^p$ as a covering of $\mathbb{P}^1$, ramification, genus.
- T. Needham, *Visual Complex Analysis*, Oxford 1997 — geometric picture of Riemann surfaces of $z^{p/q}$ and monodromy.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Pow.Complex` — `Complex.cpow`, the principal-branch fractional power.
- `Mathlib.RingTheory.RootsOfUnity.Basic` / `Mathlib.RingTheory.RootsOfUnity.Complex` — cyclic group $\mu_q$, `IsPrimitiveRoot`, `Complex.isPrimitiveRoot_exp`.
- `Mathlib.FieldTheory.KummerExtension` — degree-$q$ cyclic (Kummer) extensions, the field-theoretic shadow of the covering.
- `Mathlib.GroupTheory.SpecificGroups.Cyclic` — $\mathbb{Z}/q\mathbb{Z}$ deck-group structure.

## Metadata

```yaml
tags:
  - complex-analysis
  - trigonometry
  - de-moivre
  - fractional-powers
  - roots-of-unity
  - wiedijk-100
related_proofs:
  - de-moivre-oq-03
difficulty: high
source: user-request
created: 2026-07-09T16:03:13-07:00
```
