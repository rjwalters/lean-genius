# Problem: Galois group of X⁵ − X − 1 is S₅ (unconditional, via Dedekind–Frobenius)

**Slug**: abel-ruffini-galois-extensions-oq-01-oq-01
**Created**: 2026-07-09T16:03:14-07:00
**Status**: Active
**Source**: user-request <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\mathrm{Gal}\big(X^5 - X - 1 \,/\, \mathbb{Q}\big) \;\cong\; S_5,
$$

equivalently, in Lean/Mathlib terms, an explicit multiplicative equivalence

$$
\texttt{galEquivS5} \;:\; (X^5 - X - 1).\mathrm{Gal} \;\simeq^{*}\; \mathrm{Equiv.Perm}\,(\mathrm{Fin}\,5),
$$

built **unconditionally** (no assumed isomorphism hypothesis). As a corollary, no complex root of $X^5 - X - 1$ is solvable by radicals.

### Plain Language

Selmer's trinomial $X^5 - X - 1$ is the smallest and most famous "generic-looking" quintic whose roots cannot be written using $+,-,\times,\div$ and $n$-th roots. Making that statement rigorous requires showing its symmetry group (the Galois group) is the *full* symmetric group $S_5$ on its five roots. The obstacle: unlike $X^5 - 4X + 2$, this polynomial has **four** non-real roots, so complex conjugation acts as a *double transposition*, not a transposition — so the easy "transposition + $p$-cycle generate $S_p$" route Mathlib already automates does **not** apply. We must instead certify the Galois group by reducing $X^5 - X - 1$ modulo small primes, reading off the cycle types of the Frobenius elements, and using the Dedekind–Frobenius theorem to lift those cycle types into the actual Galois group.

### Why This Matters

- **Discharges an open hypothesis in the gallery.** The sibling entry `AbelRuffiniOQ07NotSolvable` (`abel-ruffini-oq-07`) proves that $X^5 - X - 1$ is not solvable by radicals only *conditionally* on the unproved isomorphism $\mathrm{Gal} \cong S_5$. Proving that isomorphism turns a conditional gallery result into an unconditional one.
- **Selmer's trinomial is the canonical example.** $X^5 - X - 1$ appears in essentially every textbook as *the* concrete unsolvable quintic; a machine-checked, unconditional certificate for its Galois group is of independent expository value.
- **Builds reusable infrastructure.** The Dedekind–Frobenius bridge (factorization type mod $p$ ⟹ conjugacy class of a Frobenius element in $\mathrm{Gal}$) is missing from Mathlib and is a broadly useful tool for computing Galois groups of specific polynomials — far beyond this one example.

## Known Results

### What's Already Proven

- **$X^5 - X - 1$ is irreducible over $\mathbb{Q}$** — classical (it has no rational roots and no quadratic factor over $\mathbb{Q}$; equivalently it is irreducible mod 2). Provable in Mathlib via `Polynomial.Monic.irreducible_of_irreducible_map` reducing mod 2, or by `decide`-style factorization over $\mathbb{F}_2$.
- **Prime-degree, two-non-real-roots ⟹ full Galois group** — `Polynomial.Gal.galActionHom_bijective_of_prime_degree'` (`Mathlib.Analysis.Complex.Polynomial.Basic`). This is exactly the tool that *fails* to apply to $X^5 - X - 1$ because it has four non-real roots.
- **$\mathrm{Gal}(X^5 - 4X + 2) \cong S_5$, unconditional** — the source gallery entry `abel-ruffini-galois-extensions-oq-01` (`galEquivS5`), which uses the two-non-real-root shortcut and explicitly leaves $X^5 - X - 1$ open (see its `openQuestions`).
- **Abel–Ruffini correspondence** — `solvableByRad.isSolvable'` (`Mathlib.FieldTheory.AbelRuffini`): a radical-solvable root of an irreducible polynomial forces a solvable Galois group. Combined with $S_5$ not solvable (`Equiv.Perm.fin_5_not_solvable`) this yields the unsolvability corollary once the isomorphism is in hand.

### What's Still Open

- **The Dedekind–Frobenius theorem is not in Mathlib.** There is no lemma stating that if a separable, monic $f \in \mathbb{Z}[X]$ factors mod an unramified prime $p$ into irreducibles of degrees $d_1, \dots, d_k$, then the Galois group of $f$ over $\mathbb{Q}$ contains a permutation of the roots with cycle type $(d_1, \dots, d_k)$.
- **Reading a $\mathbb{Q}$-Galois group off modular factorizations** — the general "compute $\mathrm{Gal}$ from cycle types" strategy has no Mathlib automation.
- **$\mathrm{Gal}(X^5 - X - 1) \cong S_5$ itself** — the target of this problem; open in the gallery.

### Our Goal

Produce a Lean 4 / Mathlib development that constructs an explicit `galEquivS5 : (X^5 - X - 1).Gal ≃* Equiv.Perm (Fin 5)` with **0 sorries and 0 axioms** (foundational `propext`/`Classical.choice`/`Quot.sound` only), and derives the unconditional corollary `root_not_solvableByRad`. The scope includes formalizing enough of the Dedekind–Frobenius bridge to certify a transposition (or 5-cycle + double transposition) in the group from a modular factorization — this is the piece Mathlib lacks and the true difficulty of the problem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abel-ruffini-galois-extensions-oq-01 | Direct parent: the unconditional $S_5$ result for the *easy* witness $X^5 - 4X + 2$; documents this exact open question in its `openQuestions`. | `galActionHom_bijective_of_prime_degree'`, `MulEquiv.ofBijective`, Eisenstein, IVT/Rolle root counts |
| abel-ruffini-oq-07 | The conditional entry to be discharged: proves $X^5 - X - 1$ unsolvable *given* $\mathrm{Gal} \cong S_5$. | Assumed isomorphism hypothesis, `solvableByRad.isSolvable'` |
| abel-ruffini-galois-extensions | Grandparent: abstract Abel–Ruffini theory ($S_n$ solvable iff $n \le 4$; $A_5$ simple; non-solvable Galois ⟹ no radical formula). | Solvable-group classification, Galois correspondence |
| abel-ruffini | Root entry: the impossibility theorem this instantiates. | Solvability of $S_n$, radical extensions |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Full Dedekind–Frobenius bridge.**
   Formalize: for monic separable $f \in \mathbb{Z}[X]$ and a prime $p \nmid \mathrm{disc}(f)$, if $\bar f$ factors over $\mathbb{F}_p$ with degree multiset $(d_i)$, then $\mathrm{Gal}(f/\mathbb{Q})$ (as a subgroup of $S_n$ via its action on roots) contains an element of cycle type $(d_i)$. Then:
   - $X^5 - X - 1 \bmod 2$ is irreducible (degree-5 factor) ⟹ a **5-cycle** in $\mathrm{Gal}$.
   - $X^5 - X - 1 \bmod 3 = (X^2 + \dots)(X^3 + \dots)$ (a $2{+}3$ split, verifiable by `decide`) ⟹ an element of cycle type $(2,3)$; its cube is a **transposition**.
   - A 5-cycle and a transposition in a transitive subgroup of $S_5$ generate $S_5$ (Mathlib has transposition + $p$-cycle ⟹ $S_p$ style lemmas around `Equiv.Perm` / `galActionHom_bijective_of_prime_degree'`; may need `Equiv.Perm.isSwap` + `Subgroup.closure` results).
   - Why it might work: this is the textbook proof, fully rigorous, and each modular factorization is a finite `decide`.
   - Risk: Dedekind's theorem is genuinely nontrivial to formalize — it needs the reduction $\mathcal{O}_K/\mathfrak{p}$ ↔ $\mathbb{F}_p[X]/\bar f$, decomposition groups, and the Frobenius. This is the crux and could be months of work.

2. **Approach B — Discriminant / resolvent shortcut to $S_5$ vs $A_5$.**
   Show $\mathrm{Gal}$ is transitive (irreducibility) and *not* contained in $A_5$ by proving the discriminant of $X^5 - X - 1$ (which is $2869 = 19 \cdot 151$) is not a perfect square, hence $\mathrm{Gal} \not\subseteq A_5$. Combined with one non-trivial cycle constraint (e.g. a 5-cycle from mod 2) and the classification of transitive subgroups of $S_5$ ($C_5, D_5, F_{20}, A_5, S_5$), rule out all proper subgroups.
   - Why it might work: the discriminant computation is a single (large) integer check; "not a square ⟹ not in $A_5$" is `Polynomial.Gal`/`disc` theory.
   - Risk: Mathlib's discriminant-of-Galois-group support is thin; the classification of transitive subgroups of $S_5$ would itself have to be formalized. Likely still needs *some* modular cycle-type input, so it does not fully avoid Approach A's core difficulty.

3. **Approach C — Direct computation in the splitting field.** Construct the splitting field explicitly and compute the group order = 120. Almost certainly infeasible: the splitting field has degree 120 and no closed-form generators.

### Key Difficulties

- **Dedekind–Frobenius is absent from Mathlib.** This is the central gap; everything else is comparatively routine.
- **Four non-real roots** block the `galActionHom_bijective_of_prime_degree'` shortcut that made the $X^5 - 4X + 2$ sibling easy — this is *why* the harder machinery is required.
- **Lifting cycle types to actual group elements** requires care about ramification (choosing $p \nmid \mathrm{disc}$), the identification of roots mod $p$ with roots in characteristic 0, and faithfulness of the action.
- **Generation lemma** "5-cycle + transposition ⟹ $S_5$" must be available in the exact `Equiv.Perm (Fin 5)` / `galActionHom` form, with transitivity supplied by irreducibility.

### What Would a Proof Need?

- **Key lemma 1 (Dedekind):** monic separable $f \in \mathbb{Z}[X]$, prime $p \nmid \mathrm{disc}(f)$; then the factorization type of $\bar f$ over $\mathbb{F}_p$ equals the cycle type of a Frobenius element of $\mathrm{Gal}(f/\mathbb{Q})$ acting on the roots.
- **Key lemma 2 (modular factorizations, by `decide`):** $X^5 - X - 1$ is irreducible mod 2 (⟹ 5-cycle) and factors as (deg 2)(deg 3) mod 3 (⟹ a $(2,3)$-element, whose cube is a transposition).
- **Key lemma 3 (generation):** a transitive subgroup of $S_5$ containing a 5-cycle and a transposition is all of $S_5$.
- **Packaging:** assemble the above into `galEquivS5 : (X^5 - X - 1).Gal ≃* Equiv.Perm (Fin 5)`, mirroring the sibling's `MulEquiv.ofBijective`/`permCongr` packaging, then transport `Equiv.Perm.fin_5_not_solvable` and apply `solvableByRad.isSolvable'` for `root_not_solvableByRad`.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The elementary parts (irreducibility, modular factorizations by `decide`, the generation lemma, final packaging) are all within reach of current Mathlib — the sibling entry `abel-ruffini-galois-extensions-oq-01` demonstrates the packaging pattern end-to-end.
- The **Dedekind–Frobenius theorem is not in Mathlib** and formalizing it is a substantial project (decomposition/inertia groups, Frobenius, reduction of number rings mod a prime). This single dependency dominates the difficulty and is why the sibling entry deliberately switched witnesses to avoid it.
- Partial credit is possible: formalize the elementary lemmas plus a *stated* (axiomatized) Dedekind bridge to produce a clearly-labelled `axiomatized` entry, then chip away at the axiom — but a fully `verified` result requires the whole bridge.

**Estimated Effort**:
- Exploration: 2–4 days (survey Mathlib's ring-of-integers / discriminant / Frobenius support; confirm the modular factorizations)
- If tractable (Dedekind bridge already available or easy): 1–2 weeks for packaging
- If hard (must formalize Dedekind–Frobenius from scratch): unknown — likely months; a strong candidate for a stated-axiom intermediate entry

## References

### Papers
- Selmer, E. S., *"On the irreducibility of certain trinomials"*, Math. Scand. 4 (1956) — origin of $X^5 - X - 1$ as a standard irreducible trinomial.
- Dedekind, R., *"Über den Zusammenhang zwischen der Theorie der Ideale und der Theorie der höheren Kongruenzen"* (1878) — the factorization/Frobenius theorem underlying the whole approach.

### Online Resources
- https://en.wikipedia.org/wiki/Dedekind%27s_theorem_on_the_factorization_of_prime_ideals — statement and proof sketch of the factorization ↔ splitting correspondence.
- https://en.wikipedia.org/wiki/Abel%E2%80%93Ruffini_theorem — background on the unsolvability of the quintic.
- Keith Conrad, *"Galois groups as permutation groups"* (expository notes) — worked examples computing $\mathrm{Gal}$ from modular factorizations, including trinomials like $X^5 - X - 1$.

### Mathlib
- `Mathlib.FieldTheory.PolynomialGaloisGroup` — `Polynomial.Gal`, `galActionHom`, `card_rootSet_eq_natDegree`.
- `Mathlib.FieldTheory.AbelRuffini` — `solvableByRad.isSolvable'` (the radical ⟹ solvable-Galois correspondence).
- `Mathlib.GroupTheory.Solvable` — `Equiv.Perm.fin_5_not_solvable`, `solvable_of_surjective`.
- `Mathlib.Analysis.Complex.Polynomial.Basic` — `galActionHom_bijective_of_prime_degree'` (the shortcut that does **not** apply here).
- `Mathlib.RingTheory.Discriminant` / `Mathlib.NumberTheory.RamificationInertia` / `Mathlib.RingTheory.DedekindDomain.*` — the raw material a Dedekind–Frobenius formalization would build on (Frobenius / decomposition groups are only partially developed).

## Metadata

```yaml
tags:
  - galois-theory
  - abel-ruffini
  - solvability
  - symmetric-group
  - quintic
  - field-theory
  - advanced
related_proofs:
  - abel-ruffini-galois-extensions-oq-01
  - abel-ruffini-oq-07
difficulty: high
source: user-request
created: 2026-07-09T16:03:14-07:00
```
