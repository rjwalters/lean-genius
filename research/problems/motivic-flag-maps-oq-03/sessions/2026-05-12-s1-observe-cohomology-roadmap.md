# Session 1 — OBSERVE: cohomology/topology consequences roadmap

**Slug**: `motivic-flag-maps-oq-03`
**Researcher**: researcher-10
**Date**: 2026-05-12
**Phase**: OBSERVE → ORIENT (doc-only deliverable; no Lean changes)
**Parent gallery**: `motivic-flag-maps` (Bryan–Elek–Manners–Salafatinos–Vakil 2025, arXiv:2601.07222)

---

## 1. The open question, restated

The parent result is the motivic identity in the Grothendieck ring of varieties:

$$
[\Omega^2_\beta(\mathrm{Fl}_{n+1})] \;=\; [\mathrm{GL}_n] \cdot [\mathbb{A}^a] \;\;\in\;\; K_0(\mathrm{Var}_k)
$$

with $a = \sum_i \tfrac{d_i(d_i+1)}{2} + (n-1)\sum_i d_i$ for a positive homology class
$\beta = (d_1,\dots,d_n)$ and $\Omega^2_\beta$ the space of based maps $(\mathbb{P}^1, 0, \infty) \to (\mathrm{Fl}_{n+1}, *, *)$.

OQ-03 asks: **What does this identity tell us about the topology or cohomology of $\Omega^2_\beta(\mathrm{Fl}_{n+1})$?**

The honest short answer: a $K_0(\mathrm{Var})$ identity is *exactly* the statement that the
two varieties are indistinguishable by any **motivic measure** — that is, by any
additive, multiplicative invariant that is constant on isomorphism classes. The
class equality propagates verbatim through each ring homomorphism
$\mu : K_0(\mathrm{Var}_k) \to R$ ("realization functor") in the following table.

| Realization $\mu$              | Target ring $R$                | Sends $\mathbb{L} = [\mathbb{A}^1] \mapsto$ | Field hypothesis |
| ------------------------------ | ------------------------------ | ------------------------------------------ | ---------------- |
| Euler characteristic           | $\mathbb{Z}$                   | $1$                                        | $k = \mathbb{C}$ (or any with comp. supp.) |
| Counting points over $\mathbb{F}_q$ | $\mathbb{Z}$                   | $q$                                        | $k = \mathbb{F}_q$ |
| Hodge–Deligne $E$-polynomial   | $\mathbb{Z}[u,v]$              | $uv$                                       | $k = \mathbb{C}$ |
| Poincaré polynomial (cells)    | $\mathbb{Z}[t]$                | $t^2$                                      | when motive is pure Tate |
| Class in $K_0(\mathrm{Coh}\,\overline{k})$ via $\ell$-adic $\chi_c$ | $\mathbb{Z}[\![\Lambda]\!]$ representations | $\ell$-adic cyclotomic | $k$ finite or NF |

So the consequence of the motivic identity is uniform: **for each realization
$\mu$, the value $\mu(\Omega^2_\beta(\mathrm{Fl}_{n+1}))$ equals $\mu(\mathrm{GL}_n) \cdot \mu(\mathbb{A}^a)$**.
The interesting question is then which $\mu$ are sharp enough to give a
non-trivial topological statement, and which ones can actually be expressed in
the current `MotivicFlagMaps` Lean formalization.

---

## 2. Race-safety re-check (2026-05-12 ~21:11 UTC)

```
$ gh pr list --state open --search "motivic-flag-maps-oq-03"
[#18286] seeker: initialize 6 research workspaces — pool 10 → 16 available
```

Only the seeker batch-init PR exists; no in-flight researcher PR on this slug.
The slug appears in the candidate pool as tier B (significance 6, tractability 5,
status `available`). Sibling status:

- **OQ-01** (Mathlib formalization to remove axioms): `status=active`, `phase=OBSERVE`, 9 insights logged, completed grassmannian duality via `Polynomial Z` universality.
- **OQ-02** (partial-flag extension): `status=active`, `phase=OBSERVE`, 6 insights logged, completed `MotivicFlagMapsPartialFlags.lean` (635 lines, 3 axioms remaining, 0 sorries).

OQ-03 is **orthogonal** to both: OQ-01 attacks the moduli-space axiom directly,
OQ-02 generalizes the statement to partial flags. OQ-03 instead **derives
downstream invariants** from the (still-axiomatic) main identity. This is a
fundamentally different kind of work and does not duplicate anything in the
sibling workspaces.

---

## 3. Gallery audit: what does the current formalization expose?

`grep -n "topology\|cohomology\|Cohomology\|Topology\|Singular\|EulerChar\|Hodge\|Betti\|chern\|Chow"` returns
**zero hits** across `MotivicFlagMaps.lean` (438 lines), `MotivicFlagMapsPartialFlags.lean` (635 lines),
and `MotivicFlagMapsProvable.lean` (182 lines). The entire current Lean
treatment lives at the level of $K_0(\mathrm{Var})$ as an abstract commutative
ring carrying a distinguished element $\mathbb{L}$:

```
structure GrothendieckRingVar (k : Type*) [Field k] where
  carrier : Type*
  [ringInst : CommRing carrier]
  L : carrier        -- Lefschetz motive [A¹]
```

There is no concrete model — no scissor-relation construction, no constructor
for $[X]$ from a variety $X$, no realization homomorphism into $\mathbb{Z}$ or
$\mathbb{Z}[t]$. The only concrete consequences proved in the file are
**polynomial identities** in this abstract ring: `GLn_class`, `Fl_n_class`,
`projective_class_formula`, `fiber_class_k1/k2`, plus the two `axiom`
declarations encoding the main theorem:

```
axiom motivicClassBasedMaps (n : ℕ) (β : HomologyClass n) : K.carrier
axiom motivic_class_flag_maps (n : ℕ) (hn : n ≥ 1)
    (β : HomologyClass n) (hβ : β.positive) :
    motivicClassBasedMaps K n β = motivicClassGLnAffine K n (computeA β)
```

So the **bridge from $K_0(\mathrm{Var})$ to topology/cohomology** is entirely
**unbuilt** in this repository. Any progress on OQ-03 must first construct at
least one realization homomorphism.

---

## 4. Mathlib audit: what is actually available at v4.26.0?

Mathlib v4.26.0 (pinned in `proofs/lakefile.toml`) has the following pieces
that bear on building a realization functor. None of these together gives the
full picture, but each can be combined into a usable scaffold.

### 4.1 Algebraic infrastructure (concrete, ready to use)

- `Polynomial R` (`Mathlib.Algebra.Polynomial.Basic`) — for $\mathbb{Z}[t]$, $\mathbb{Z}[u,v]$ via `Polynomial (Polynomial ℤ)`
- `RingHom` (`Mathlib.Algebra.Ring.Hom.Defs`)
- `MvPolynomial` (`Mathlib.Algebra.MvPolynomial.Basic`) — cleaner for $\mathbb{Z}[u,v]$
- `Polynomial.eval₂` (substitution / evaluation at a ring element)
- `Polynomial.geom_sum` / `mul_geom_sum` — already invoked in `projective_class_formula`
- `Finset.prod_range_succ`, `Finset.sum_range_succ` — used in `GLnClass` formula

### 4.2 What is missing

- **No** `K_0(Var)` in Mathlib — confirmed by absence of any file named
  `Grothendieck*Var*` or `Motivic*` under `Mathlib/AlgebraicGeometry`.
- **No** `EulerCharacteristic` of a (quasi-projective) variety.
- **No** `PointCount` / $\zeta$-function machinery in any usable form for
  $K_0(\mathrm{Var}_{\mathbb{F}_q})$.
- **No** Hodge-theory or Hodge–Deligne polynomial.

This is in line with general Mathlib coverage: motivic / Hodge-theoretic
infrastructure has not been formalized.

### 4.3 What this means for OQ-03

The bridge to "topology/cohomology" cannot be built from a Mathlib-provided
realization — it must be **axiomatized as a ring homomorphism** out of the
abstract `GrothendieckRingVar.carrier`, just as the main result is axiomatized.
This is **legitimate** for the OQ-03 task: we are not asked to *construct* the
realization; we are asked to derive its consequences from the motivic identity.

The right shape of the formalization is therefore:

```
structure MotivicMeasure (K : GrothendieckRingVar k) (R : Type*) [CommRing R] where
  μ      : K.carrier →+* R
  μ_L    : μ K.L = (lefschetzImage : R)   -- e.g. 1, q, t², or uv
```

Then for any `μ : MotivicMeasure K R`, the theorem
`motivic_class_flag_maps K n hn β hβ` propagates through `μ` to give a
ring identity in `R`. The `axiomCount` does **not** rise: we introduce a
*structure*, not an axiom, and instances of the structure are user-supplied.
(See AXIOM INTEGRITY POLICY in CLAUDE.md — `MotivicMeasure` carries fields
the user must populate, but it is not itself an assumption about the parent
result.)

---

## 5. Three candidate S2 targets

All three are doc-or-thin-Lean targets that share the same scaffold:
introduce `MotivicMeasure`, populate one instance, derive an explicit numeric
or polynomial identity for `Ω²_β(Fl_{n+1})` as a corollary of the axiomatic
parent theorem. Each target is meant to be one short PR.

### S2-A. Euler-characteristic vanishing on the moduli space (TIGHTEST)

**Statement.** For any positive $\beta$ and any $n \ge 1$, the Euler
characteristic of $\Omega^2_\beta(\mathrm{Fl}_{n+1})$ vanishes:
$\chi_c(\Omega^2_\beta(\mathrm{Fl}_{n+1})) = 0$.

**Why this is sharp.** The Euler realization sends $\mathbb{L} \mapsto 1$.
Then $\chi(\mathrm{GL}_n) = \prod_{i=1}^{n}(1^i - 1) \cdot 1^{n(n-1)/2} = 0$
for every $n \ge 1$. Hence the right-hand side of the motivic identity is
$0 \cdot 1^a = 0$, and therefore so is the left.

**Lean shape.**

```
def eulerMeasure (K : GrothendieckRingVar k) : MotivicMeasure K ℤ :=
  ⟨RingHom.id ℤ ∘ ..., by simp⟩  -- the unique ring hom factoring through L ↦ 1

theorem euler_char_motivic_flag_maps_zero
    (n : ℕ) (hn : n ≥ 1) (β : HomologyClass n) (hβ : β.positive) :
    eulerMeasure K (motivicClassBasedMaps K n β) = 0 := by
  rw [motivic_class_flag_maps K n hn β hβ]
  -- reduces to: ∏ (1 - 1) · 1^a = 0
```

**Estimated cost.** ~60–90 lines. Build-verifiable. Adds no axioms.

**Significance.** Modest but real. The vanishing is well known but the
formalization gives the first cohomological consequence pulled through the
machinery. Sharp enough to falsify any wrong sign convention in `GLnClass`.

### S2-B. Point counts over $\mathbb{F}_q$ (BROADEST)

**Statement.** Fix a prime power $q$. Then
$\#\Omega^2_\beta(\mathrm{Fl}_{n+1})(\mathbb{F}_q) = q^a \cdot \prod_{i=1}^n (q^i - 1) \cdot q^{n(n-1)/2}$.

**Why.** The point-count realization $\mu_q : K_0(\mathrm{Var}_{\mathbb{F}_q}) \to \mathbb{Z}$
is the ring hom with $\mathbb{L} \mapsto q$. Apply to the motivic identity.

**Lean shape.**

```
def pointCountMeasure (q : ℕ) (K : GrothendieckRingVar k) : MotivicMeasure K ℤ :=
  ⟨..., μ_L := show μ K.L = q from rfl⟩

theorem pointCount_motivic_flag_maps (q n : ℕ) (hn : n ≥ 1)
    (β : HomologyClass n) (hβ : β.positive) :
    pointCountMeasure q K (motivicClassBasedMaps K n β)
      = q^(computeA β).toNat * (∏ i ∈ Finset.range n, (q^(i+1) - 1)) * q^(n*(n-1)/2) := by
  ...
```

**Estimated cost.** ~120–180 lines (more arithmetic care than S2-A; integer
exponentiation, `Nat.factorial`-style products).

**Significance.** Connects to the actual cardinality of $\mathrm{GL}_n(\mathbb{F}_q)$,
a textbook formula. The cleanest "topological" statement — by Weil
conjectures, point counts are alternating sums of $\ell$-adic Betti numbers,
so this is one $q$-specialization away from the full cohomology story.

### S2-C. $\mathbb{L}^a$-divisibility of the based-map class (NARROWEST)

**Statement.** In $K_0(\mathrm{Var}_k)$, the class
$[\Omega^2_\beta(\mathrm{Fl}_{n+1})]$ is divisible by $\mathbb{L}^{n(n-1)/2}$
(in the multiplicative sense), reflecting the affine-bundle structure visible
in the cell decomposition of $\mathrm{GL}_n$.

**Why.** $[\mathrm{GL}_n] = \prod (L^i - 1) \cdot L^{n(n-1)/2}$, so the
right-hand side of the motivic identity has $L^{n(n-1)/2}$ as a literal
factor. This descends through the identity to the left.

**Lean shape.** A single divisibility statement with `Dvd.dvd`:

```
theorem L_pow_dvd_motivicClassBasedMaps
    (n : ℕ) (hn : n ≥ 1) (β : HomologyClass n) (hβ : β.positive) :
    K.L ^ (n*(n-1)/2) ∣ motivicClassBasedMaps K n β := by
  rw [motivic_class_flag_maps K n hn β hβ]
  unfold motivicClassGLnAffine GLnClass
  exact ⟨..., by ring⟩
```

**Estimated cost.** ~40–60 lines. Smallest of the three.

**Significance.** Tightest deliverable. Asserts an *intrinsic* algebraic
consequence in $K_0(\mathrm{Var})$ — no realization needed — and so is a
precursor lemma to *all* of S2-A and S2-B (every realization sends a divisor
to a divisor).

---

## 6. Recommended S2 ordering

Ship **S2-C first** (smallest, axiom-free, no new structure), then **S2-A**
(introduces `MotivicMeasure` as a single-instance proof of concept), then
**S2-B** (the broad result that benefits most from `MotivicMeasure` being
already in place). Each S2 PR is independent — failure of one does not
block the others. Total expected envelope: ~220–330 Lean lines across three
PRs, all build-verifiable, all axiom-free.

---

## 7. What this session deliberately does **not** do

- Build $K_0(\mathrm{Var})$ from a scissor-relation quotient. That is the
  large-scale Mathlib formalization OQ-01 is tracking; OQ-03 deliberately
  works against the same `GrothendieckRingVar` abstraction.
- Touch the Bryan–Elek–Manners–Salafatinos–Vakil axioms. Those are the
  parent's open conjecture; OQ-03 only consumes them.
- Claim that "equal motivic classes" implies "isomorphic" or "diffeomorphic".
  It does not — the equality is in a Grothendieck group, which is far weaker.
  This is an honest disclaimer to put in the gallery copy if/when OQ-03
  ships to the gallery.

---

## 8. Concrete next-session checklist

When (or if) S2-C is picked up:

1. Add to `MotivicFlagMaps.lean` a single new theorem
   `L_pow_dvd_motivicClassBasedMaps` immediately after
   `motivic_class_flag_maps_n2` (line ~340).
2. Re-run `./proofs/scripts/docker-build.sh Proofs.MotivicFlagMaps` to
   verify no regressions in the 26 existing theorems.
3. Update `motivic-flag-maps-oq-03.json` (NB: create — does not yet exist
   in `src/data/research/problems/`) with `phase: ACT`, status `progress`.
4. PR title: `research(motivic-flag-maps-oq-03): S2-C ACT — L-power divisibility of motivic class`.

If S2-A is picked first:

1. Decide whether `MotivicMeasure` lives in `MotivicFlagMaps.lean` (visible
   to all three OQs) or in a new `MotivicMeasures.lean` (cleaner separation).
   Recommendation: new file, since OQ-01 / OQ-02 do not need it.
2. Build verifies `eulerMeasure` is a valid `MotivicMeasure` instance and
   then proves `euler_char_motivic_flag_maps_zero`.

---

## 9. Phase transition

```
OBSERVE  →  (this PR)  →  ORIENT  (with three S2 candidates fully scoped)
```

Phase advances to ORIENT on merge. ACT requires picking and shipping one
of S2-A/B/C in a follow-up session.
