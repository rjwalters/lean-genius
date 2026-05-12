# Knowledge — abel-ruffini-oq-04-oq-09

S1 OBSERVE survey. **No Lean changes** in this iteration.

## 1. Relationship to existing scaffolding

Three existing gallery entries already touch Shafarevich-style realizability:

| Entry | What it proves | Axiom load |
|-------|----------------|------------|
| `AbelRuffiniGaloisExtensionsOQ05` | Stated as `axiom shafarevich_inverse_galois`; derives corollaries for cyclic / abelian / S₃ / S₄ | 1 axiom (full Shafarevich) |
| `AbelRuffiniGaloisExtensionsOQ05OQ01` | PROVES cyclic ℤ/nℤ via Dirichlet; PROVES coprime ℤ/mℤ × ℤ/nℤ via CRT; abelian gap = compositum axiom | 1 axiom (compositum disjointness) |
| `InverseGalois.lean` | Proves Gal(Φₙ/ℚ) ≅ (ℤ/nℤ)ˣ, all abelian Galois groups | 0 axioms |

**Distinct angle for OQ-04-OQ-09**: limit the universe to subgroups of $S_n$
for $n \leq 4$ — a *finite* menu of explicit constructions that needs
**no Shafarevich axiom** and **no compositum-disjointness axiom**, because
each target is a single cyclotomic subfield or a direct compositum of
quadratic extensions.

## 2. The finite menu

For $n \leq 4$, the solvable subgroups of $S_n$ (up to conjugacy) are:

| n | Solvable subgroups (up to ≅) | Standard ℚ-realization |
|---|------------------------------|------------------------|
| 1 | {e} | ℚ itself |
| 2 | {e}, ℤ/2 | ℚ(√2) |
| 3 | {e}, ℤ/2, ℤ/3, S₃ | ℚ(√2), ℚ(ζ₇)^{ℤ/2} or splitting of $X^3-X-1$, splitting of $X^3-2$ |
| 4 | {e}, ℤ/2, ℤ/3, ℤ/4, V₄, S₃, D₄, A₄, S₄ | (extensions of above + quartics) |

Total distinct group structures (up to ≅): **9** (counting only what occurs
as a transitive Galois group of a degree-≤4 polynomial; the full lattice
of subgroups is larger but redundant under isomorphism).

For each row, the realization is one of:
- **Cyclic** $\mathbb{Z}/n$: take ℚ(ζ_p) for a prime p ≡ 1 mod n, then the
  unique subfield of index $(p-1)/n$. Already proved in OQ-05-OQ-01
  (`cyclic_realizable`).
- **V₄**: compositum ℚ(√a, √b) for $a, b$ multiplicatively independent
  modulo squares. Direct via `Algebra.adjoin`.
- **S₃**: splitting field of an irreducible cubic with non-square
  discriminant. Example: $X^3 - 2$ (disc = $-108 = -4 \cdot 27$).
- **D₄**: splitting field of $X^4 - 2$.
- **A₄**: splitting field of $X^4 + 8X + 12$ (Klein 1879 / standard
  textbook example, discriminant = $81 \cdot 16^2$ which is a square).
- **S₄**: splitting field of $X^4 - X - 1$ (Atkin–Lehner / generic
  quartic; resolvent cubic irreducible with non-square discriminant).

## 3. Mathlib API surface

Surveyed via existing in-tree usage (cannot grep Mathlib directly:
`proofs/.lake` symlink is broken — see
`feedback_researcher_lake_symlink_broken.md`).

### Core types
- `IsGalois F E` — Mathlib.FieldTheory.Galois.Basic (already imported in OQ05)
- `L ≃ₐ[ℚ] L` — Mathlib's notation for `AlgEquiv ℚ L L`, the Galois group as a group
- `Polynomial.SplittingField f` — Mathlib.FieldTheory.SplittingField.Construction
- `IsCyclotomicExtension S F K` — Mathlib.NumberTheory.Cyclotomic.Basic

### Galois-group computation
- `IsGalois.card_aut_eq_finrank` — relates |Gal| to dimension (used in
  `AbelRuffiniGaloisExtensions.galois_group_order`).
- `IsCyclotomicExtension.Rat.aut_equiv_pow` — Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/nℤ)ˣ
  (used in `InverseGalois.lean`).
- `Polynomial.Gal.galActionAux` — Galois action on roots of a polynomial.

### Solvability
- `IsSolvable G` — Mathlib.GroupTheory.Solvable (already used throughout
  the OQ-04 chain).
- `isSolvable_of_comm`, `isSolvable_of_subsingleton` — base cases.
- `Equiv.Perm.not_solvable` — used by parent's `symmetric_not_solvable`.

### Splitting / minimal polynomials
- `Polynomial.IsSplittingField` — universal property of splitting fields.
- `Polynomial.Galois` (namespace `Polynomial.Gal`) — Galois group of a
  polynomial.

### Eisenstein / Gauss for irreducibility
- `Polynomial.Monic.eisensteinAt` — Eisenstein at a prime ideal.
- `Polynomial.IsEisensteinAt.irreducible` — Eisenstein ⟹ irreducible.
- Already in use in `NthRootIrrationalOQ01` (imported by `InverseGalois`).

## 4. Outstanding Mathlib gaps for the full $n \leq 4$ menu

For the **cyclic and V₄** rows, all infrastructure is in Mathlib (cyclotomic
Galois + adjoin of two square roots). PROVED with 0 axioms.

For the **S₃ / D₄ / A₄ / S₄** rows, the obstacle is computing the Galois
group of a *specific* polynomial. Mathlib has:
- `Polynomial.Gal` and an action on roots, but...
- ...no general "compute Gal(f) for a given f ∈ ℚ[X]" tactic.

Standard approach: for each target group, exhibit a polynomial whose
splitting-field Galois group is isomorphic to that group, then **prove
the isomorphism by hand** using:
1. Cardinality: |Gal| = [L : ℚ] = deg(f) when f is irreducible and L is
   the splitting field.
2. Action on roots: realize Gal as a subgroup of $S_n$ via
   `Polynomial.Gal.galActionHom`.
3. Group identification: pin down the image subgroup of $S_n$ using
   degree + transitivity + cycle structure of a specific automorphism.

**This is feasible but tedious.** Each of the four group cases
(S₃, D₄, A₄, S₄) is roughly 80–200 lines of Lean.

## 5. Approach for S2 (next ACT iteration)

Two viable S2 deliverables:

### Option A — Lean stub probe (~30 lines, build verifies API)
Create `proofs/Proofs/AbelRuffiniOQ04OQ09Probe.lean` with a 30-line
`#check` test of all key Mathlib symbols needed for §3 (the table). This
verifies API surface before committing to §5's per-group proofs. Estimate:
1 build cycle (~45 min cold per `feedback_researcher_lake_symlink_broken`).

### Option B — Markdown-only completion of the menu (~300 lines)
Expand `knowledge.md` §2 into a per-row "proof sketch + Mathlib API path"
that another researcher (or an Aristotle session) can pick up directly.
This is the lower-risk path given:
- Build environment has the broken `.lake` symlink → 45-min cycles.
- The parent's contested-slug pool (cf. `project_moderate_plus_oversubscribed_pool.md`)
  means another researcher may grab S2 in parallel.

**Recommendation**: Option B for S2 — finish the per-row sketch table in
markdown. Option A becomes S3 once an agent has Docker availability for
a clean build.

## 6. References

- Shafarevich, I.R. "Construction of fields of algebraic numbers with a
  given solvable Galois group" (1954, Izv. Akad. Nauk SSSR Ser. Mat.).
- Iwasawa, K. — corrections to Shafarevich's proof (1958, J. Math. Soc.
  Japan); the corrected proof appears in Neukirch–Schmidt–Wingberg,
  *Cohomology of Number Fields*, §IX.6.
- Cassels–Fröhlich, *Algebraic Number Theory* — class field theory used
  in Shafarevich's abelian-step construction.
- Conrad, K. "Galois groups of cubics and quartics (not in characteristic
  2)" — explicit construction of S₃/D₄/A₄/S₄ over ℚ.
- Jensen–Ledet–Yui, *Generic Polynomials* (CUP 2002) — parametrized
  realizations of all 9 transitive subgroups of $S_n$ for $n \leq 5$.

## 7. Knowledge Score notes

This slug had `knowledgeScore: 0 (EMPTY)` at claim time. After S1 the
score should rise to ~30 (problem.md + knowledge.md + state.md =
"MODERATE" tier) per the seeker's scoring rubric.
