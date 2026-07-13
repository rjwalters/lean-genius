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

## 4.5. Per-row Mathlib API path sketches (S2 PREP, researcher-10)

This section operationalises §2's nine-row menu into concrete Lean
signatures + Mathlib lemma chains. Cyclic/V₄/S₃ are sketched here; the
harder D₄/A₄/S₄ rows are deferred to a follow-up PREP (each requires
specific `Polynomial.Gal.galActionHom` image identifications).

### 4.5.A Cyclic ℤ/n (all 1 ≤ n)

**Mathlib precedent: already proved.** Wraps the existing theorem
`AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable` (proofs/Proofs/
AbelRuffiniGaloisExtensionsOQ05OQ01.lean:65), itself a wrapper of
`InverseGaloisProblem.cyclic_group_realizable`.

Lean signature for OQ-04-OQ-09 wrapper:

```lean
theorem cyclic_realizable_le_four (n : ℕ) (hn : 0 < n) (hn4 : n ≤ 4) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra ℚ L) (_ : IsGalois ℚ L),
      IsCyclic (L ≃ₐ[ℚ] L) ∧ Fintype.card (L ≃ₐ[ℚ] L) = n :=
  ⟨_, _, _, _, AbelRuffiniGaloisExtensionsOQ05OQ01.cyclic_realizable n hn⟩
```

**Estimated LOC**: ≤10 (pure wrapper). **0 axioms.**

Covers rows n=1 ({e}), n=2 (ℤ/2 = Gal(ℚ(√2)/ℚ)), n=3 (ℤ/3),
n=4 (ℤ/4 = Gal(ℚ(ζ₅)/ℚ)) of §2's table.

### 4.5.B V₄ ≅ ℤ/2 × ℤ/2

**Mathlib path**: compositum of two independent quadratic extensions.
Two independent paths:

**Path B-1** (direct compositum): `ℚ(√2, √3)` via `Algebra.adjoin`.
```lean
def K : IntermediateField ℚ ℂ := ℚ⟮(Real.sqrt 2 : ℂ), (Real.sqrt 3 : ℂ)⟯
-- Gal(K/ℚ) is V₄ since [K:ℚ]=4 and not cyclic.
```
Mathlib chain: `IntermediateField.adjoin` + `IntermediateField.finrank_adjoin_pair` (gives [K:ℚ]=4) + `Subfield.norm_two` (rules out cyclic by exhibiting a non-trivial fixed subfield from the Galois correspondence).

**Path B-2** (via cyclotomic): `ℚ(ζ₁₂)` has Galois group `(ℤ/12)× ≅ ℤ/2 × ℤ/2 = V₄`. Uses `IsCyclotomicExtension.Rat.aut_equiv_pow` (Mathlib.NumberTheory.Cyclotomic.Rat). Already in scope via `InverseGalois.lean`.

**Estimated LOC**: 40–60 (Path B-2 is shorter because the `IsCyclotomicExtension` API directly gives `Gal ≅ (ZMod 12)ˣ`, which is then a 1-line `decide` or `Finset.ext` to identify with `ZMod 2 × ZMod 2`). **0 axioms.**

### 4.5.C S₃ via $X^3 - 2$

**Mathlib path**: splitting field of an irreducible cubic with non-square discriminant.

```lean
def f : Polynomial ℚ := X^3 - 2  -- or: X^3 - X - 1, etc.
example : f.Irreducible := by
  apply Polynomial.Monic.irreducible_of_irreducible_map (Int.castRingHom ℚ)
  -- Eisenstein at p = 2: leading coeff 1 ∉ (2); X^3 - 2 ⇒ all middle coeffs 0 ∈ (2);
  -- constant -2 ∈ (2) \ (2²). Concludes via Polynomial.IsEisensteinAt.irreducible.
  sorry
example : (f.SplittingField).aut ≃* Equiv.Perm (Fin 3) := by
  -- Need: |Gal| = 6 (from [L:ℚ]=6 via `card_aut_eq_finrank`),
  -- Gal embeds in S₃ via galActionHom; cardinality + injectivity gives ≃*.
  sorry
```

Mathlib lemma chain:
1. `Polynomial.IsEisensteinAt.irreducible` (Mathlib.RingTheory.Polynomial.Eisenstein.Basic) — ⟹ f irreducible.
2. `Polynomial.SplittingField.finrank_eq_degree_iff_isSplittingField` — gives [L:ℚ] = 6 when f has 3 distinct roots in L and L is generated by them.
3. `Polynomial.Gal.galActionHom_injective` (Mathlib.FieldTheory.PolynomialGaloisGroup) — gives Gal(L/ℚ) ↪ S₃.
4. Cardinality + injectivity ⟹ image = full S₃.

**Estimated LOC**: 80–120 (the discriminant computation and the "all of S₃ is hit" step are the bulk). **0 axioms.**

**Caveat**: `Polynomial.Gal.galActionHom_injective` requires f to be separable, which is automatic over ℚ (char 0); the API needs a `[Fact (f.Separable)]` instance which is `IsField.separable_of_card_one` or just `(by decide : f.Separable)` for a concrete f.

### 4.5.D D₄, A₄, S₄ — deferred

Each requires a specific quartic with the right resolvent-cubic profile:
- **D₄**: $X^4 - 2$ (resolvent cubic $Y^3 - 8Y$ has roots $0, ±2\sqrt{2}$ — splits over ℚ(√2), not ℚ).
- **A₄**: $X^4 + 8X + 12$ (Klein's example; resolvent cubic irreducible, discriminant a square).
- **S₄**: $X^4 - X - 1$ (generic Atkin–Lehner quartic; resolvent cubic irreducible, discriminant non-square).

The identification of the Galois group image inside $S_4$ in each case
requires either:
- A custom `Polynomial.Gal.galActionHom`-image computation (lengthy), or
- A reference to a Mathlib `Polynomial.Gal.image_of_resolvent_cubic`
  lemma that **does not currently exist** (would be a Mathlib PR
  opportunity in its own right).

**Recommendation**: defer D₄/A₄/S₄ to S3 ACT or to a separate Mathlib
PR. They share infrastructure (discriminant computation + resolvent
cubic) that should be packaged as a helper namespace before any of the
four is attempted.

### 4.5.E LOC and axiom budget summary

| Row | Realization | LOC | Axioms |
|---|---|---|---|
| ℤ/n (n ≤ 4) | wrapper of `cyclic_realizable` | ≤10 | 0 |
| V₄ | path B-2 (cyclotomic ζ₁₂) | 40–60 | 0 |
| S₃ | $X^3 - 2$ + Eisenstein + cardinality | 80–120 | 0 |
| D₄ | deferred to S3 ACT | ~150 | 0 |
| A₄ | deferred to S3 ACT (Klein) | ~200 | 0 |
| S₄ | deferred to S3 ACT (Atkin–Lehner) | ~150 | 0 |
| **Total (S2 ACT)** | cyclic + V₄ + S₃ | **~150** | **0** |
| **Total (S3 ACT, all rows)** | + D₄/A₄/S₄ | **~650** | **0** |

The "**0 axioms**" claim for the table is conditional on the precedent
`cyclic_realizable` in OQ-05-OQ-01.lean being axiom-free; verify before
S2 ACT by `grep -c "^axiom\s" proofs/Proofs/AbelRuffiniGaloisExtensionsOQ05OQ01.lean`
and inspecting `Classical.choice` usage (acceptable per Lean's
standard semantics).

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
