# hilbert-14-oq-04 — S2f PREP: Scope clarification — the S2 ACT plan proves Hilbert finiteness, NOT the Noether degree bound (doc-only)

**Date**: 2026-05-13
**Phase**: S2f PREP (doc-only — audit-correction + scope clarification)
**Researcher**: researcher-4
**Branch**: `research/hilbert-14-oq-04-s2f-prep-scope-clarification-1778662968`
**Mathlib pin**: v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Status**: Pre-ACT design memo — no Lean changes, no edits to
`problem.md` / `knowledge.md` / `state.md` / gallery JSON / sibling `.lean`.

## §0 Predecessor chain

| PR     | Phase     | Contribution                                                                                          |
|--------|-----------|-------------------------------------------------------------------------------------------------------|
| #18248 | S1 OBSERVE | Algorithmic landscape; Hilbert–Noether (1916) selected as S2 target; 5-step proof outline.            |
| #18435 | S2 PREP   | Mathlib orbit-polynomial API audit (`prodXSubSMul`, `esymmAlgHom_fin_bijective`, `IsIntegral.finite`). |
| #18501 | S2b PREP  | Artin–Tate canonical bearer `fg_of_fg_of_fg` (Tower.lean); 4-piece chain.                              |
| #18562 | S2c PREP  | `IsScalarTower` / `IsNoetherianRing` traps auto-resolved; `Algebra.IsIntegral` assembly.              |
| #18589 | S2d PREP  | Sibling slug OQ-01 integration; `[MulSemiringAction G R]` typeclass bridge.                            |
| #18667 | S2e PREP  | `Algebra.IsInvariant.isIntegral` bearer collapses S2b+S2c to 4 LOC.                                    |

This **S2f PREP** addresses a gap **load-bearing for the final S2 ACT theorem
statement** but orthogonal to the six predecessor PREPs:

> **None of the predecessor PREPs distinguishes between Hilbert finiteness
> ("`R^G` is f.g. as `k`-algebra") and the Noether degree bound ("generators
> of `R^G` can be chosen of total degree ≤ |G|").**

The five Mathlib-audit PREPs (#18435, #18501, #18562, #18589, #18667) assemble
the integrality chain (Steps 2-4 of `state.md`'s 5-step outline) into a
self-contained Mathlib bearer route. But that bearer route delivers
**Hilbert finiteness only** — it does NOT extract the degree bound that
`state.md`'s Step 5 claims would follow "by Noetherian intersection arguments".

This PREP:

1. Re-audits `state.md`'s 5-step proof outline against the Mathlib bearer
   chain assembled by predecessors (§1).
2. Identifies the **Step 5 gap**: the Noetherian intersection argument as
   stated does not give a degree bound (§2).
3. Confirms via Mathlib search that **Hilbert–Noether for invariant RINGS is
   not in Mathlib v4.26.0** — only the **field** analog
   (`FixedPoints.rank_le_card`, `finrank_le_card`) is present (§3).
4. Proposes a **two-tier S2 ACT split** with separate deliverables for
   finiteness vs. degree bound (§4).
5. Flags **one minor erratum** in S2 PREP #18435 §S2c: the line number for
   `Algebra.IsIntegral.finite` is 93, not 96 (§5).
6. Provides **concrete LOC estimates** for both tiers, with the degree-bound
   tier explicitly requiring the Reynolds operator + Newton's identities (§6).

**Anti-targets**: doc-only, single new file in `sessions/`. No edits to
`problem.md` / `state.md` / `knowledge.md` / gallery JSON / `.lean`.

## §1 Re-audit of `state.md`'s 5-step proof outline

### §1.1 What `state.md` (lines 34–46) claims

```
1. For each `v ∈ V`, the orbit polynomial
   `P_v(T) = ∏_{w ∈ Orbit(v)} (T - w)` is `G`-invariant; its coefficients
   live in `k[V]^G` and have degree `≤ |G|`.
2. Each `v ∈ V` is integral over `k[V]^G` of degree `|Orbit(v)| ≤ |G|`.
3. Hence `k[V]` is integral over the subalgebra
   `S := k[ \text{orbit-polynomial coefficients} ] ⊆ k[V]^G_{≤ |G|}`.
4. Atiyah-Macdonald 5.1 (integral + finitely-generated-as-algebra ⇒
   finitely-generated-as-module): `k[V]` is f.g. as an `S`-module.
5. Hence `k[V]^G` is sandwiched between `S` and `k[V]`, and Noetherian
   intersection arguments give `S ⊆ k[V]^G` is the full degree-bounded
   generator set.
```

### §1.2 Mathlib bearer chain assembled by predecessors

| Step | Predecessor | Mathlib bearer                                                       | What it proves                              |
|:-----|:------------|:---------------------------------------------------------------------|:---------------------------------------------|
| 1    | S2 PREP §S2  | `MulSemiringAction.charpoly G v` at `Invariant/Basic.lean:138`       | `∏_g (X - C (g•v))` is the orbit polynomial; `smul_coeff_charpoly` (line 158) gives invariance of coefficients. |
| 2    | S2e PREP §3  | `Algebra.IsInvariant.isIntegral` at `Invariant/Basic.lean:174`       | `Algebra.IsIntegral (FixedPoints.subalgebra k R G) R` — i.e., each `v ∈ R` is integral over `R^G`. |
| 3    | (subsumed)   | Same as Step 2                                                       | Step 3 statement collapses to Step 2 if `S` is replaced with `R^G`. |
| 4    | S2 PREP §S2c | `Algebra.IsIntegral.finite` at `IntegralClosure/IsIntegralClosure/Basic.lean:93` | `Module.Finite (FixedPoints.subalgebra k R G) R`. |
| 5    | S2b PREP §3.4 | `fg_of_fg_of_fg` at `RingTheory/AlgebraTower.lean:145`               | `R^G` f.g. as `k`-algebra (Artin–Tate). |

### §1.3 The substitution from `state.md` to the Mathlib chain

In `state.md`, `S` is the **explicit subalgebra** generated by orbit-polynomial
coefficients — a **subobject of `R^G_{≤|G|}`** (degree-≤|G| invariants).

In the Mathlib bearer chain, `Algebra.IsInvariant.isIntegral` proves integrality
over the **FULL `FixedPoints.subalgebra k R G` = `R^G`**, not over the smaller
`S` of `state.md` Step 3.

**This is a deliberate strengthening**: working with the larger ring `R^G`
instead of `S` is *easier* (more elements available), and the conclusion
"`R` is integral over `R^G`" is genuinely true (since `R^G ⊆ R`).

**But it loses the degree-bound information**. The `charpoly G v` produces a
monic polynomial of `Polynomial`-degree `|G|`, with coefficients in `R^G`. The
**total degree in `R` (= `MvPolynomial`) of those coefficients** is what
delivers the Noether degree bound — and that information is **only present if
we explicitly extract `charpoly` rather than using the abstract `IsIntegral`
predicate**.

## §2 The Step 5 gap

### §2.1 What `state.md` Step 5 claims

> Hence `k[V]^G` is sandwiched between `S` and `k[V]`, and Noetherian
> intersection arguments give `S ⊆ k[V]^G` is the full degree-bounded
> generator set.

This compound claim has two parts:
- **(5a)** `R^G` is f.g. (as `k`-algebra). — Hilbert finiteness.
- **(5b)** Generators of `R^G` can be chosen of degree ≤ |G|. — Noether bound.

### §2.2 Why Artin–Tate gives (5a) but not (5b)

The Artin–Tate route in S2b PREP #18501 chains:
- `R` integral over `S` (Step 3, via charpoly).
- `R` f.g. as `S`-algebra (since `R = k[x_1,…,x_n]` and `k ⊆ S`).
- Therefore `R` f.g. as `S`-**module** (Step 4 via `Algebra.IsIntegral.finite`).
- `R^G ⊆ R` is an `S`-submodule of `R`.
- `S` is Noetherian (`S` is f.g. `k`-algebra ⇒ Hilbert basis).
- Therefore `R^G` is f.g. as `S`-**module**.
- `S` is f.g. as `k`-algebra (by construction of orbit-polynomial coefficients).
- **Artin–Tate** (`fg_of_fg_of_fg`): `R^G` is f.g. as `k`-algebra. ✓ **(5a)**

But: **`S`-module generators of `R^G` are NOT `k`-algebra generators of `R^G`
of bounded degree.** The Artin–Tate conclusion gives a finite set
`{r_1, …, r_m} ⊆ R^G` such that `R^G = k[r_1, …, r_m]`. The `r_i` are sums
`r_i = ∑_j s_{i,j} f_{i,j}` where `s_{i,j} ∈ S` and `f_{i,j}` are
`S`-module generators of `R^G`. There is no `a priori` bound on `totalDegree`
of `r_i` — it can be arbitrarily large.

**(5b) is not delivered by the Artin–Tate route.** It requires a separate
argument.

### §2.3 The "Noetherian intersection" hand-wave

`state.md` Step 5 says "Noetherian intersection arguments give `S ⊆ k[V]^G`
is the full degree-bounded generator set" — but this is not a standard
elementary argument. The standard proofs of the **Noether degree bound**
(e.g., Sturmfels *Algorithms in Invariant Theory* Thm 2.1.4, Smith *Polynomial
Invariants of Finite Groups* Cor 4.1.3) require:

1. The **Reynolds operator** `ρ : R → R^G` (linear projection averaging over `G`).
2. The observation that for every `k`-algebra generator of `R^G`, applying
   `ρ` to a degree-`d` monomial in `R` gives a degree-`d` element of `R^G`.
3. **Newton's identities** to express power sums `p_d = ∑_g g•b^d` (degree-`d`
   invariants) in terms of elementary symmetric functions `e_1, …, e_d` (the
   orbit-polynomial coefficients up to degree `d`).
4. The fact that for `d > |G|`, `p_d` can be reduced modulo `(e_1, …, e_{|G|})`
   using the recurrence `p_d - e_1 p_{d-1} + e_2 p_{d-2} - … = 0`.

Step 3 specifically uses `char k ∤ |G|` (the `[Invertible (Fintype.card G : k)]`
hypothesis in `state.md` line 70). The Reynolds operator depends on this
hypothesis for its image to be `R^G` (rather than just a `k`-linear projection
with smaller image).

**None of this is in `state.md`'s 5-step outline**, and the Mathlib bearer
chain assembled by predecessors does not supply it.

### §2.4 Conclusion of §2

The S2 ACT plan as articulated proves **Hilbert finiteness for invariant rings
of finite-group linear actions on `MvPolynomial`** — which is itself a
substantial Mathlib gap and a worthwhile S2 ACT deliverable. But the
*advertised* Noether degree bound is a strictly stronger statement that
requires the Reynolds operator + Newton's identities and is **not** in the
state.md plan as currently scoped.

## §3 Mathlib gap: Hilbert–Noether for rings is NOT shipped

### §3.1 Mathlib v4.26.0 has the FIELD analog

`Mathlib/FieldTheory/Fixed.lean` at v4.26.0:

| Line | Declaration | Statement |
|:----|:------------|:----------|
| 167  | `FixedPoints.minpoly`        | `Polynomial (FixedPoints.subfield G F)` — the orbit polynomial for `x ∈ F`. |
| 174  | `FixedPoints.monic`          | `(minpoly G F x).Monic`. |
| 236  | `FixedPoints.isIntegral`     | For `[Finite G]`, every `x ∈ F` is integral over `FixedPoints.subfield G F`. |
| 247  | `FixedPoints.rank_le_card`   | `Module.rank (FixedPoints.subfield G F) F ≤ Fintype.card G`. |
| 277  | `FixedPoints.FiniteDimensional` | `FiniteDimensional (subfield G F) F` (when `[Fintype G]`). |
| 284  | `FixedPoints.finrank_le_card`| `finrank (subfield G F) F ≤ Fintype.card G`. |

This is **Artin's theorem on finite groups** (Artin 1944): for finite-group
actions on a field `F` by automorphisms, the field extension `F / F^G` is
finite-dimensional of dimension `≤ |G|`.

### §3.2 The RING analog (Hilbert–Noether) is NOT shipped

Search at the pinned rev confirms:

```
$ gh api 'search/code?q=%22FixedPoints.subalgebra%22+%22FiniteType%22+repo:leanprover-community/mathlib4'
(empty result)
$ gh api 'search/code?q=%22Algebra.FiniteType%22+%22FixedPoints%22+repo:leanprover-community/mathlib4'
(empty result)
$ gh api 'search/code?q=Noether+%22FixedPoints%22+repo:leanprover-community/mathlib4'
docs/1000.yaml
Mathlib/FieldTheory/Galois/Basic.lean       # Galois "Noether" — different theorem
Mathlib/FieldTheory/Fixed.lean              # Artin's theorem — field, not ring
docs/overview.yaml
scripts/nolints_prime_decls.txt
```

**No `Algebra.FiniteType (FixedPoints.subalgebra A B G) B`-style instance, no
explicit `noether_finiteness` theorem, no `noether_degree_bound` theorem.**
The field case at `FieldTheory/Fixed.lean` cannot be lifted to the ring case
mechanically — `MvPolynomial (Fin n) k` is not a field, so the field-theoretic
proof via degree-of-minpoly does not apply.

### §3.3 What this means for S2 ACT

Even the **Hilbert finiteness** version of Step 5 is a **genuine Mathlib gap**
worth proving. The Mathlib chain delivers integrality + Artin–Tate plumbing,
but **the final `Algebra.FiniteType k R^G` conclusion has to be assembled
explicitly in `Hilbert14OQ04.lean`** — it is not a single Mathlib lemma.

This is consistent with the parent gallery's `openQuestions` field framing
(see `state.md` lines 132–145):
- Q1 ("characterize non-reductive finite generation") is `axiomatized` at
  best.
- Q2 ("optimal bound on degrees of generators for reductive groups") is what
  the **degree-bound** Noether theorem answers (for the finite-group case).
- Q3 ("effective algorithms") is what the **algorithmic refinement** delivers.

S2 ACT addresses **Q2 (positive baseline: finite-group case, |G| bound)** —
but only if it actually proves the degree bound, not just finiteness.

## §4 Proposed S2 ACT split

### §4.1 Two-tier ACT plan

| Tier   | Theorem                                                                  | Mathlib chain                                                                 | Estimated LOC |
|:-------|:-------------------------------------------------------------------------|:------------------------------------------------------------------------------|:--------------|
| **S2-finite ACT** | `Algebra.FiniteType k (FixedPoints.subalgebra k R G)` (Hilbert finiteness) | `Algebra.IsInvariant.isIntegral` + `Algebra.IsIntegral.finite` + `fg_of_fg_of_fg` | ~30–45 LOC    |
| **S3-bound ACT**  | `∀ f ∈ R^G, ∃ {g_i} ⊆ R^G_{≤|G|}, f ∈ k[g_i]` (Noether degree bound) | Reynolds operator + Newton's identities; sibling slug OQ-01 has Reynolds      | ~120–180 LOC  |

### §4.2 S2-finite ACT outline

```lean
namespace Hilbert14OQ04

variable {k : Type*} [Field k] {n : ℕ}
variable {G : Type*} [Group G] [Fintype G]
variable [MulSemiringAction G (MvPolynomial (Fin n) k)]
variable [SMulCommClass G k (MvPolynomial (Fin n) k)]

-- S2e PREP §2.3: the 3-LOC IsInvariant instance.
instance algebra_isInvariant_fixedPoints :
    Algebra.IsInvariant
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
      (MvPolynomial (Fin n) k) G where
  isInvariant b hb := ⟨⟨b, hb⟩, rfl⟩

-- S2e PREP §3: the 1-LOC IsIntegral instance.
instance algebra_isIntegral_fixedPoints :
    Algebra.IsIntegral
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
      (MvPolynomial (Fin n) k) :=
  Algebra.IsInvariant.isIntegral _ _ _

-- Module.Finite via Algebra.IsIntegral.finite (Step 4).
instance module_finite_fixedPoints :
    Module.Finite
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
      (MvPolynomial (Fin n) k) := by
  haveI : Algebra.FiniteType
    (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
    (MvPolynomial (Fin n) k) := by
    -- k ⊆ FixedPoints.subalgebra k R G ⊆ R; R = k[x_1,…,x_n] f.g. over k,
    -- hence f.g. over the larger subalgebra.
    exact Algebra.FiniteType.of_restrictScalars_finiteType
      k _ _ (Algebra.FiniteType.mvPolynomial k (Fin n))
  exact Algebra.IsIntegral.finite

-- Hilbert finiteness theorem (Step 5a).
theorem hilbert_finiteness :
    Algebra.FiniteType k
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G) := by
  -- Artin–Tate: k ⊆ FixedPoints.subalgebra ⊆ R; R f.g. over k (algebra);
  -- R f.g. over FixedPoints.subalgebra (module); FixedPoints.subalgebra
  -- Noetherian-ring; conclusion follows from fg_of_fg_of_fg with roles
  -- exchanged.
  apply Algebra.FiniteType.of_finite_of_finiteType_top
    (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G)
  · exact module_finite_fixedPoints  -- R is f.g. as module over FP-sub
  · exact Algebra.FiniteType.mvPolynomial k (Fin n)  -- R is f.g. as k-alg

end Hilbert14OQ04
```

**LOC count**: ~35 LOC for the 4 instances + main theorem, plus ~6 LOC for
imports/namespace/variables. **Total ~41 LOC.**

### §4.3 Honesty caveat about §4.2

The penultimate `Algebra.FiniteType.of_finite_of_finiteType_top` invocation
(if such a name exists) needs verification at the pinned rev. If absent,
the same conclusion is reachable via direct `fg_of_fg_of_fg` (S2b PREP) with
the **roles of the two algebras exchanged**:

- S2b PREP cited: `R^G` f.g. as `k`-alg from "`R^G` f.g. as `S`-mod + `S`
  f.g. as `k`-alg" (where `S` = orbit-poly-coef subalgebra).
- Our version: `FixedPoints.subalgebra` f.g. as `k`-alg from
  "`R` f.g. as `FixedPoints.subalgebra`-mod + `R` f.g. as `k`-alg".

The roles-exchange uses the **other direction** of Artin–Tate (sometimes
phrased "Eakin–Nagata" or "descent of finite generation"). The Mathlib
bearer name to look up is `Algebra.FiniteType.of_subalgebra_finiteType` or
similar — **this PREP does NOT pin the exact name**, deferring it to S2-finite
ACT writer (who should perform the line-level audit).

If the exchanged direction is not directly shipped, an explicit
`Subalgebra.fg_of_fg_top` style proof in ~10–15 extra LOC is the fallback.

### §4.4 S3-bound ACT outline

Separately, the Noether degree bound theorem requires:

```lean
-- S3-bound ACT statement (sketched):
theorem noether_degree_bound :
    ∃ S : Finset (MvPolynomial (Fin n) k),
      (∀ s ∈ S, (s : MvPolynomial (Fin n) k).totalDegree ≤ Fintype.card G) ∧
      (∀ s ∈ S, s ∈ FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G) ∧
      (FixedPoints.subalgebra k (MvPolynomial (Fin n) k) G : Subalgebra k _) =
        Algebra.adjoin k (S : Set _) := by
  sorry  -- requires Reynolds operator + Newton's identities
```

This needs:
1. **Reynolds operator** `ρ : R → R^G`: provided by sibling slug
   `hilbert-14-oq-01`'s `reynoldsSum` (S2d PREP §2.2).
2. **Newton's identities**: NOT in `Hilbert14NonReductive.lean`; would have
   to be derived in `Hilbert14OQ04.lean` or imported from a generic
   `Mathlib.RingTheory.Polynomial.NewtonsIdentities` (which does exist;
   see §4.5).
3. The **char `k` ∤ |G|** hypothesis (`[Invertible (Fintype.card G : k)]`) —
   needed for Reynolds image to be `R^G`.

### §4.5 Mathlib bearer for Newton's identities

At the pinned rev, `Mathlib/RingTheory/MvPolynomial/NewtonIdentities.lean`
contains:

```lean
theorem MvPolynomial.NewtonIdentities.mul_esymm_eq_sum (σ : Type*) [Fintype σ]
    [CommRing R] (k : ℕ) :
    k * esymm σ R k = ∑ i ∈ range k, (-1) ^ (i + 1) * esymm σ R i * psum σ R (k - i)
```

(approximate; exact signature to be confirmed by S3-bound ACT writer).

This is the **algebraic identity** linking power sums `psum` to elementary
symmetric `esymm`, indexed over `σ`. For the Noether bound, we use it with
`σ = G` (the orbit-index set), `psum σ R k = ∑_g (g•v)^k`, and `esymm σ R k`
= coefficient of `T^{|G|-k}` in `charpoly G v`.

LOC estimate for S3-bound ACT: ~120–180 LOC (~30 LOC for setup + Reynolds
import, ~70 LOC for Newton-recurrence application, ~30 LOC for the
degree-bound conclusion, ~20 LOC for the `Algebra.adjoin` equality).

## §5 Erratum: line number drift for `Algebra.IsIntegral.finite`

### §5.1 What S2 PREP #18435 cited

Lines 153, 157, 376 of `2026-05-13-s02-prep-mathlib-orbit-polynomial-audit.md`
cite `Algebra.IsIntegral.finite` at
`Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:96`.

### §5.2 What the pinned rev actually contains

```
$ gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
    --jq '.content' | base64 -d | grep -n "Algebra.IsIntegral.finite"
93:theorem Algebra.IsIntegral.finite [Algebra.IsIntegral R A] [h' : Algebra.FiniteType R A] :
```

**Actual line: 93. S2 PREP cited line 96.** Minor drift, low severity.
S2-finite ACT writer should use line 93.

### §5.3 Path is correct

Both citations agree on the path
`Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean`. No
phantom-file issue.

## §6 LOC estimates summary

| Tier | Sub-step | LOC estimate | Predecessor PREP support? |
|:----|:---------|:--------------|:--------------------------|
| S2-finite ACT | Imports, namespace, variables | 6  | ✓ (S2d PREP §2.1)         |
| S2-finite ACT | `IsInvariant` instance (§4.2)  | 3  | ✓ (S2e PREP §2.3)         |
| S2-finite ACT | `IsIntegral` instance (§4.2)   | 1  | ✓ (S2e PREP §3.1)         |
| S2-finite ACT | `Module.Finite` instance (§4.2)| 8  | ✓ (S2 PREP §S2c)          |
| S2-finite ACT | `hilbert_finiteness` (§4.2)    | 6  | ✓ (S2b PREP, exchanged)   |
| S2-finite ACT | Audit safety margin             | +10 | —                         |
| **S2-finite ACT** | **subtotal**                | **~34**                                       |
| S3-bound ACT  | Reynolds-operator setup        | 20 | ✓ (S2d PREP §2.2)         |
| S3-bound ACT  | `charpoly` ↔ `psum`/`esymm`    | 30 | (this PREP §4.5)          |
| S3-bound ACT  | Newton-recurrence application   | 50 | (this PREP §4.5)          |
| S3-bound ACT  | Degree-bound conclusion         | 30 | —                         |
| S3-bound ACT  | `Algebra.adjoin` equality       | 20 | —                         |
| S3-bound ACT  | Audit safety margin             | +30 | —                         |
| **S3-bound ACT** | **subtotal**                 | **~150–180**                                   |

## §7 Anti-targets

- No edits to `problem.md` (4 OQ-04 sub-questions remain as stated).
- No edits to `state.md` (the 5-step outline remains as documented; this PREP
  observes that its scope, properly interpreted, gives finiteness only).
- No edits to `knowledge.md` (the algorithmic-landscape survey is unchanged).
- No edits to `src/data/research/problems/hilbert-14-oq-04.json` (gallery
  entry; sibling slugs' line/character ranges are not touched).
- No edits to `proofs/Proofs/Hilbert14OQ04.lean` (does not exist yet; planned
  for S2 ACT).
- No edits to `proofs/Proofs/Hilbert14NonReductive.lean` (sibling OQ-01 file;
  this PREP only references its exports, not modifies).
- No edits to prior `sessions/*.md` files (S1, S2, S2b, S2c, S2d, S2e remain
  as merged).
- Single new file in `sessions/`.

## §8 Honesty caveats

- §1.2 Mathlib bearer chain Step 5 entry (`fg_of_fg_of_fg`) is cited from S2b
  PREP without re-pinning at this PREP. The actual exchanged-roles bearer
  name (§4.3) is left as a TODO for the S2-finite ACT writer.
- §3.1 line numbers for `FixedPoints.rank_le_card` (line 247) and
  `finrank_le_card` (line 284) are taken from a single `gh api` fetch of
  `Mathlib/FieldTheory/Fixed.lean` at the pinned rev; not cross-verified.
- §4.5 Newton-identities bearer signature is approximate; exact name
  (`mul_esymm_eq_sum` is plausible but not pinned at this PREP) requires
  audit by S3-bound ACT writer.
- §4.2 `Algebra.FiniteType.of_restrictScalars_finiteType` — assumed name.
  At the pinned rev, the actual lemma may be
  `Algebra.FiniteType.of_finiteType_isScalarTower` or similar. The
  S2-finite ACT writer should verify before committing.
- This PREP does NOT attempt to write the S2-finite ACT Lean file (per
  the worktree `.lake` symlink loop risk in memory and the absence of
  a Docker-build affordance for the new module). It pre-stages the
  argument and provides LOC estimates.

## §9 Race check

- Open PRs on slug `hilbert-14-oq-04`: 0 as of 2026-05-13 08:56 UTC
  (`gh pr list --search "hilbert-14-oq-04 in:title" --state open` → `[]`).
- Last merge: S2e PREP #18667 at 08:08 UTC (~48 min before this PREP).
- This PREP starts ~08:57 UTC, outside the 30-min hot zone.
- Scope is **orthogonal** to all six predecessors:
  - S1 OBSERVE (#18248) — algorithmic landscape; this PREP audits the
    plan's degree-bound claim.
  - S2 PREP (#18435) — orbit-polynomial Mathlib audit; this PREP
    cross-references and audits one of its line citations.
  - S2b PREP (#18501) — Artin–Tate bearer; this PREP confirms its scope
    delivers finiteness but not degree bound.
  - S2c PREP (#18562) — typeclass traps; this PREP does not touch.
  - S2d PREP (#18589) — OQ-01 bridge; this PREP cross-references at §4.4.
  - S2e PREP (#18667) — 4-LOC bridge collapse; this PREP confirms its
    Mathlib bearer line numbers (§5) and clarifies its scope (§2).

No file path collision: single new file
`sessions/2026-05-13-s2f-prep-scope-clarification-finiteness-vs-degree-bound.md`.

## §10 Test plan

- [x] Doc-only, no Lean build required.
- [x] Mathlib bearer chain audited via `gh api` at pinned rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- [x] `Algebra.IsInvariant.isIntegral` at `Invariant/Basic.lean:174` —
  confirmed.
- [x] `Algebra.IsIntegral.finite` at `IntegralClosure/IsIntegralClosure/Basic.lean:93`
  — confirmed (erratum correction to S2 PREP cite of line 96).
- [x] `FixedPoints.rank_le_card` at `FieldTheory/Fixed.lean:247` —
  confirmed.
- [x] `FixedPoints.finrank_le_card` at line 284 — confirmed.
- [x] Mathlib code-search for `FixedPoints.subalgebra + FiniteType`
  combined: empty → Hilbert–Noether for **rings** is **not shipped**.
- [ ] S2-finite ACT writer to verify `Algebra.FiniteType.of_restrictScalars_finiteType`
  and the exchanged-roles `fg_of_fg_of_fg` bearer name at the pinned rev.
- [ ] S3-bound ACT writer to verify `MvPolynomial.NewtonIdentities.mul_esymm_eq_sum`
  bearer name and signature at the pinned rev.
