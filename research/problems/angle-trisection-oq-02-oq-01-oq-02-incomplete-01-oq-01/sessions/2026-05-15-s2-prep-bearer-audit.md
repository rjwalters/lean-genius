# Session 2026-05-15 — S2 PREP (researcher-4, doc-only)

**Slug**: angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01
**Phase**: OBSERVE → ORIENT (S2 PREP)
**Iteration**: 1 → 2
**Researcher**: researcher-4
**PR**: (this PR)
**Outcome**: S2 PREP audit — Mathlib v4.26.0 bearer-lemma pin, parent
private-surface map, **two material drift findings** that revise the S1
OBSERVE plan, R2-pure route recipe.

---

## 1. Bearer-lemma audit (v4.26.0)

Each row pins the v4.26.0 path:line and signature. Verified by
fetching `https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/<path>`.

| # | Lemma (S1 §3 name) | v4.26.0 path:line | Actual signature in v4.26.0 | Drift? |
|---|---|---|---|---|
| B1 | `IsAlgClosed.lift` | `Mathlib/FieldTheory/IsAlgClosed/Basic.lean:351` | `noncomputable irreducible_def lift : S →ₐ[R] M` (S algebraic over R, M `IsAlgClosed`) — **AlgHom, not AlgEquiv** | none |
| B2 | `IntermediateField.normalClosure_le_iff` | (not load-bearing for ⇒ direction; deferred) | — | — |
| B3 | `Polynomial.SplittingField` | `Mathlib/FieldTheory/SplittingField/Construction.lean` | abbreviated structure, used as type `p.SplittingField` | none |
| B4 | `SplittingField.adjoin_rootSet` | `Mathlib/FieldTheory/SplittingField/Construction.lean` (called via `IsSplittingField.adjoin_rootSet` and `Polynomial.SplittingField.adjoin_rootSet` in `Mathlib/FieldTheory/PolynomialGaloisGroup.lean:70`) | confirmed by usage site | none |
| B5 | `Polynomial.Gal` | `Mathlib/FieldTheory/PolynomialGaloisGroup.lean:55` | `def Gal := p.SplittingField ≃ₐ[F] p.SplittingField  deriving Group, Fintype, EquivLike, AlgEquivClass` | none |
| **B6** | `Polynomial.Gal.card_eq_finrank_splittingField` (S1 §3 guess) | **`Mathlib/FieldTheory/PolynomialGaloisGroup.lean:349` (actual name `Gal.card_of_separable`)** | `theorem card_of_separable (hp : p.Separable) : Nat.card p.Gal = finrank F p.SplittingField` — **uses `Nat.card`, not `Fintype.card`** | **YES — name drift + cardinality flavor drift** |
| B7 | `IntermediateField.adjoin.finrank` | `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:459` | `theorem adjoin.finrank {x : L} (hx : IsIntegral K x) : Module.finrank K K⟮x⟯ = (minpoly K x).natDegree` | none |
| B8 | `Module.finrank_mul_finrank` | `Mathlib/FieldTheory/Tower.lean` (referenced; used in parent file L401, `NormalizedTrace.lean`, etc.) | tower-law multiplicativity | none |

**Auxiliary v4.26.0 pins surfaced during the audit** (not in S1 §3 but
load-bearing for the proof recipe):

| # | Lemma | v4.26.0 path:line | Signature |
|---|---|---|---|
| A1 | `minpoly.irreducible` | `Mathlib/FieldTheory/Minpoly/Basic.lean:277` | `theorem irreducible (hx : IsIntegral A x) : Irreducible (minpoly A x)` |
| A2 | `minpoly.aeval` | `Mathlib/FieldTheory/Minpoly/Basic.lean:88` | `theorem aeval : aeval x (minpoly A x) = 0` |
| A3 | `minpoly.natDegree_pos` | `Mathlib/FieldTheory/Minpoly/Basic.lean:199` | `theorem natDegree_pos [Nontrivial B] (hx : IsIntegral A x) : 0 < natDegree (minpoly A x)` |
| A4 | `Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits` | `Mathlib/FieldTheory/IsAlgClosed/Basic.lean:528` | `def: (K →ₐ[F] L) ≃ (K →ₐ[F] A)` under L↪A and minpoly-splits-in-L hypothesis |

### Material drift findings (B6)

1. **Name drift**: S1 §3 listed `Polynomial.Gal.card_eq_finrank_splittingField`.
   The actual v4.26.0 canonical name is `Polynomial.Gal.card_of_separable`.
   No `card_eq_finrank_splittingField` exists in v4.26.0 Mathlib (verified
   by raw-fetch of `Mathlib/FieldTheory/PolynomialGaloisGroup.lean`).
2. **Cardinality flavor drift**: `card_of_separable` returns
   `Nat.card p.Gal = finrank F p.SplittingField`, **not** `Fintype.card`.
   The S1 OBSERVE survey question 4 (refine `wantzel_galois_iff`
   statement: `Fintype.card` or `Cardinal.mk`?) is now answered with a
   THIRD option: **`Nat.card`** (which Mathlib uses for the canonical
   bearer in v4.26.0). `Gal p` does derive `Fintype`, so `Fintype.card`
   would also typecheck, but stating it via `Nat.card` aligns with the
   bearer lemma and avoids an extra coercion step at S3 ACT.

**Adopted convention (this slug, S3+)**:
```lean
theorem isConstructible_galois_two_group (α : ℂ) (h : IsConstructible α) :
    ∃ n : ℕ, Nat.card (minpoly ℚ α).Gal = 2 ^ n
```
(NOT `Fintype.card`, NOT `|...|`, NOT `Cardinal.mk`.)

---

## 2. Parent private-surface audit

Audit of `private` declarations in
`proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean` against
their usefulness for the ⇒ direction of `wantzel_galois_iff`:

| Symbol | Line | Public role | Needed for ⇒? | Re-derive vs surface-lift? |
|---|---|---|---|---|
| `isConstructible_algebraic : IsConstructible α → IsAlgebraic ℚ α` | 134 | private | **yes** (need `IsIntegral` for `minpoly.irreducible`, `adjoin.finrank`) | **Re-derive** (~10 LOC inductive proof — identical to L134-142) |
| `finrank_sup_quadratic_dvd_two` | 158 | private (helper) | no | not needed |
| `isConstructible_sup_degree : ∀ K, finrank K (K ⊔ ℚ⟮α⟯) ∣ 2^n` | 241 | private (stronger IH) | no — the ⇒ proof uses `isConstructible_algebraic_degree` only | not needed |
| `isConstructible_algebraic_degree : IsAlgebraic ℚ α ∧ ∃ n, finrank ℚ ℚ⟮α⟯ ∣ 2^n` | 351 | private | **yes** (yields `2^n` bound for each conjugate's adjoin) | **Re-derive from public surface** (see §3 below) |

**Public surface available** (from grepping `^theorem ` and `^lemma `):

```
L89   isConstructible_rat
L93   isConstructible_zero
L97   isConstructible_one
L101  isConstructible_sqrt2
L121  isConstructible_map  (Galois invariance under ℂ →ₐ[ℚ] ℂ)
L514  cube_root_2_minpoly_irred
L526  cos20_minpoly_degree
L530  regular_7gon_poly_degree
L535  cube_root_2_degree
L542  DegreePowerOfTwo  (def)
L558  cos20_degree_not_pow_two
L564  three_not_pow_two
L569  regular_7gon_impossible_degree
L589  not_constructible_of_bad_degree  ← key public lever
L627  angle_trisection_impossible_degree
L631  doubling_cube_impossible_degree
L635  regular_7gon_construction_impossible
```

---

## 3. Material drift finding: parent docstring vs file contents

### Drift D-2 (CRITICAL)

The parent file's module docstring at lines 38–48 reads:

> ```
> ## New Lemmas (Session 36)
> - `isConstructible_map`: …
>
> ## New Lemmas (Session 37)
> - `isConstructible_minpoly_pow2`: IsConstructible α → ∃ m, natDeg(minpoly ℚ α) = 2^m.
>   Clean consequence of isConstructible_algebraic_degree + adjoin.finrank.
> - `isConstructible_irred_degree_pow2`: For p irreducible with constructible root α,
>   natDeg p = 2^m for some m. Positive form of not_constructible_of_bad_degree.
> ```

**Both `isConstructible_minpoly_pow2` and `isConstructible_irred_degree_pow2`
are absent from the file as of HEAD `74a47a86244` (parent build SHA).**

Verified by:
```
grep -n "^theorem \|^lemma " proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean
# returns 17 declarations; none of them is `isConstructible_minpoly_pow2`
# or `isConstructible_irred_degree_pow2`.
```

The docstring is aspirational/stale: Session 37 was planned but never
landed. `isConstructible_minpoly_pow2` exists only as a private witness
inside `not_constructible_of_bad_degree` (L595: `obtain ⟨halg, n, hn_dvd⟩
:= isConstructible_algebraic_degree α hcα`), and its positive
"natDeg = 2^m" form is not exposed.

**Impact on S1 OBSERVE knowledge.md**: §1 inheritance table lists both
lemmas as "proved" (status column), and §8 S2 PREP queue item 3 reads
"S1 recommendation is **R2** (new file …)
provided the public surface
(`isConstructible_minpoly_pow2`, `isConstructible_map`) is sufficient".
**That premise is false.** The available public surface is
`isConstructible_map` only.

This S2 PREP **corrects the S1 plan**: R2 must include either a
re-derivation of the minpoly-pow2 bound from `not_constructible_of_bad_degree`
(see §4 R2-pure recipe), or be replaced by R3 (companion + parent
surface-lift PR).

---

## 4. Route decision: R2-pure (companion file, no parent edits)

### R2-pure recipe — re-derive `isConstructible_minpoly_pow2` from public surface

The contrapositive of `not_constructible_of_bad_degree`, applied to the
minimal polynomial of α (which is irreducible by `minpoly.irreducible`),
yields the positive form. ~25 LOC, no parent edits required.

```lean
-- In the companion file AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean
import Proofs.AngleTrisectionOQ02OQ01OQ02Incomplete01
import Mathlib.FieldTheory.PolynomialGaloisGroup
-- (and other Mathlib imports as needed)

namespace AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01

open AngleTrisectionOQ02OQ01OQ02Incomplete01 Polynomial

/-- Constructible numbers are algebraic over ℚ.
    Re-derived publicly (the parent has a `private` copy at L134). -/
theorem isConstructible_algebraic (α : ℂ) (h : IsConstructible α) :
    IsAlgebraic ℚ α := by
  -- Identical induction to parent L134-142 (~10 LOC).
  sorry  -- S3 ACT body

/-- Positive form: minimal polynomial of a constructible number has
    2-power natDegree. Re-derived from `not_constructible_of_bad_degree`
    (contrapositive on minpoly). -/
theorem isConstructible_minpoly_pow2 (α : ℂ) (h : IsConstructible α) :
    ∃ m : ℕ, (minpoly ℚ α).natDegree = 2 ^ m := by
  have hint : IsIntegral ℚ α :=
    isAlgebraic_iff_isIntegral.mp (isConstructible_algebraic α h)
  have hirr : Irreducible (minpoly ℚ α) := minpoly.irreducible hint
  have haeval : Polynomial.aeval α (minpoly ℚ α) = 0 := minpoly.aeval ℚ α
  -- Contrapositive of not_constructible_of_bad_degree:
  -- IsConstructible α → ¬ ¬ DegreePowerOfTwo (minpoly ℚ α)
  by_contra hne; push_neg at hne
  have hbd : ¬ DegreePowerOfTwo (minpoly ℚ α) := fun ⟨m, hm⟩ => hne m hm
  exact not_constructible_of_bad_degree hirr hbd α haeval h
```

**Resulting public surface** in the companion: `isConstructible_algebraic`,
`isConstructible_minpoly_pow2`. These suffice to feed S3 ACT's main
target `isConstructible_galois_two_group`.

### Why not R1 / R3?

- **R1** (extend parent file): The parent is 639 LOC at 0 sorries / 0
  axioms. Adding ~200 LOC of Galois-group reasoning to it bloats the
  surface and increases the regression-fault footprint of every
  unrelated edit. R2-pure preserves separation.
- **R3** (companion + surface-lift PR): Cleaner long-term, but adds a
  sequencing dependency (surface-lift PR must merge before companion
  can build). With the queue at 175 open PRs and a recent drain wave,
  same-cycle landing of two PRs on the same parent file is unwise.
  Revisit if S3 ACT discovers we need `isConstructible_sup_degree`
  publicly.

---

## 5. Material drift finding: ⇒ direction Step 4 (σ existence) is harder than the S1 sketch

### Drift D-3 (CRITICAL — revises S1 §4 proof sketch)

S1 OBSERVE knowledge.md §4 Step 4 reads:

> *For each i, there is a ℚ-algebra map ℚ⟮α⟯ → ℂ sending α to βᵢ
> (universal property of minpoly). Extend via `IsAlgClosed.lift` to
> σᵢ : ℂ →ₐ[ℚ] ℂ with σᵢ(α) = βᵢ. Apply `isConstructible_map σᵢ h`
> to get `IsConstructible βᵢ`.*

**`IsAlgClosed.lift` does not directly extend ℚ⟮α⟯ →ₐ[ℚ] ℂ to ℂ →ₐ[ℚ] ℂ.**

The signature (B1 audit row) is:
```
noncomputable irreducible_def lift : S →ₐ[R] M
  [Algebra R S]  [Algebra R M]  [IsAlgClosed M]
  [Algebra.IsAlgebraic R S]
  [NoZeroSMulDivisors R S]  [NoZeroSMulDivisors R M]
```

To use `lift` with `S = ℂ`, `R = ℚ`, `M = ℂ`, we would need
`Algebra.IsAlgebraic ℚ ℂ` — **which is false** (ℂ is transcendental
over ℚ; it contains π, e, …). The `lift` lemma fundamentally cannot
produce ℂ →ₐ[ℚ] ℂ.

**Concrete options for S3 ACT**:

| Option | Approach | Cost |
|---|---|---|
| **OPT-1** | Replace `isConstructible_map` with a relativized variant `isConstructible_map_intermediate : (K : IntermediateField ℚ ℂ) → [Algebra.IsAlgebraic ℚ K] → (σ : K →ₐ[ℚ] ℂ) → ∀ α : ℂ, α ∈ K → IsConstructible α → IsConstructible (σ ⟨α, _⟩)`. Rewrite the inductive proof to track the intermediate field of witnesses. | ~50–80 LOC; structurally clean; lives in companion |
| **OPT-2** | Use `IsAlgClosed.lift` with `S =` algebraic closure of ℚ inside ℂ (a subfield of ℂ that *is* algebraic over ℚ), then compose with the inclusion → ℂ. Get a self-embedding (algebraic closure of ℚ in ℂ) →ₐ[ℚ] ℂ; combine with the ℚ-algebra equivalence ℚ⟮α⟯ ≃ₐ[ℚ] ℚ⟮β⟯ (both being ℚ[X]/(minpoly ℚ α)). | ~40–60 LOC; requires more Mathlib spelunking for the algebraic-closure-in-ℂ object |
| **OPT-3** | Extend ℚ⟮α⟯ →ₐ[ℚ] ℂ to ℂ →ₐ[ℚ] ℂ via choice of a transcendence basis of ℂ/ℚ — Mathlib has `Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits` (A4 audit row) and related, but the direct "Zorn extension" of an algebra hom of a transcendental superfield is **not** trivially available. | uncertain; high risk |

**Recommended for S3 ACT**: **OPT-1**. The relativized
`isConstructible_map_intermediate` is direct, lives in the companion
file (no parent edits), and matches how the actual proof recurses
(each constructibility witness is finite-extension-bounded). The
parent's existing `isConstructible_map` is a degenerate case
(K = ⊤, σ extends trivially).

OPT-2 is the fallback if OPT-1 hits an unexpected Mathlib gap.

---

## 6. Refined S3 ACT skeleton (target statement + lemma sequence)

```lean
namespace AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01

-- (1) Bridge from public parent surface
theorem isConstructible_algebraic (α : ℂ) (h : IsConstructible α) :
    IsAlgebraic ℚ α := by sorry  -- ~10 LOC inductive (mirror L134-142)

theorem isConstructible_minpoly_pow2 (α : ℂ) (h : IsConstructible α) :
    ∃ m : ℕ, (minpoly ℚ α).natDegree = 2 ^ m := by
  sorry  -- ~10 LOC, contrapositive of not_constructible_of_bad_degree

-- (2) Relativized Galois invariance (OPT-1)
lemma isConstructible_map_intermediate
    (K : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ K]
    (σ : K →ₐ[ℚ] ℂ) (α : ℂ) (hα : α ∈ K) (h : IsConstructible α) :
    IsConstructible (σ ⟨α, hα⟩) := by
  sorry  -- ~30-50 LOC, induction tracking witnesses' intermediate field

-- (3) Main target: ⇒ direction
theorem isConstructible_galois_two_group (α : ℂ) (h : IsConstructible α) :
    ∃ n : ℕ, Nat.card (minpoly ℚ α).Gal = 2 ^ n := by
  -- Step 1: minpoly is separable (char 0)
  -- Step 2: |Gal(p)| = finrank ℚ p.SplittingField  (B6: card_of_separable)
  -- Step 3: SplittingField p = ℚ⟮β₁,...,βₖ⟯ where βᵢ are roots (B4)
  -- Step 4: Each βᵢ is constructible (relativized via (2))
  -- Step 5: finrank ℚ ℚ⟮βᵢ⟯ ∣ 2^nᵢ                 (via (1) + adjoin.finrank B7)
  -- Step 6: finrank ℚ ℚ⟮β₁,...,βₖ⟯ ∣ 2^N            (tower law B8 + induction)
  -- Step 7: 2^N divisor ⇒ exact 2-power            (Nat.dvd_prime_pow)
  sorry

end AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01
```

**LOC budget** (revised):

| Item | LOC (est.) |
|------|-----------|
| `isConstructible_algebraic` (re-derive) | 10 |
| `isConstructible_minpoly_pow2` (re-derive) | 10 |
| `isConstructible_map_intermediate` (OPT-1) | 40–60 |
| `isConstructible_galois_two_group` (Steps 1–7) | 80–120 |
| Imports + docstring + namespace boilerplate | 30 |
| **Total (companion file)** | **170–230 LOC** |

This is slightly above the S1 OBSERVE estimate of ~200 LOC for the ⇒
direction, primarily because OPT-1 adds the relativized map lemma
(~50 LOC) that the S1 sketch elided.

---

## 7. ⇐ direction scope decision

S1 OBSERVE §2 estimated ~300 LOC for the ⇐ direction (Gal-2-group ⇒
constructible). This S2 PREP **confirms the spin-out recommendation**:

- ⇐ requires FTGT (Fundamental Theorem of Galois Theory) + Sylow
  theorems + degree-2 extensions are sqrt adjunctions. None of these
  pieces are stubbed in the parent.
- Combined with OPT-1's 40–60 LOC for the relativized map, ⇒ alone
  fills the realistic single-PR budget. ⇐ + ⇔ should land as a
  dedicated `angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-02`
  slug.

**Spin-out filing target**: Once ⇒ is verified (post-S4 ACT), file a
seeker-generated OQ-02 stub. This S2 PREP defers that action; no
spin-out is created in this iteration.

---

## 8. Conflict-free guarantees

This S2 PREP iteration touches **four files**, all strictly orthogonal
to any open PR on the shared parent file:

```
research/problems/angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01/
  sessions/2026-05-15-s2-prep-bearer-audit.md    [NEW]
  state.md                                        [UPDATED]
src/data/research/problems/
  angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01.json  [UPDATED]
```

No Lean changes. No parent-file edits. No edits to sibling slugs.

**Open PR search** (2026-05-15T23:14Z, pre-claim, repo-scoped):
```
gh pr list -R rjwalters/lean-genius \
  --search "angle-trisection-oq-02-oq-01-oq-02-incomplete-01-oq-01 in:title" \
  --state open --limit 20
# → 0 results (confirmed)
```

A broader `"angle-trisection in:title"` search returned 5 open PRs, all
on **different child slugs** (`oq-05-oq-04`, `cos-20-gal-oq-01-oq-03`),
not on `oq-02-oq-01-oq-02-incomplete-01-oq-01`. No overlap.

---

## 9. Next-action gate for S3 ACT

S3 ACT readiness checklist:

- [x] Bearer paths pinned (8 + 4 auxiliary)
- [x] Drift D-1 (B6 name + cardinality) documented; adopted `Nat.card`
- [x] Drift D-2 (parent docstring stale on Session 37 lemmas) documented;
  R2-pure recipe re-derives them in the companion
- [x] Drift D-3 (Step 4 σ existence harder than S1 sketch) documented;
  OPT-1 (relativized `isConstructible_map_intermediate`) recommended
- [x] Route decision: **R2-pure** (companion `AngleTrisectionOQ02OQ01OQ02Incomplete01OQ01.lean`,
  no parent edits)
- [x] Statement convention: `Nat.card (minpoly ℚ α).Gal = 2 ^ n`
- [x] Scope decision: ⇒ direction only in this slug; ⇐ defers to OQ-02
  spin-out

S3 ACT can begin from this checklist with **no further audit work
required**. Estimated S3 ACT LOC: 170–230, single companion file,
1–2 strategic sorries acceptable on OPT-1's induction or Steps 4–6 of
the main theorem.

---

## 10. Honest assessment

- This S2 PREP is **doc-only**. No theorem was proved; no Lean was
  modified.
- The session's value is in the two material drift findings (D-2, D-3)
  that revise the S1 OBSERVE plan. Without them, S3 ACT would have
  spent significant time discovering that `isConstructible_minpoly_pow2`
  doesn't exist and that `IsAlgClosed.lift` cannot directly give
  ℂ →ₐ[ℚ] ℂ.
- The bearer audit confirmed 7/8 S1 §3 paths (some by pinning paths
  not literally listed); 1/8 had a name + cardinality drift
  (B6: `card_eq_finrank_splittingField` → `card_of_separable`).
- The slug remains a moderate-tractability OQ extension. S3 ACT
  reach is realistic at 1–2 sessions.
