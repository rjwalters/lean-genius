# S7 PREP — Step 1b Artin-Schreier degree-2 no-root irreducibility scaffold (doc-only)

**Date**: 2026-06-02
**Researcher**: researcher-1
**Slug**: angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01
**Phase**: S7 PREP (doc-only; follows S6 ACT 2026-06-01 which closed Step 1a)
**Predecessor**: S6 ACT (researcher-1, 2026-06-01) — Step 1a `aGen_not_isSquare` (+ helpers + 9 Mathlib v4.26.0 latent-API-drift repairs); see `2026-06-01-s06.md`
**Lean file**: `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` (380 LOC, 22 theorems, 1 axiom, 0 sorries on `origin/main`)

## 1. Trigger

Picker drew this slug 2026-06-02, ~24 hours after S6 ACT merge. State:

| Source | Phase | Iteration | Last update | Open PRs |
|--------|-------|-----------|-------------|----------|
| `state.md` | COMPLETED + S6 ACT | 6 | 2026-06-01 | 0 |
| `meta.json` | `axiomatized` / `axiom` badge | — | — | — |
| `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean` | 380 LOC, 0 sorries, 1 axiom | — | 2026-06-01 (S6 ACT) | — |

S6 ACT closed **Step 1a** of the four-step Artin-Schreier chain that
discharges the single intentional axiom `counterexample_gal_card`. The
state.md `Next Action` paragraph names **Step 1b** (Artin-Schreier
degree-2 irreducibility of `g_factor = X² + X + aGen`) as the closest
tractable next ACT, estimated ~120-200 LOC.

This S7 PREP iteration is doc-only:
- the slug is `COMPLETED (axiomatized)` at gallery level — no urgency
- S6 ACT shipped a substantive `+95 LOC` Lean ACT only 24h ago
- Step 1b is a 120-200 LOC chunk that warrants its own dedicated ACT cycle
- a paste-ready scaffold + API-risk audit now is a force-multiplier for
  the eventual S7 ACT picker

## 2. Mathlib v4.26.0 API research (verified this session)

### 2.1 No Artin-Schreier named lemma

GitHub code search for `ArtinSchreier` over `leanprover-community/mathlib4`
returns **0 hits** (probed 2026-06-02). Mathlib v4.26.0 has no
`ArtinSchreier`, `IsArtinSchreier`, or `Polynomial.artinSchreier`
predicate, no `Polynomial.isIrreducible_artinSchreier` lemma, no
`Polynomial.isArtinSchreier_iff_no_root` characterisation. The state.md
expectation ("Mathlib v4.26.0 has degree-2 irreducibility helpers but no
Artin-Schreier-degree-2 named lemma") is **confirmed**.

### 2.2 Degree-2 irreducibility helpers (cited from Step 1a's mathlib4 deps)

| Mathlib lemma | Statement (informal) | Use |
|----------------|----------------------|-----|
| `Polynomial.irreducible_of_degree_eq_two` (if it exists) or specialisation | a degree-2 polynomial over a field is irreducible iff it has no root | top-level route |
| `Polynomial.degree_eq_iff_natDegree_eq` | bridges `degree = 2` ↔ `natDegree = 2 ∧ ≠ 0` | rewrite from existing `g_factor_natDegree` lemma |
| `Polynomial.roots_eq_zero_iff_X_sub_C` / `Polynomial.IsRoot.dvd` | "no root" formalisation | `∀ t, ¬ (g_factor.eval t = 0)` |

**Risk**: the exact name `Polynomial.irreducible_of_degree_eq_two` may not
exist verbatim — Mathlib often phrases this as a forward-only lemma like
`Polynomial.Monic.irreducible_of_irreducible_map` plus separate root-free
predicate. **S7 ACT MUST verify the exact API name before pasting.**

## 3. Mathematical strategy for Step 1b

**Statement** (target lemma):

```lean
lemma g_factor_irreducible : Irreducible g_factor
```

**Argument**: `g_factor = X² + X + aGen` has degree 2 over `base = FractionRing (Polynomial (ZMod 2))`. Since `base` is a field, a degree-2 polynomial is irreducible iff it has no root in `base`. So the problem reduces to:

```lean
lemma g_factor_no_root : ∀ t : base, g_factor.eval t ≠ 0
```

The Artin-Schreier reasoning enters here. Suppose `t² + t + aGen = 0` in `base`. Recall that in `base`, `aGen` is the image of `X : Polynomial (ZMod 2)` under `algebraMap`. The equation rearranges to `t² + t = aGen`. We aim to derive a contradiction by lifting to `Polynomial (ZMod 2)` via `IsLocalization.surj`.

By `IsLocalization.surj` (used in S6's Step 1a), `t = p/q` for some `p : Polynomial (ZMod 2)`, `q ∈ R⁰`. Substituting and multiplying through by `q²`:

```
(p/q)² + (p/q) = aGen
⟹  p² + p·q = X · q²    -- in Polynomial (ZMod 2)
```

(Using `aGen_lifted = X` after `algebraMap` injectivity, same template as S6 Step 1a's `hpq` derivation.)

The mathematical content of "no root in `base`" is then **the same parity argument** as Step 1a's `R_sq_eq_X_mul_sq_imp_false`, generalised. The key auxiliary helper is:

```lean
private lemma R_sq_add_R_mul_eq_X_mul_sq_imp_false
    {p q : Polynomial (ZMod 2)} (hq : q ≠ 0)
    (hpq : p * p + p * q = Polynomial.X * (q * q)) : False
```

**Outline of helper proof** (sketch, NOT yet verified):

1. Rewrite `p * p + p * q = p * (p + q)` (in any commutative ring).
2. So `p * (p + q) = X · q²`.
3. Case A: `p = 0`. Then LHS = 0 but `X · q² ≠ 0` (since `X ≠ 0` and `q ≠ 0`). Contradiction.
4. Case B: `p ≠ 0`. Then by UFD-ness of `Polynomial (ZMod 2)`, `X` divides `p · (p + q)`. Since `X` is prime (irreducible in UFD), either `X ∣ p` or `X ∣ (p + q)`.
   - **Sub-case B1**: `X ∣ p`. Write `p = X · p'`. Substitute:
     ```
     X · p' · (X · p' + q) = X · q²
     ⟹  p' · (X · p' + q) = q²
     ```
     Now compare degrees: deg(LHS) ≥ deg(p') + deg(X · p' + q). If `q ≠ 0` and deg(q) = deg(p'), then deg(X · p') > deg(q) so deg(X·p' + q) = deg(X·p') = 1 + deg(p'). LHS degree = 2·deg(p') + 1, RHS degree = 2·deg(q) = 2·deg(p'). Even = odd contradiction (modulo `omega`).
     Several more sub-subcases on relative degrees of `p, p', q` — needs careful enumeration.
   - **Sub-case B2**: `X ∣ (p + q)`. Symmetric to B1 by reversing the role of p and (p+q). Write `p + q = X · r`, then `q = X·r - p = X·r + p` in char 2. Substitute and continue.

**Estimated LOC**: 80-150 for the helper, +20-40 for the top-level `g_factor_irreducible`. Within state.md's S7 budget of 120-200 LOC.

**Verification status**: paper-sketch only. Specific case analysis on degrees has not been fully validated; the S7 ACT picker should expect ~2-3 Docker iterations to debug edge cases (esp. cancellation when `q = X·r`).

## 4. Paste-ready Lean scaffold (S7 ACT skeleton, NOT verified)

Insert after Step 1a's `aGen_not_isSquare` (line 249) and before Part II (line 251) of `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01OQ01.lean`:

```lean
-- ============================================================================
-- Part I.5: Step 1b — `g_factor = X² + X + aGen` is irreducible over `base`
-- ============================================================================
-- Strategy: in char 2, a degree-2 polynomial is irreducible iff no root.
-- Suppose t² + t + aGen = 0 for some t ∈ base; lift to Polynomial (ZMod 2)
-- via IsLocalization.surj, clear denominators, derive parity contradiction
-- by the helper R_sq_add_R_mul_eq_X_mul_sq_imp_false. Mirrors S6 Step 1a.
-- ============================================================================

/-- Internal helper: in `Polynomial (ZMod 2)`, the equation `p² + p·q = X · q²`
    with `q ≠ 0` is impossible. By UFD analysis on the factorisation
    `p · (p + q) = X · q²`. -/
private lemma R_sq_add_R_mul_eq_X_mul_sq_imp_false
    {p q : Polynomial (ZMod 2)} (hq : q ≠ 0)
    (hpq : p * p + p * q = Polynomial.X * (q * q)) : False := by
  sorry  -- S7 ACT TARGET

/-- **Step 1b**: `g_factor = X² + X + aGen` has no root in `base`. -/
lemma g_factor_no_root (t : base) : g_factor.eval t ≠ 0 := by
  intro heval
  -- t² + t + aGen = 0  ⟹  t² + t = aGen  (in char 2, -aGen = aGen)
  have h_root_eq : t * t + t = aGen := by
    -- unfold g_factor, eval, distribute, rearrange using CharP 2
    sorry  -- routine: 5-10 lines of ring/simp/CharP rewriting
  -- Apply IsLocalization.surj to write t = p/q
  obtain ⟨⟨p, q⟩, hyq⟩ :=
    IsLocalization.surj (M := nonZeroDivisors (Polynomial (ZMod 2)))
      (S := base) t
  set qP : Polynomial (ZMod 2) := (q : Polynomial (ZMod 2)) with hqP
  have hqv_ne : qP ≠ 0 := nonZeroDivisors.coe_ne_zero q
  -- Derive p · p + p · qP = X · (qP · qP)  in Polynomial (ZMod 2)
  have hpq : p * p + p * qP = Polynomial.X * (qP * qP) := by
    -- (i) Square hyq, (ii) translate to algebraMap equation, (iii) inject
    -- Pattern mirrors S6 aGen_not_isSquare proof (lines 232-248)
    sorry  -- 15-25 lines following the S6 template
  exact R_sq_add_R_mul_eq_X_mul_sq_imp_false hqv_ne hpq

/-- **Step 1b top-level**: `g_factor` is irreducible over `base`.

    Combines `g_factor_no_root` with a Mathlib degree-2 + no-root
    irreducibility criterion. The exact bearer name needs to be verified
    at S7 ACT time (candidate: `Polynomial.irreducible_of_degree_eq_two`
    or a `Polynomial.degree_eq_two_iff_*` characterisation). -/
lemma g_factor_irreducible : Irreducible g_factor := by
  sorry  -- S7 ACT: pin down the v4.26.0 API name and apply
```

## 5. API verification checklist (for S7 ACT picker)

Before pasting, verify the following Mathlib v4.26.0 lemma names via `gh api -X GET '/search/code'` or live mathlib4_docs WebFetch:

- [ ] `Polynomial.irreducible_of_degree_eq_two` — exact name + signature
- [ ] `Polynomial.degree_eq_two_iff_*` — alternative if above is missing
- [ ] `Polynomial.IsRoot.dvd` — used in case-B UFD analysis (sub-case B1/B2)
- [ ] `Polynomial.X_dvd_iff` — for the `X | p` decomposition (likely
      `Polynomial.X_dvd_iff_eval_zero` or `Polynomial.dvd_iff_isRoot`)
- [ ] `IsCoprime.X_*` or analogous: relating coprimality to `X`-divisibility
- [ ] `Polynomial.natDegree_add_eq_left/right_of_natDegree_lt` — for the
      degree-comparison step in case B1/B2

## 6. ACT-readiness gate (post-S7 PREP)

| Dim | Signal | S6 status | S7 PREP status (this PR) |
|-----|--------|-----------|--------------------------|
| 1 | Lean file builds GREEN under Docker | ✅ (S6 7746 jobs, 0 errors) | ✅ unchanged |
| 2 | Mathlib pin stable | ✅ `2df2f0150c…` | ✅ unchanged |
| 3 | Paste-ready Step 1b Lean scaffold | ❌ (only state.md mention) | 🟡 SKELETON with 4 sorries (helper + 3 above) |
| 4 | API names verified | ❌ | 🟡 4 candidates listed, verification deferred to ACT |
| 5 | Cross-slug additive | ✅ unchanged | ✅ unchanged |
| 6 | Sibling races | ✅ (0 open PRs on slug) | ✅ unchanged |
| 7 | Docker B1 daemon | ✅ GREEN (S6) | ✅ presumed (24h since) |
| 8 | Disk pressure | ✅ (S6 had ≥ 62 Gi after recovery) | ✅ presumed |

**Verdict**: 6 GREEN + 2 YELLOW. The 2 YELLOWs (paste-ready scaffold has 4
sorries; API names not name-verified) are *intentional* — the S7 PREP
ships the strategic skeleton and defers full Lean discharge to the
dedicated S7 ACT cycle (estimated 1-2 Docker iterations for the helper +
1 for the wiring).

## 7. NOT shipped

- No Lean edits (paste-ready scaffold remains in this memo, not in the
  Lean file)
- No `meta.json` edits (slug is `COMPLETED (axiomatized)` at gallery
  level; counts already current at 22 theorems / 1 axiom / 0 sorries)
- No bearer-pin SHA re-check (Mathlib SHA stable 19+ days; spot-check
  would be busywork)

## 8. Files touched this PR

* `research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/state.md`
  — header refresh: Phase S6 ACT → S7 PREP, Iteration 6 → 7, Owner /
  Last Updated / Branch, S7 PREP session-log entry.
* `research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01-oq-01/sessions/2026-06-02-s07-prep-step1b-artin-schreier-degree2-noroot.md`
  — this memo.

**Zero changes to**: `proofs/Proofs/*.lean`, `proofs/Proofs.lean`,
`problem.md`, `knowledge.md`, `src/data/research/problems/*.json`,
`src/data/proofs/*/meta.json`, `annotations.json`, `index.ts`.
