# Session S15 ACT — Uniform trace bridge `r_subLeadingCoeff_eq_neg_p_uniform` (build verified)

**Date**: 2026-05-14
**Researcher**: researcher-3 (claim TTL 90 min, knowledge score 24 / RICH)
**Mode**: ACT (Lean implementation, Docker-build verified)
**Phase**: S14 PREP → S15 ACT — discharge the audited two-stage trace-bridge implementation

## What this session ships

S11–S14 PREP (researcher-12, researcher-9, researcher-5) designed and
audited a two-stage proof template for the uniform trace fingerprint of
`r p` for the verified primes. S15 ACT lands all three audited
deliverables in the parent file
`proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`.

### Stage 1 — Uniform sub-leading coefficient of `Φ_{2p}` (all odd primes p ≥ 3)

```lean
theorem cyclotomic_two_mul_prime_subLeadingCoeff_uniform
    {p : ℕ} (hp : p.Prime) (hp_odd : Odd p) :
    (cyclotomic (2 * p) ℤ).coeff (p - 2) = -1
```

Proves the **trace counterpart** of the S9 norm anchor
`cyclotomic_two_mul_prime_eval_neg_one_uniform` (`Φ_{2p}(−1) = p`).
Both follow from the same geometric-series identification
`Φ_{2p} = ∑_{i<p} (−X)^i` (S9 structural lemma).

**Proof structure** (4 steps, ~30 LOC):
1. Rewrite `Φ_{2p}` via S9 structural lemma to `∑ i ∈ range p, (−X)^i`.
2. Distribute `coeff (p − 2)` over the sum via `finset_sum_coeff`
   (S12 PREP cited `Polynomial.finsetSum_coeff` — the actual v4.26.0
   name is snake_case `finset_sum_coeff` at `Mathlib/Algebra/Polynomial/Coeff.lean:89`,
   which is `@[simp]`-tagged; see Bearer audit erratum below).
3. `Finset.sum_eq_single (p − 2)` — only the `i = p − 2` term contributes
   nonzero coefficient at index `p − 2` (off-diagonal vanishing via
   the helper lemma `neg_X_pow_coeff_eq`).
4. Surviving coefficient is `(−1)^(p − 2) = −1` because `p − 2` is odd
   (since `p` is odd ≥ 3); discharged by `Odd.neg_one_pow`.

**Companion private lemma** `neg_X_pow_coeff_eq` distributes
`((-X)^i).coeff k = (−1)^i * (if k = i then 1 else 0)` for arbitrary
`i, k : ℕ`, using `(-X) = -1 * X` + `mul_pow` + `(-1 : ℤ[X])^i = C ((-1)^i)`
(from `← C_pow`) + `coeff_C_mul` + `coeff_X_pow`.

### Stage 2a — Per-prime structural bridge (`p ∈ {5, 7, 11, 13}`)

```lean
theorem r_subLeadingCoeff_via_moebius_uniform :
    ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p - 1) / 2 - 1)
        = -((p : ℤ) - 1) + (cyclotomic (2 * p) ℤ).coeff (p - 1 - 1)
```

Per-prime decomposition of the trace into `−(p − 1)` (the constant shift
across the `(p − 1)/2` real conjugates) plus the cyclotomic sub-leading
`Φ_{2p}.coeff (p − 2)`.

**Proof** (4 branches × 3 LOC = ~30 LOC): `rcases` destructure of
`p ∈ {5, 7, 11, 13}`; each branch unfolds `r p` via `r_p_eq`, normalises
the cyclotomic index `2 * p → 2p` via `show`, rewrites with the
explicit `cyclotomic_{2p}_eq` form (S5/S6), expands coefficients via
`simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C,
coeff_X, coeff_one]`, and closes with `decide` on the literal integer
arithmetic.

**Excludes `p = 3`**: `(3-1)/2 - 1 = 0` collides with the
constant-coefficient case (already handled by `r_3_traceCoeff` and
the S10 `r_constantCoeff_eq_signed_uniform`).

### Stage 2b — Finset-quantified trace fingerprint corollary

```lean
theorem r_subLeadingCoeff_eq_neg_p_uniform :
    ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p - 1) / 2 - 1) = -(p : ℤ)
```

Combines Stage 2a with Stage 1 to derive `−p` directly from the
cyclotomic-anchor route, **without** the case-by-case `decide` chain
that the existing per-prime `r_subLeadingCoeff_eq_neg_p` (S4) uses.
Index `p − 1 − 1` reduces to `p − 2` via `omega` from `Prime p`'s
`two_le`. ~10 LOC.

**Why not just repackage `r_subLeadingCoeff_eq_neg_p` as a Finset
conjunction?** Stage 2b deliberately routes through the
**cyclotomic anchor** (Stage 1), making the dependence on the
Möbius identity `μ(2p) = 1` explicit in the proof term. This mirrors
the S10 architectural choice for the constant-coefficient corollary
(which routes through the S9 numerical anchor). The two corollaries
together package both Vieta endpoints of `r p` in a uniform
cyclotomic-anchor form.

## Stats

- **File grows**: 1166 → 1383 LOC (+217 LOC: docstring header ~80 LOC,
  helper lemma ~10 LOC, Stage 1 ~30 LOC, Stage 2a ~30 LOC, Stage 2b
  ~12 LOC, ad-hoc whitespace/markdown ~55 LOC).
- **Theorems**: 61 → 64 named theorems (+3: Stage 1, Stage 2a, Stage 2b)
  plus 1 private lemma (`neg_X_pow_coeff_eq`).
- **Sorries**: 1 → 1 (unchanged — the open conjecture).
- **Axioms**: 0 → 0 (unchanged).
- **Mathlib bearers used**: `cyclotomic_two_mul_prime_eq_geom_neg_series`
  (S9), `cyclotomic_{ten,fourteen,22,26}_eq` (S5/S6), `r_{5,7,11,13}_eq`,
  `finset_sum_coeff`, `Finset.sum_eq_single`, `Finset.mem_range`,
  `Odd.neg_one_pow`, `Polynomial.coeff_{sub,add,C_mul,X_pow,C,X,one}`,
  `mul_pow`, `C_neg`, `C_1`, `C_pow`, `Polynomial.coeff_C_mul`.

## Build status

**VERIFIED CLEAN.** Docker build at warm Mathlib cache: `7743 jobs`,
~90s wall-clock, 0 errors, 0 sorries-introduced (the existing
`eisenstein_conjecture_cos_pi_p` sorry is unchanged).

Build log: `.loom/logs/researcher-3-s15-build3.log` (final clean build
after 2 surgical fix iterations).

## Surgical-fix iterations

| Iter | Issue | Fix |
|---|---|---|
| 1 → 2 | `Unknown identifier finsetSum_coeff` (S12 PREP cited camelCase form) | Rename to snake_case `finset_sum_coeff` per actual v4.26.0 lemma at `Mathlib/Algebra/Polynomial/Coeff.lean:89` |
| 1 → 2 | `Function expected at C_pow` (cited as `C_pow (a) (n)`) | Use `← C_pow` rewrite — `C_pow` has implicit args, no function-application syntax |
| 2 → 3 | 3 unused simp args per Stage 2a branch (`coeff_X_pow_self`, `coeff_one_zero`, `coeff_X_one`) flagged by `linter.unusedSimpArgs` | Trim simp set to `[coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X, coeff_one]` (7 lemmas) |

## Bearer audit erratum (S12 PREP correction)

S12 PREP (PR #18571) §1 Bearer-table claimed:
> `Finset.sum_coeff` (S11 PREP) → `Polynomial.finsetSum_coeff` (camelCase)
> at `Mathlib/Algebra/Polynomial/Coeff.lean:89-91`. The snake_case alias
> `finset_sum_coeff` is **DEPRECATED since 2026-04-08** (Coeff.lean:93).

**Both halves of this claim are inverted at v4.26.0.** Direct
verification by `curl https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/Mathlib/Algebra/Polynomial/Coeff.lean`:

```
@[simp]
theorem finset_sum_coeff {ι : Type*} (s : Finset ι) (f : ι → R[X]) (n : ℕ) :
    coeff (∑ b ∈ s, f b) n = ∑ b ∈ s, coeff (f b) n :=
  map_sum (lcoeff R n) _ _
```

at line **89** (snake_case, `@[simp]`-tagged, **canonical**, no
deprecation tag). Line 93 (S12's claimed deprecation tag location)
contains `map_sum (lcoeff R n) _ _` — the proof body — not a
deprecation. There is **no** `finsetSum_coeff` (camelCase) name in
v4.26.0 Mathlib at the cited file.

The S15 ACT implementation uses the **actual v4.26.0 name** `finset_sum_coeff`
(snake_case). This is consistent with the in-file precedent: the S9
proof (`cyclotomic_two_mul_prime_eval_neg_one_uniform` at line 1052)
uses `eval_finset_sum` — Mathlib's snake_case naming convention.

**Implication for future PREPs**: Mathlib v4.26.0's actual lemma names
should be confirmed by direct `curl` of the pinned-rev source rather
than relying on memory of HEAD or assumed naming conventions. The
v4.26.0 pin at `proofs/lakefile.toml:7-9` is the canonical reference.

## Connection to the open conjecture

S15 closes the **second** of the two Vieta fingerprints in uniform form:

| Endpoint | Identity | Anchor | Uniform thm |
|---|---|---|---|
| Constant `(r p).coeff 0` | `(-1)^((p-1)/2) · p` | `Φ_{2p}(-1) = p` (S9) | `r_constantCoeff_eq_signed_uniform` (S10) |
| Sub-leading `(r p).coeff ((p-1)/2 - 1)` | `-p` | `Φ_{2p}.coeff (p-2) = -1` (S15 Stage 1) | `r_subLeadingCoeff_eq_neg_p_uniform` (S15 Stage 2b) |

Both endpoints now have a **single uniform proof** routed through a
cyclotomic structural anchor for `Φ_{2p}` plus a per-prime decomposition
of `r p`. The uniform conjecture
`eisenstein_conjecture_cos_pi_p` (line 1378, sorry) needs the **deeper**
sub-leading divisibility for *all* indices `0 ≤ k < (p-1)/2`, not just
the two extreme endpoints — that requires the cyclotomic ramification
calculation or the local-field uniformizer theorem (Neukirch ANT II.6).

## Pool / race state at session end

- **0 open S15 / Stage-1 / Stage-2 / trace-bridge PRs** (verified via
  `gh pr list -R rjwalters/lean-genius --search "angle-trisection-cos-20-gal-oq-01-oq-03 in:title" --state open`).
- **Companion stale ACT PR**: #17906 (S4 — irreducibility round-out for
  small-prime suite, build pending, opened 2026-05-12T06:22Z, ~46h old).
  This S15 ACT is **not** orthogonal-by-construction to #17906 —
  both touch `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` —
  but the two ACT regions are line-disjoint (S4 touches the
  irreducibility chain at lines ~395-437; S15 inserts the trace bridge
  at lines ~1135-1352). Merge ordering: S15 first (verified clean) is
  the lower-risk choice; #17906's PR description claims build-pending
  status that this session did not verify.

## Anti-targets

S15 ACT does **not**:
- Touch `eisenstein_conjecture_cos_pi_p` (line 1378). The open
  conjecture's general-prime sorry is unchanged.
- Modify the S5/S6 cyclotomic anchor lemmas (lines 488–700) referenced
  as bearers.
- Modify the S8/S9 uniform bridge or anchor (lines 870–1056).
- Modify the S3-era `r_constantCoeff_eq_signed_p` or S4-era
  `r_subLeadingCoeff_eq_neg_p` (lines 304–391) — the S15 corollaries
  are the **uniform packagings** of those per-prime fingerprints, not
  replacements.
- Edit `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/{meta,annotations}.json`.
  The file's gallery view will be refreshed by the deployer's
  auto-meta-update pipeline; this session updates only the slug-private
  state.md + JSON.
- Touch sibling slug files (`AngleTrisectionCos20Gal*.lean`).
- Bump the Mathlib pin past v4.26.0.

## Honesty / verification log

### Lean code

- 217-LOC additive insert at lines 1135-1352 in
  `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`.
- 0 LOC removed; 0 existing theorems modified.
- 1 private helper lemma (`neg_X_pow_coeff_eq`) + 3 named theorems
  (Stage 1, Stage 2a, Stage 2b).
- 0 axioms added; 1 sorry (the open conjecture, unchanged).

### Build verification

- `./proofs/scripts/docker-build.sh Proofs.AngleTrisectionCos20GalOQ01OQ03`
  ran 3 times this session:
  - **build1** (initial): FAIL on `finsetSum_coeff` (S12 erratum) +
    `C_pow` (function-application syntax).
  - **build2** (post-fix): SUCCESS, 7743 jobs, 90s warm. 9 unused
    simp-arg warnings (3 per Stage 2a branch).
  - **build3** (cleanup): SUCCESS, 7743 jobs, ~90s warm. 0 errors,
    0 unused simp args, 1 sorry (pre-existing, unchanged).
- Final build log: `.loom/logs/researcher-3-s15-build3.log`.

### Bearer-name verification

- `finset_sum_coeff` at v4.26.0 verified via direct `curl` of
  `Mathlib/Algebra/Polynomial/Coeff.lean:89` (snake_case, `@[simp]`,
  no deprecation tag at line 93).
- `C_pow` at v4.26.0 verified via direct `curl` of
  `Mathlib/Algebra/Polynomial/Basic.lean:480` (implicit args
  `{a : R} {n : ℕ}`, `C (a^n) = C a ^ n`).
- `Odd.neg_one_pow` confirmed via local grep of `proofs/Proofs/`
  (active use in `ElementaryQuadraticReciprocityOQ03OQ02OQ03.lean`,
  `TaylorSinCosConvergenceOQ03.lean`, `DerangementsOQ03.lean`,
  `Erdos1131Problem.lean`).
- S5/S6 `cyclotomic_{ten,fourteen,22,26}_eq` confirmed at lines
  500, 513, 649, 663 of the parent file.
- `r_{5,7,11,13}_eq`, `Finset.mem_insert`, `Finset.mem_singleton`,
  `Finset.sum_eq_single`, `Finset.mem_range` all standard, used
  elsewhere in the project.

### What could be wrong

- The proof routes through `cyclotomic_two_mul_prime_eq_geom_neg_series`
  (S9 lemma at line 1000) — if a future Mathlib bump changes the
  cyclotomic API or the geometric-series form, the S9 lemma could
  break and Stage 1 would cascade. Mitigation: the v4.26.0 pin is
  fixed at `proofs/lakefile.toml:7-9`; the S15 build verification
  was at this exact pin.
- The 4-branch `rcases` in Stage 2a is fragile to additions to the
  verified prime set. If S16+ extends the gallery to `p ∈ {5, 7, 11,
  13, 17}`, both Stage 2a and Stage 2b need an additional branch.
- The Möbius identity `μ(2p) = 1` is implicit in the structure of
  the proof but not explicitly stated as a lemma. A future
  refactor could extract it as `r_subLeadingCoeff_via_moebius_uniform`'s
  cyclotomic-side companion.
