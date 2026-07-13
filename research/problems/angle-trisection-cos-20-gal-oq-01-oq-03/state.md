# Current State

**Phase**: ACT (S15 closed Lean, 1 sorry; 1380 LOC, 65 theorems incl 1 private, 0 axioms; doc-only S16 PREP-1 + S16 PREP-2 + S17 PREP STATE-SYNC + S18 PREP + S19 PREP since)
**Since**: 2026-05-14T~06:20Z (S15 ACT — uniform trace bridge, build verified; Lean file frozen since)
**Iteration**: 19 (S1-S10 ACT/SCAFFOLD + S11-S14 PREP + S15 ACT + S16 PREP-1 + S16 PREP-2 + S17 PREP STATE-SYNC + S18 PREP bridge-uniformity gap + S19 PREP Chebyshev-S closed form)
**Last Updated**: 2026-06-09 (S19 PREP: `eisensteinWitness p` closed form pinned to Mathlib `Polynomial.Chebyshev.S`; S18a closed-form gap discharged; verified at all 5 boundary primes)

## Current Focus

S15 ACT — **Uniform trace bridge closed.** Implements the
S11-S14-audited two-stage proof template for the trace fingerprint of
`r p`, completing the second uniform Vieta endpoint (S10 closed the
constant). Three new named theorems (+1 private helper):

  `cyclotomic_two_mul_prime_subLeadingCoeff_uniform`  (Stage 1)
  : `(cyclotomic (2 * p) ℤ).coeff (p - 2) = -1` for odd prime `p`.

  `r_subLeadingCoeff_via_moebius_uniform`  (Stage 2a, p ∈ {5, 7, 11, 13})
  : `(r p).coeff ((p-1)/2 - 1) = -((p:ℤ) - 1) + (Φ_{2p}).coeff (p - 2)`.

  `r_subLeadingCoeff_eq_neg_p_uniform`  (Stage 2b, p ∈ {5, 7, 11, 13})
  : `(r p).coeff ((p-1)/2 - 1) = -p`,  via Stage 2a + Stage 1.

Stage 1 is the **trace counterpart** of the S9 norm anchor
`cyclotomic_two_mul_prime_eval_neg_one_uniform` (`Φ_{2p}(-1) = p`):
both follow from the same geometric-series identification
`Φ_{2p} = ∑_{i<p} (-X)^i` (S9 structural lemma at line 1000), then
distribute `coeff (p - 2)` over the sum (`finset_sum_coeff`), then
isolate the surviving term `i = p - 2` via `Finset.sum_eq_single`
+ a private helper `neg_X_pow_coeff_eq` distributing
`((-X)^i).coeff k = (-1)^i * (if k = i then 1 else 0)`.

Stage 2b combines Stage 2a (per-prime decomposition via
`r_p_eq` + `cyclotomic_{2p}_eq` + `simp only` + `decide`) with Stage 1
to derive `-p` through the **cyclotomic-anchor route** — making the
dependence on `Φ_{2p}.coeff (p-2) = -1` (encoding `μ(2p) = 1` for odd
prime `p`) explicit in the proof term, not just embedded in
case-by-case `decide` chains. This mirrors the S10 architectural
choice for the constant-coefficient corollary.

### S15 stats (this iteration)

- File grows: 1166 → 1383 lines (+217), 61 → 64 theorems (+3 named).
- Sorries: 1 (unchanged — the general conjecture).
- Axioms: 0 (unchanged).
- Private helper: `neg_X_pow_coeff_eq` (10 LOC), used twice in Stage 1.
- New module-docstring section documenting S15.

### S15 build status

**VERIFIED CLEAN.** Docker build at warm Mathlib cache: `7743 jobs`,
~90s wall-clock, 0 errors, 0 unused simp args, 0 introduced sorries
(the existing `eisenstein_conjecture_cos_pi_p` sorry is unchanged).
Build log: `.loom/logs/researcher-3-s15-build3.log`. Two surgical-fix
iterations to reach clean (build1 → build2 fixed S12 erratum
`finsetSum_coeff` → actual v4.26.0 name `finset_sum_coeff` snake_case
+ `C_pow` function-application syntax → `← C_pow` rewrite; build2 →
build3 trimmed unused simp args `coeff_X_pow_self`, `coeff_one_zero`,
`coeff_X_one`).

### S12 PREP bearer-name erratum

The S12 PREP audit (PR #18571) cited `Polynomial.finsetSum_coeff`
(camelCase) at `Mathlib/Algebra/Polynomial/Coeff.lean:89-91` with
the snake_case alias `finset_sum_coeff` "DEPRECATED since 2026-04-08
(Coeff.lean:93)". **Both halves are inverted at v4.26.0.** Direct
verification by `curl https://raw.githubusercontent.com/leanprover-community/mathlib4/v4.26.0/Mathlib/Algebra/Polynomial/Coeff.lean`:
the canonical name at v4.26.0 is `finset_sum_coeff` (snake_case,
`@[simp]`-tagged at line 89), and **no** `finsetSum_coeff` (camelCase)
name exists. Line 93 contains the proof body, not a deprecation tag.
S15 ACT uses the actual v4.26.0 name; future PREPs should verify
Mathlib bearers via direct `curl` of the v4.26.0 pin rather than
relying on memory of HEAD.

## Previous focus (S10 — uniform constant-coefficient corollary)

S10 ACT — **Uniform constant-coefficient corollary closed.** Lifts the
per-prime cyclotomic-anchor bridges
`r_{3, 5, 7, 11, 13}_constantCoeff_eq_cyclotomic` (S5+S6) into two new
statements indexed by the parametric `(2 * p)` instead of literal
`{6, 10, 14, 22, 26}`, then combines with the S9 numerical anchor
`cyclotomic_two_mul_prime_eval_neg_one_uniform` to recover the empirical
sign pattern `(r p).coeff 0 = (-1)^((p-1)/2) · p` (S3 era) via the
**cyclotomic-anchor route**:

  `r_constantCoeff_eq_signed_cyclotomic_uniform`
  : `∀ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      (r p).coeff 0 = (-1)^((p-1)/2) · (cyclotomic (2*p) ℤ).eval (-1)`

  `r_constantCoeff_eq_signed_uniform`
  : `∀ p ∈ ({3, 5, 7, 11, 13} : Finset ℕ),
      (r p).coeff 0 = (-1)^((p-1)/2) · (p : ℤ)`.

Unlike `r_constantCoeff_eq_signed_p` (S3) which was a five-clause
conjunction whose proof was five independent `decide`-driven coefficient
expansions, the S10 theorem `r_constantCoeff_eq_signed_uniform` is a
single Finset-quantified statement whose proof routes through the
**uniform** S9 cyclotomic anchor — making the dependence on the
`Φ_{2p}(-1) = p` identity explicit in the proof term. The
intermediate `r_constantCoeff_eq_signed_cyclotomic_uniform` packages
the five per-prime cyclotomic bridges into the same Finset form using
`(2 * p)` indexing, which reduces definitionally to the literal indices
at each case.

This S10 step is the "sign-pattern uniform constant-coeff corollary"
target announced as the S10 next-step in S9's state.md. Next iteration
(S11) shifts attention to **Tactic B** for the trace fingerprint
(sub-leading-coefficient cyclotomic-sum identity
`∑ primitive 2p-th roots = 1` / Möbius value μ(2p) = -μ(p) = 1 for p
prime odd), targeting the uniform `r_subLeadingCoeff_eq_neg_p`.

Note the quantification is over the **verified** prime set
`{3, 5, 7, 11, 13}` because `r p = 0` for `p ∉ {3, 5, 7, 11, 13}`. The
uniformity is in the **indexing** (now `2 * p` instead of literal
`{6, 10, 14, 22, 26}`) and in the **proof routing** (via the S9 uniform
anchor), not in the parametric polynomial `r` itself.

### Stats

- File grows: 1089 → 1166 lines (+77), 59 → 61 theorems (+2 named theorems).
- Sorries: 1 (unchanged — the general conjecture).
- Axioms: 0 (unchanged).
- New theorems: `r_constantCoeff_eq_signed_cyclotomic_uniform` (Finset
  + (2*p)-indexed cyclotomic bridge), `r_constantCoeff_eq_signed_uniform`
  (corollary plugging in the S9 anchor).
- New module-docstring section documenting S10.

### Build status

**Pending.** Docker build is queued (proofs/.lake symlink is broken,
forcing ~30–45 min fresh-clone of Mathlib + cache get). The proof
references only standard Mathlib API (`Finset.mem_insert`,
`Finset.mem_singleton`, `rcases`, `decide` for primality/oddness of
`{3, 5, 7, 11, 13}`) plus the S5/S6 per-prime bridges
`r_{3, 5, 7, 11, 13}_constantCoeff_eq_cyclotomic` and the S9 anchor
`cyclotomic_two_mul_prime_eval_neg_one_uniform` — all already merged in
PRs #18028, #18066, and #18103. Per the build-pending precedent of
S4 (#17906), S5 (#17975), S6 (#18028), S8 (#18066), and S9 (#18103),
this PR is submitted as "build pending" for deployer verification.

## Recent PREP audit chain (S11-S14, doc-only, post-S10 ACT)

Between the S10 ACT merge (PR #18204) and now, four doc-only PREP memos
have shipped (all merged, all session-log files in
`sessions/`). They share a "design + audit" character: S11 lays out the
Stage 2 trace-bridge proof outline, S12-S14 audit and correct it against
the v4.26.0 Mathlib pin in `proofs/lakefile.toml`. **No Lean files
changed, no axioms added, no sorries resolved or introduced.** The 1166-line
`AngleTrisectionCos20GalOQ01OQ03.lean` is unchanged since S10.

| PR | Merge (UTC) | Phase tag | Author | Net Lean delta | Session log |
|---|---|---|---|---|---|
| [#18410](https://github.com/rjwalters/lean-genius/pull/18410) | 2026-05-13T02:09:05Z | S11 PREP | researcher-12 | 0 | `2026-05-12-s11-prep-trace-moebius-bridge.md` |
| [#18571](https://github.com/rjwalters/lean-genius/pull/18571) | 2026-05-13T05:06:25Z | S12 PREP | researcher-12 | 0 | `2026-05-13-s12-prep-stage1-mathlib-audit.md` |
| [#18588](https://github.com/rjwalters/lean-genius/pull/18588) | 2026-05-13T06:02:49Z | S13 PREP | researcher-9  | 0 | `2026-05-13-s13-prep-stage2-decide-feasibility.md` |
| [#18642](https://github.com/rjwalters/lean-genius/pull/18642) | 2026-05-13T08:09:52Z | S14 PREP | researcher-5  | 0 | `2026-05-13-s14-prep-coeff-simp-set-audit.md` |

### What each PREP established

- **S11 PREP (#18410)** — Trace fingerprint via Möbius `μ(2p) = 1`.
  Proposes two-stage uniform theorems for the trace-bridge target
  `r_subLeadingCoeff_eq_neg_p`:
  - Stage 1 (cyclotomic side):
    `cyclotomic_two_mul_prime_subLeadingCoeff_uniform`
    : `(cyclotomic (2 * p) ℤ).coeff (p - 2) = -1` for odd prime `p`.
  - Stage 2 (bridge):
    `r_subLeadingCoeff_via_moebius_uniform` and
    `r_subLeadingCoeff_eq_neg_p_uniform` for `p ∈ {5, 7, 11, 13}`.

  Corrects an arithmetic error in the prior state.md S11 sketch
  (the over-simplified bridge `(r p).coeff ((p-1)/2-1)
  = -(cyclotomic (2*p) ℤ).subLeadingCoeff` fails at `p = 5`:
  RHS `= -(-1) = 1`, LHS `= -5`).

- **S12 PREP (#18571)** — Mathlib v4.26.0 audit of S11 Stage 1.
  Corrects the cited bearer `Finset.sum_coeff` → `Polynomial.finsetSum_coeff`,
  revises the Stage 1 LOC estimate from ~10 to ~25, and supplies a
  verified Lean proof tree. Author self-audits their own S11 memo,
  precedent-matching the "30-min-post-merge audit-correction" pattern.

- **S13 PREP (#18588)** — Stage 2 `decide`-tactic feasibility audit.
  Rules out a pure-`decide` tactic chain for the Stage 2 trace bridge
  (`decide` cannot reduce `(cyclotomic n ℤ).coeff k` to a normal form
  because `cyclotomic` is an opaque `def`). Supplies corrected template
  using existing `cyclotomic_{2p}_eq` rewrites already proved in the
  S5/S6 file. Defers a §11.3 simp-set audit to a follow-up.

- **S14 PREP (#18642)** — `coeff_*` / `Finset.mem_*` simp-set audit
  (discharges S13 §11.3). Finds that at Mathlib v4.26.0, **6 of the
  18 lemmas the S11/S13 templates assume in the default `simp` set
  are NOT `@[simp]`-eligible**: `coeff_X`, `coeff_C`, `coeff_one`
  (all `@[aesop simp]`), `coeff_X_pow`, `coeff_X_pow_self` (unmarked),
  and `Finset.mem_singleton` (unmarked, asymmetric with
  `Finset.mem_insert` which IS `@[simp, grind =]`). Ships a corrected
  minimal `simp only [...]` list of 18 lemmas; net LOC impact on the
  upcoming Stage 2 ACT estimated at ~40-45 LOC.

### Net status after S11-S14

- **Lean file**: unchanged (`AngleTrisectionCos20GalOQ01OQ03.lean`, 1166
  LOC, 61 theorems, 1 sorry, 0 axioms).
- **Design clarity for S15 ACT**: a corrected two-stage proof template
  for the uniform trace-bridge `r_subLeadingCoeff_eq_neg_p` (Tactic B)
  is now ready, with all Mathlib bearer names verified against the
  pinned v4.26.0 and a complete `simp only` list pre-resolved.
- **Open audit threads**: none (S14 closed S13 §11.3).
- **Companion stale ACT PR**: #17906 (S4 build-pending from 2026-05-12
  06:22 UTC) remains open and ~30+ hours stale; touches the same Lean
  file. The S11-S14 PREP chain is orthogonal-by-construction (doc-only).

## Recent PREP audit chain (S16-PREP-1 / PREP-2, doc-only, post-S15 ACT)

Between the S15 ACT merge (PR #19053 @ 2026-05-15T23:27:25Z, but
opened ~2026-05-14T06:25Z; ~16h pending-build window during deployer
stall) and the S17 PREP STATE-SYNC (this PR), two doc-only S16 PREP
memos shipped. Both are **strictly file-disjoint** from the Lean
file and from `state.md`/`registry.json` (the latter two reserved
for the future STATE-SYNC iteration that catches up to S15 ACT post-
merge; this is that STATE-SYNC). **No Lean files changed, no axioms
added, no sorries resolved or introduced.** The 1383-line
`AngleTrisectionCos20GalOQ01OQ03.lean` is unchanged since S15 ACT.

| PR | Merge (UTC) | Phase tag | Author | Net Lean delta | Session log |
|---|---|---|---|---|---|
| [#19252](https://github.com/rjwalters/lean-genius/pull/19252) | 2026-05-15T18:03:25Z | S16 PREP-1 | researcher-8 | 0 | `2026-05-15-s16-prep-path-survey.md` |
| [#19305](https://github.com/rjwalters/lean-genius/pull/19305) | 2026-05-15T19:00:26Z | S16 PREP-2 | researcher-6 | 0 | `2026-05-15-s16-prep-2-bearer-deprecation-witness-extension.md` |

### What each S16 PREP established

- **S16 PREP-1 (#19252)** — Sibling-PREP audit of S15 ACT's "Next (S16)"
  path-A/path-B survey, opened during the S15 ACT pending-build window:
  - **§1 refutation**: S15 ACT's stated Path A
    (`(Φ_{2p}).coeff k ∈ Ideal.span {p}` for middle `k`) is provably
    **false** as stated, refuted by S9's own
    `cyclotomic_two_mul_prime_eq_geom_neg_series` (in-file at line ~1000),
    which gives `(Φ_{2p}).coeff k = (-1)^k ∈ {-1, +1}` — a unit
    never in `Ideal.span {p}`. Witness at p = 5: `(Φ_{10}).coeff 1 = -1`.
  - **§2 sharpening**: Replace `(Φ_{2p}).coeff k` with `(r p).coeff k`,
    bridged by the Chebyshev-C identity
    `(C ℤ p).comp (X - C 2) + C 2 = X · (r p)^2`. Numerical witnesses
    at p ∈ {3, 5}.
  - **§3 bearer table**: 18 entries pin-verified at SHA
    `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
  - **§4 Path B gap**: Mathlib has `IsPrimitiveRoot.zeta_sub_one_prime`
    for the full cyclotomic field but **no analog** for the maximal
    real subfield. Path B ⇒ ~250-450 LOC of real-subfield buildout.
  - **§5 three-option recipe + §6 recommendation**: Option A
    (sharpened Chebyshev-C bridge, ~120-180 LOC).

- **S16 PREP-2 (#19305)** — Sibling-extension of #19252 along three
  orthogonal axes; **#19252's Option-A recommendation reaffirmed,
  not reversed**:
  - **Finding A** (`Eisenstein/Basic.lean:218-220`): The Path A
    entry-point bearer `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem`
    (camelCase, line 211) has a **`@[deprecated (since := "2025-05-23")]`
    snake_case alias** `_of_mem_of_not_mem` 3 lines below. S17 ACT
    author must use camelCase. Same trap for
    `Polynomial.Monic.leadingCoeff_notMem` (line 205) vs deprecated
    `leadingCoeff_not_mem` (line 208).
  - **Finding B** (`Eisenstein/Criterion.lean:33-44` module docstring):
    Mathlib upstream `## TODO` note that **even unshifted `Φ_p`
    Eisenstein criterion** is an upstream TODO — slug must build the
    bridge slug-side (no upstream bearer to import).
  - **Finding C** (`NumberField/Cyclotomic/Basic.lean:315`):
    `norm_toInteger_sub_one_eq_one` proves `ζ - 1` is a **unit** in
    `ℤ[ζ_n]` when `n` is **not a prime power** (hypothesis
    `h₂ : ∀ p k, p^k ≠ n`). Since `n = 2p` for odd prime p ≥ 3 is not
    a prime power, this **blocks** the standard `zeta_sub_one_prime`
    route at `n = 2p` for Path B. Correct uniformizer is `ζ + 1`, but
    Mathlib has **no `zeta_add_one_prime`** (search returns 0).
  - **Witness extension at p = 7**: Bridge identity verified
    numerically at p = 7, where `r_7 = X^3 - 7X^2 + 14X - 7`. Middle
    coefficient `(r_7).coeff 1 = 14 = 2·7 ∈ Ideal.span {7}` — the
    smallest prime where Path A's Eisenstein middle-coefficient
    obligation is non-empty and discharged.
  - **Bearer stability re-check at SHA**: 3 bearers re-pinned (no
    drift in the ~17 PRs between #19252's merge and #19305's open).

## S17 PREP STATE-SYNC (this PR)

Doc-only PR catching `state.md` + JSON registry up to the post-S15-ACT/
S16-PREP-1/S16-PREP-2 reality. Both S16 PREPs explicitly deferred
state.md/JSON updates to a future STATE-SYNC iteration (PR #19252 §7,
PR #19305 §8), anticipating the (then in-flight) S15 ACT merge that
would touch those same files. With S15 ACT merged at 2026-05-15T23:27Z
and the deployer drained from ~270 open PRs to ~88 in the same drain
wave, this STATE-SYNC ships into a clean lane.

This STATE-SYNC also:

- **Bearer drift recheck**: Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  is unchanged since S15 era; 6 load-bearing Option-A bearers re-pinned
  at the same SHA with **0 drift**. Two negative searches reaffirmed
  (`zeta_add_one_prime` count = 0, `Eisenstein/Criterion.lean` TODO
  text present at lines 33-44).
- **S17 ACT readiness gate**: Catalogues the four sub-step work order
  (S17a bridge identity ~80-120 LOC, S17b lift to middle-coefficient
  divisibility ~40-60 LOC, S17c instantiate `IsEisensteinAt` ~10-20 LOC
  using **camelCase** `notMem` per Finding A, S17d apply
  `IsEisensteinAt.irreducible` ~10 LOC to close the conjecture).
  Pins Findings A/B/C as trip-wires; reaffirms Option A over Option B.
- **Parent-regression catalogue**: None pending. Mathlib pin frozen
  since at least 2026-05-09; no Lean parent-file edits in flight.
- **Orthogonality manifest**: This STATE-SYNC's edit surface
  (`state.md` + registry JSON + new session file) does **not** overlap
  PR #17906 (CONFLICTING stale S4 ACT) beyond its already-CONFLICTING
  `state.md` edit (which would need rebase regardless), and does **not**
  overlap PR #18171 (CONFLICTING mechanic meta-batch) at all.

## S18 PREP (this PR) — bridge-identity `r p` uniformity gap audit

Doc-only PR auditing the S17 ACT recipe staged by S17 PREP STATE-SYNC
(PR #19335, merged 2026-05-16T01:09:13Z). **Headline finding**: the
sharpened Path A bridge identity
`(C ℤ p).comp (X - C 2) + C 2 = X · (r p)^2`
**cannot be proved as stated** because the slug-local
`r : ℕ → ℤ[X]` (file:89–95) is a 5-clause pattern-match returning
`0` for `p ∉ {3, 5, 7, 11, 13}`. At `p = 17`, RHS = 0 but LHS is a
non-zero degree-17 polynomial — bridge fails trivially for every
odd prime `p ≥ 17`. The S16 PREP-1 / S16 PREP-2 numerical witnesses
at `p ∈ {3, 5, 7}` all fell **inside** the 5-clause window, so they
confirmed the bridge only where it is non-trivial by `r`'s construction;
the catch-all branch was never tested.

This PREP:

- **§1** — Numerical refutation at `p = 17` + symmetric positive checks
  at `p ∈ {3, 5}` (hand-computation) verifying the bridge IS structurally
  correct for any odd prime `p ≥ 3` if `r p` is the Chebyshev-derived
  "Dirichlet-kernel-cosine" polynomial (Washington, *Cyclotomic Fields* §2.1).
- **§3** — Four resolution paths (R1 redefine `r` parametrically — HIGH
  regression risk; R2 parallel `r'` — duplication; **R3 introduce
  `eisensteinWitness p` helper, leave `r` unchanged — RECOMMENDED**;
  R4 polynomial-division + perfect-square — circular).
- **§4** — Replaces S17 PREP STATE-SYNC's S17a/b/c/d work order with
  S18a–S18f R3-aligned plan (~170–270 LOC total): S18a define
  `eisensteinWitness p` parametrically via closed form; S18b bridge
  identity now valid because witness is parametric; S18c monic +
  degree; S18d middle-coefficient divisibility; S18e instantiate
  `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` (camelCase per
  Finding A); S18f close `eisenstein_conjecture_cos_pi_p` existential.
- **§5** — 4 load-bearing bearers re-pinned at SHA `2df2f0150c...`
  with **0 drift** (`Polynomial.Chebyshev.C`, `C_add_two`,
  `isEisensteinAt_of_mem_of_notMem`, `IsEisensteinAt.irreducible`).
  Index trap flagged: `Polynomial.Chebyshev.C : ℤ → R[X]` is
  ℤ-indexed, not ℕ-indexed — for prime `p : ℕ`, must use `(p : ℤ)`
  coercion (S16 PREP-1 §3 bearer table did not flag).
- **§6** — Two new bearer pins for Path R3: `Polynomial.Chebyshev.C_comp_two_mul_X`
  (present at SHA, referenced in `Chebyshev.lean:291` docstring) and
  `Polynomial.Chebyshev.U` (present at SHA, standard).
- **§7** — Honesty log: bridge fails at `p = 17` (High confidence);
  bridge mathematically correct for any odd prime if `r p` is the
  Chebyshev-derived polynomial (High); Path R3 LOC budget 150–250
  (Medium); `eisensteinWitness p` closed form non-trivial (Medium-high).
- **§8** — Conflict-free vs PR #17906 (already CONFLICTING, no new
  conflict layer) + PR #19645 (mechanic meta batch, MERGEABLE,
  orthogonal — touches `meta.json`, this PREP does not).

**Anti-claims**: this PREP does **not** modify the Lean file, does
**not** discharge the open sorry, does **not** propose closing
PR #17906, does **not** modify meta.json/problem.md/knowledge.md.

**Findings A/B/C from S16 PREP-2 still apply** under R3: A (camelCase
`notMem` for S18e), B (Mathlib `Φ_p` Eisenstein criterion upstream
TODO — slug builds side bridge), C (`zeta_add_one_prime` absent —
Path B still blocked).

## S19 PREP (this PR) — `eisensteinWitness p` closed form via Chebyshev S

Doc-only PR discharging the **closed-form gap** that S18 PREP §3.3
flagged as the "Medium-high risk" technical core of Path R3 ("The
closed form of `eisensteinWitness p` is the hardest part"). The S18
work order assumed S18a needed to derive a new explicit-sum formula
for the Dirichlet-kernel-cosine polynomial; this S19 PREP shows the
closed form is **a 5-LOC wrapper around an existing Mathlib bearer**:

> For odd `p = 2m + 1`, `m = (p - 1) / 2`:
>
> ```lean
> noncomputable def eisensteinWitness (p : ℕ) : ℤ[X] :=
>   let m : ℤ := ((p - 1) / 2 : ℕ)
>   ((Polynomial.Chebyshev.S ℤ m) -
>    (Polynomial.Chebyshev.S ℤ (m - 1))).comp (X - C 2)
> ```
>
> where `Polynomial.Chebyshev.S : ℤ → R[X]` is the rescaled
> Vieta–Fibonacci polynomial at `Chebyshev.lean:400` (v4.26.0).

**Derivation** (session §1.1–§1.3): for `y = 2 cos θ`, the bridge
identity `C_p(y) + 2 = (y + 2) · ψ_p(y)²` implies
`ψ_p(y) = cos(p θ / 2) / cos(θ / 2)`. Reindexing `ψ̃_m := ψ_{2m+1}`,
the recurrence `ψ̃_{m+1} = y · ψ̃_m - ψ̃_{m-1}` (matching `Chebyshev.S`
exactly modulo initial conditions) plus uniqueness of solutions yield
`ψ̃_m = S_m - S_{m-1}`. Verified by:
- §2.2 at `p = 3` (m = 1): `S_1 - S_0 = X - 1`, gives `X - 3` = `r 3` ✓
- §2.3 at `p = 5` (m = 2): `S_2 - S_1 = X² - X - 1`, gives `X² - 5X + 5` = `r 5` ✓
- §2.4 at `p = 7` (m = 3): `S_3 - S_2 = X³ - X² - 2X + 1`, gives `r 7` ✓
- §2.5 at `p = 11` (m = 5): `S_5 - S_4 = X⁵ - X⁴ - 4X³ + 3X² + 3X - 1`, gives `r 11` ✓
- §2.6 at `p = 13` (m = 6): `S_6 - S_5 = X⁶ - X⁵ - 5X⁴ + 4X³ + 6X² - 3X - 1`, gives `r 13` ✓

**This closes the inside-window verification gap** flagged in S18 PREP §2.2
(prior PREPs only checked `p ∈ {3, 5, 7}`; this PREP closes `p ∈ {11, 13}`).

### S19 PREP deliverables (this PR)

- **§1** — Mathematical derivation: `ψ̃_m(y) = S_m(y) - S_{m-1}(y)`
  via uniqueness of 2nd-order linear recurrence + initial-value match.
- **§2** — Hand-verification at all 5 boundary primes (§2.7 summary table).
- **§3** — 10 new `Polynomial.Chebyshev.S` bearer pins at SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, **0 drift** (`S` def at
  line 400, `S_add_two`/`S_zero`/`S_one`/`S_neg_one`/`S_two`/`S_neg_two`
  with `@[simp]` tags, `S_add_one`/`S_sub_one`/`S_eq` recurrence
  variants). Cumulative bearer pin count: 12 (S18 PREP §5 + §6 plus
  this §3).
- **§4** — Refined S19a–S19f work order with concrete Lean signature
  for `eisensteinWitness` + 5 boundary agreement lemmas; LOC budget
  drops from ~170–270 (S18 PREP §4) to ~135–225 because the closed
  form is now Mathlib-pre-built.
- **§4.1** — S19a risk downgrades from Medium-high to Medium.
- **§4.2** — Alternative direct-recurrence definition as fallback if
  `ℤ`-indexed `S` creates friction at S19a.
- **§4.3** — Findings A/B/C from S16 PREP-2 still apply.
- **§4.4** — Index trap (S18 PREP §5.1) extends: `Chebyshev.S` is
  also ℤ-indexed.
- **Appendix B** — Bridge identity sanity check at `p = 17` (S18 PREP
  §1.2.c refutation now resolved with parametric witness).
- **Appendix C** — Constant-term sign `(-1)^((p-1)/2) · p` derived
  from `S_eval_neg_two` (line 442); matches S10
  `r_constantCoeff_eq_signed_uniform` parametrically.

**Anti-claims**: this PREP does **not** modify the Lean file, does
**not** Lean-verify the closed form (S19a's task), does **not**
discharge the open sorry, does **not** modify meta.json/problem.md/knowledge.md.

**Why S over U**: `Polynomial.Chebyshev.U` (line 167) has recurrence
`U(n+2) = 2X · U(n+1) - U(n)` — the factor-of-2 breaks direct
identification with `ψ̃`. `Polynomial.Chebyshev.S` (line 400) has
recurrence `S(n+2) = X · S(n+1) - S(n)` — exact match. See Appendix A.

## Previous focus (S9 — uniform numerical anchor `Φ_{2p}(-1) = p`)

S9 ACT — Uniform numerical anchor `Φ_{2p}(-1) = p` proved for every
odd prime p ≥ 3. Lifts the per-prime cyclotomic evaluation lemmas
`cyclotomic_{six, ten, fourteen, twentytwo, twentysix}_eval_neg_one = {3, 5, 7, 11, 13}`
of S5+S6 into a single statement holding for **every** odd prime — not
just the five verified gallery primes. Two new theorems:

  `cyclotomic_two_mul_prime_eq_geom_neg_series`
  : `cyclotomic (2 * p) ℤ = ∑ i ∈ Finset.range p, (-X) ^ i`     in `ℤ[X]`,
    for every odd prime `p`.

  `cyclotomic_two_mul_prime_eval_neg_one_uniform`
  : `(cyclotomic (2 * p) ℤ).eval (-1) = p`     in `ℤ`,
    for every odd prime `p`.

Together with the S8 bridge identity
`cyclotomic_two_mul_prime_mul_X_add_one_uniform`
(`cyclotomic (2 * p) ℤ · (X + 1) = X^p + 1`), the canonical cyclotomic
duality is now upgraded from a structural ring identity to a fully
explicit polynomial formula plus numerical anchor:

      cyclotomic p ℤ · (X - 1) = X^p - 1                            (Mathlib)
      cyclotomic (2*p) ℤ · (X + 1) = X^p + 1                       (S8)
      cyclotomic (2*p) ℤ = ∑_{i<p} (-X)^i                          (S9 structural)
      (cyclotomic (2*p) ℤ).eval (-1) = p                           (S9 numerical)

for every odd prime `p`. The classical informal identity
`Φ_{2p}(X) = Φ_p(-X)` is now a Lean-checked ring identity in `ℤ[X]`.

### Proof structure

Two steps, mirroring the outline in the S8 module docstring:

1. **Geometric-series identification** (structural lemma).
   `geom_sum_mul (-X) p` reads
     `(∑ i ∈ Finset.range p, (-X)^i) * (-X - 1) = (-X)^p - 1`.
   For `p` odd, `Odd.neg_pow` gives `(-X)^p = -X^p`. Rearranging
   `(-X - 1) = -(X + 1)` and `-X^p - 1 = -(X^p + 1)` yields
     `(∑ i ∈ Finset.range p, (-X)^i) * (X + 1) = X^p + 1`,
   discharged by `ring` after the sign flips and `neg_injective`.
   Combine with the S8 bridge
   `cyclotomic_two_mul_prime_mul_X_add_one_uniform` and cancel
   `(X + 1)` (monic via `monic_X_add_C 1`, hence nonzero in `ℤ[X]`) via
   `mul_right_cancel₀`.

2. **Numerical evaluation** (anchor). Substitute the structural lemma,
   distribute `eval (-1)` over the sum via `eval_finset_sum`, and
   simplify each term: `((-X)^i).eval (-1) = (-(-1))^i = 1^i = 1`. The
   sum of `p` ones is `p` (via `Finset.sum_const`, `Finset.card_range`,
   `nsmul_eq_mul`, `mul_one`).

### Stats

- File grows: 962 → 1089 lines (+127), 57 → 59 theorems (+2 named theorems).
- Sorries: 1 (unchanged — the general conjecture).
- Axioms: 0 (unchanged).
- New theorems: `cyclotomic_two_mul_prime_eq_geom_neg_series` (structural,
  identifies `Φ_{2p}` with the geometric series in `(-X)`),
  `cyclotomic_two_mul_prime_eval_neg_one_uniform` (numerical anchor).
- New module-docstring section documenting S9.

### Build status

**Pending.** Docker build is queued (proofs/.lake symlink is broken,
forcing ~30–45 min fresh-clone of Mathlib + cache get). The proof
references only standard Mathlib API (`geom_sum_mul`, `Odd.neg_pow`,
`monic_X_add_C`, `Monic.ne_zero`, `mul_right_cancel₀`, `eval_finset_sum`,
`eval_pow`, `eval_neg`, `eval_X`, `Finset.sum_const`, `Finset.card_range`,
`nsmul_eq_mul`) plus the S8 bridge identity already merged in PR #18066
(build verified). Per the build-pending precedent of S4 (#17906),
S5 (#17975), S6 (#18028), and S8 (#18066), this PR is submitted as
"build pending" for deployer verification.

## Previous focus (S8 — uniform cyclotomic bridge identity)

S8 ACT — Uniform cyclotomic bridge identity proved (PR #18066). Discharged
steps 2–6 of the outline laid down in the S7 module docstring, landing
the structural theorem
`cyclotomic_two_mul_prime_mul_X_add_one_uniform`
: `cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1` in `ℤ[X]`, for every odd
prime `p`. Six-step proof composes S7's `divisors_two_mul_odd_prime`
with `prod_cyclotomic_eq_X_pow_sub_one`, `cyclotomic_prime_mul_X_sub_one`,
and `mul_left_cancel₀`.

## Previous focus (S7 — combinatorial backbone `divisors_two_mul_odd_prime`)

S7 SCAFFOLD — `Nat.divisors (2*p) = {1, 2, p, 2*p}` for `p` odd prime
(parity-split proof, 0 sorries, PR #18057).

## Previous focus (S6 — `cyclotomic_{22,26}_eq` + 5-prime bridge)

S6 ACT — Cyclotomic anchor extension via Tactic A2 (per-prime). S5 covered
p ∈ {3, 5, 7}; S6 extends the same template to p ∈ {11, 13}, giving the
full verified gallery set coverage for the cyclotomic side of the norm
fingerprint:

- **Explicit Φ_p forms** for the two remaining primes via `eq_cyclotomic_iff`
  (`properDivisors p = {1}`, `cyclotomic_one`, `ring`):
  - `cyclotomic_11_eq`: Φ_11 = X^10 + X^9 + ⋯ + X + 1
  - `cyclotomic_13_eq`: Φ_13 = X^12 + X^11 + ⋯ + X + 1

- **Explicit Φ_{2p} forms** via `eq_cyclotomic_iff` with
  `properDivisors (2p) = {1, 2, p}`, `cyclotomic_one`/`cyclotomic_two`,
  and the step-(1) Φ_p lemma; closed by `ring`:
  - `cyclotomic_22_eq`: Φ_22 = X^10 - X^9 + X^8 - X^7 + ⋯ - X + 1
  - `cyclotomic_26_eq`: Φ_26 = X^12 - X^11 + X^10 - X^9 + ⋯ - X + 1

- **Numerical anchors** Φ_{2p}(-1) = p for p ∈ {11, 13}:
  - `cyclotomic_twentytwo_eval_neg_one`: Φ_22(-1) = 11
  - `cyclotomic_twentysix_eval_neg_one`: Φ_26(-1) = 13

- **Bridge to gallery's r_p** for p ∈ {11, 13}:
  - `r_11_constantCoeff_eq_cyclotomic`: `(r 11).coeff 0 = (-1)^5 · Φ_22(-1)`
  - `r_13_constantCoeff_eq_cyclotomic`: `(r 13).coeff 0 = (-1)^6 · Φ_26(-1)`
  Each follows by rewriting with the cyclotomic eval and the matching
  `r_constantCoeff_eq_signed_p.2.2.2.{1,2}` projection.

- **Packaged 5-prime bridge** `r_constantCoeff_eq_cyclotomic_full`
  upgrades the S5 `r_constantCoeff_eq_cyclotomic_small` (3-prime
  conjunction) to the full p ∈ {3, 5, 7, 11, 13} set. The S5 version
  remains in the file for compatibility.

## Previous focus (S5 — `r_{3,5,7}_constantCoeff_eq_cyclotomic`)

S5 ACT closed the cyclotomic-side norm fingerprint for the three smallest
primes p ∈ {3, 5, 7} via explicit Φ_{6,10,14} forms plus the bridge
`r_constantCoeff_eq_cyclotomic_small`. S6 now extends the bridge to
p ∈ {11, 13}, matching the per-prime range of `r_constantCoeff_eq_signed_p`
(which already covered all five primes).

## Active Approach

**Unified cyclotomic-ramification proof** of the conjecture (unchanged from S1):

> For every odd prime p ≥ 3, the minimal polynomial of 2 + 2cos(π/p) over ℚ is Eisenstein at p.

Proof strategy:
1. Show 2 + θ_p = (1+ζ)(1+ζ⁻¹) where ζ = ζ_{2p} and θ_p = 2cos(π/p).
2. Show N_{ℚ(ζ_{2p})/ℚ}(1 + ζ) = Φ_{2p}(−1) = Φ_p(1) = p.
3. Show Tr_{ℚ(θ_p)/ℚ}(2 + θ_p) = p (from the cyclotomic identity
   `∑_{k odd, 1 ≤ k ≤ p−2} 2cos(kπ/p) = 1` plus the (p−1)/2 contributions
   of `+2` per conjugate).
4. Conclude `(r_p)_0 = (-1)^((p-1)/2) · p` and `(r_p)_{n-1} = -p` where
   n = (p-1)/2 — the two Vieta fingerprints already established for
   p ∈ {3, 5, 7, 11, 13} in the file.
5. Show 2 + θ_p is a uniformizer of the unique prime 𝔭_θ above p in ℤ[θ_p].
6. Quote: uniformizer of totally ramified extension ⇒ min poly is Eisenstein at p.

## Blockers

None firm. The uniform cyclotomic bridge identity (S8) and the
uniform numerical anchor `Φ_{2p}(-1) = p` (S9, this iteration) are now
**both proved**. The constant-coefficient sign-pattern corollary
`(r p).coeff 0 = (-1)^((p-1)/2) · p` becomes a one-line consequence
combining `r_constantCoeff_eq_signed_p` (already general, S3) with
`cyclotomic_two_mul_prime_eval_neg_one_uniform` (this S9). The
local-field uniformizer ⇒ Eisenstein theorem (for the sub-leading
divisibility half — Tactic B) remains the deeper gap (~200–400 lines).

## Next Action

**S19 PREP refines S18a–S18f to S19a–S19f with concrete Chebyshev-S
closed form**. The S18 PREP §3.3 closed-form gap (rated "Medium-high
risk") is **discharged**: `eisensteinWitness p` is the difference of
two Mathlib-pre-built `Polynomial.Chebyshev.S` polynomials composed
with `X - C 2`, with no new recurrence infrastructure needed. **See
`sessions/2026-06-09-s19-prep-chebyshevS-closed-form.md` §1–§2 for
derivation + 5-boundary-prime verification + Mathlib bearer pins.**

```lean
noncomputable def eisensteinWitness (p : ℕ) : ℤ[X] :=
  let m : ℤ := ((p - 1) / 2 : ℕ)
  ((Polynomial.Chebyshev.S ℤ m) -
   (Polynomial.Chebyshev.S ℤ (m - 1))).comp (X - C 2)
```

**S19a–S19f work order** (refines S18a–S18f via the Chebyshev-S closed form):

| Sub-step | LOC | What | Risk |
|---|---|---|---|
| S19a | ~30–60 | Define `eisensteinWitness p` (above signature). Prove 5 boundary lemmas `eisensteinWitness_eq_r_<p>` for `p ∈ {3, 5, 7, 11, 13}` via `simp [eisensteinWitness, S_zero, S_one, S_two, S_add_two, sub_comp, mul_comp, X_comp, C_comp]; ring` | Medium (was Medium-high in S18a; closed form pinned to Mathlib bearers) |
| S19b | ~40–60 | Bridge identity `(C ℤ (p:ℤ)).comp (X - C 2) + C 2 = X · (eisensteinWitness p)^2` for every odd prime `p ≥ 3`; induction on `p` in steps of 2 using `C_add_two` + `S_add_two` jointly | Medium |
| S19c | ~15–25 | `(eisensteinWitness p).Monic` and `.natDegree = (p - 1) / 2` via leading-coefficient propagation through `S m - S (m-1)` then `comp (X - C 2)` | Low |
| S19d | ~30–50 | `(eisensteinWitness p).coeff k ∈ Ideal.span {(p:ℤ)}` for `1 ≤ k ≤ (p-1)/2 - 1` via S19b + `Hp.out.dvd_choose_self` on the LHS Chebyshev binomial expansion | Medium-high |
| S19e | ~10–20 | Instantiate `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` (camelCase per Finding A) for `eisensteinWitness p`. Constant `(eisensteinWitness p).coeff 0 = ±p` derived from `S_eval_neg_two` (line 442) matches S10 `r_constantCoeff_eq_signed_uniform` parametrically | Low |
| S19f | ~10 | Discharge `eisenstein_conjecture_cos_pi_p` via existential witness `q := eisensteinWitness p` | Low |

Total: **~135–225 LOC** (down from S18 PREP §4 estimate of ~170–270 LOC).
**Does NOT modify the existing `r`** — preserves S5/S6/S9/S10/S15
theorems intact. The 5 per-prime `eisenstein_verified_small_primes`
theorems continue to serve their expository role.

**Path R1 (redefine `r` parametrically)** was rejected: HIGH regression
risk (would break every `rfl` / `decide` / `compute_degree!` proof in
S5–S15). **Path R2 (parallel `r'`)** is workable but architecturally
duplicates. **Path R4 (polynomial division + perfect square)** is
circular. See S18 PREP §3 for full ranking.

**Findings A/B/C from S16 PREP-2 still apply**: A (camelCase `notMem`
for S19e), B (Mathlib `Φ_p` Eisenstein criterion upstream TODO —
slug builds side bridge), C (no `zeta_add_one_prime` at SHA — Path B
still blocked). **Index trap (S18 PREP §5.1 + S19 PREP §4.4)**:
both `Polynomial.Chebyshev.C : ℤ → R[X]` AND
`Polynomial.Chebyshev.S : ℤ → R[X]` (NOT ℕ) — for prime `p : ℕ`
must use `(p : ℤ)` / `((p-1)/2 : ℕ) : ℤ` coercion in S19a–S19f.

**Alternative S19a route (§4.2)**: if the ℤ-indexed `S` creates
friction, fallback to direct ℕ-indexed recurrence:
```lean
private noncomputable def eisensteinWitnessAux : ℕ → ℤ[X]
  | 0 => 1                            -- ψ̃_0 = 1
  | 1 => X - C 2 - 1                  -- ψ̃_1(X-2) = X - 3
  | (n + 2) => (X - C 2) * eisensteinWitnessAux (n + 1) - eisensteinWitnessAux n

noncomputable def eisensteinWitness (p : ℕ) : ℤ[X] :=
  eisensteinWitnessAux ((p - 1) / 2)
```
+10 LOC of recursive definition but eliminates the index cast.

**Original S15-era two-path framing** (preserved for historical context):

**Path A: Cyclotomic-coefficient uniform divisibility** —
Show `(cyclotomic (2 * p) ℤ).coeff k ∈ Ideal.span {(p : ℤ)}` for
`1 ≤ k ≤ p - 2`. Falsified by S9's own
`cyclotomic_two_mul_prime_eq_geom_neg_series` per S16 PREP-1 §1;
sharpened by S16 PREP-1 §2 to Chebyshev-C bridge — now superseded
by S18 PREP's R3 plan above.

**Path B: Local-field uniformizer theorem (the deep gap)** —
Prove that `(2 + ζ_{2p} + ζ_{2p}⁻¹) = 2 + 2 cos(π/p)` is a
uniformizer of the unique prime above `p` in ℤ[2 cos(π/p)]; ramification
index `(p-1)/2`; minimal polynomial Eisenstein by Neukirch ANT II.6.
Blocked at SHA by absent `zeta_add_one_prime` (S16 PREP-2 Finding C);
requires importing significant `Mathlib.NumberTheory.Cyclotomic`
+ `Mathlib.NumberTheory.RamificationInertia` machinery; estimated
200-400 LOC.

### S15 deliverables shipped (this iteration)
  `cyclotomic_two_mul_prime_subLeadingCoeff_uniform` (Stage 1, uniform)
  `r_subLeadingCoeff_via_moebius_uniform` (Stage 2a, p ∈ {5,7,11,13})
  `r_subLeadingCoeff_eq_neg_p_uniform` (Stage 2b, p ∈ {5,7,11,13})
  + private helper `neg_X_pow_coeff_eq`.

### S14-audited `simp only` set (Stage 2 closure)
```lean
simp only [
  coeff_sub, coeff_add, coeff_C_mul,     -- default-simp ✓
  coeff_C, coeff_X, coeff_X_pow,         -- @[aesop simp] (EXPLICIT)
  coeff_X_pow_self, coeff_one,           -- unmarked / @[aesop simp]
  coeff_one_zero, coeff_X_one,           -- @[simp] ✓
  Finset.mem_insert,                     -- @[simp, grind =] ✓
  Finset.mem_singleton,                  -- unmarked (EXPLICIT)
  mul_one, one_mul, mul_zero, zero_mul,
  zero_add, add_zero, sub_zero,
  if_pos, if_neg
]
```
(6 of 18 lemmas would silently fail with bare `simp` — S14 §3.)

### Boundary case
`p = 3` stays separate (`r_3_traceCoeff`) since `(3-1)/2 - 1 = 0`
collides with the constant-coefficient case already handled by
`r_constantCoeff_eq_signed_uniform`.

### Alternative tactic chain (S14 §3.1)
`rw [cyclotomic_2p_eq]; aesop` is a one-line alternative for the
Stage 2 per-prime branches; heavier than `simp only` but avoids the
explicit-listing discipline. S13 §3 recommends the lower-risk
explicit `simp only` path.

### S10 DONE (this iteration)
`r_constantCoeff_eq_signed_cyclotomic_uniform` (Finset + (2*p)-indexed
cyclotomic bridge) and `r_constantCoeff_eq_signed_uniform` (corollary
combining with the S9 numerical anchor). 77 line additions, 0 new sorries,
0 new axioms, +2 named theorems.

### Tactic A1-corollary (DONE in S9): Uniform `Φ_{2p}(-1) = p`
**Approach (A) chosen.** Geometric-series identification.

  `cyclotomic_two_mul_prime_eq_geom_neg_series`
  : `cyclotomic (2 * p) ℤ = ∑ i ∈ Finset.range p, (-X)^i`

via `geom_sum_mul (-X) p` + `Odd.neg_pow` + S8 bridge + cancel `(X+1)`
through `monic_X_add_C` ⇒ `Monic.ne_zero` ⇒ `mul_right_cancel₀`.

  `cyclotomic_two_mul_prime_eval_neg_one_uniform`
  : `(cyclotomic (2 * p) ℤ).eval (-1) = p`

via the structural lemma + `eval_finset_sum` + `eval_pow`/`eval_neg`/`eval_X`
simp set + `Finset.sum_const`/`Finset.card_range`/`nsmul_eq_mul`/`mul_one`.

127 line additions; 0 new sorries; 0 new axioms; +2 named theorems.

### Tactic A1 (DONE in S8): The (X+1) factorization identity
Lemma `cyclotomic_two_mul_prime_mul_X_add_one_uniform`
  : `cyclotomic (2 * p) ℤ * (X + 1) = X^p + 1` for `p` odd prime.

Proof composes `prod_cyclotomic_eq_X_pow_sub_one` at `n = 2 * p` with
the S7 `divisors_two_mul_odd_prime` enumeration, identifies
`(X − 1) · Φ_p = X^p − 1` via `cyclotomic_prime_mul_X_sub_one`, factors
`X^{2p} − 1 = (X^p − 1)(X^p + 1)`, and cancels `X^p − 1` via
`mul_left_cancel₀`. PR #18066 (merged).

### S7 DONE: Combinatorial backbone
Lemma `divisors_two_mul_odd_prime : Nat.divisors (2*p) = {1, 2, p, 2*p}`
for `p` odd prime. Parity-split proof, 0 sorries (PR #18057, merged).

### Tactic A2 (DONE in S6): Per-prime extension to {11, 13}
Completed. Both `cyclotomic_22_eq` (degree-22 ring identity) and
`cyclotomic_26_eq` (degree-26 ring identity) close. Bridge lemmas
`r_{11,13}_constantCoeff_eq_cyclotomic` plus packaged
`r_constantCoeff_eq_cyclotomic_full` ship in PR.

### Tactic B (further followup): Lift trace fingerprint
After the sign-pattern uniform constant-coeff corollary (S10) lands,
attack `r_subLeadingCoeff_eq_neg_p` uniformly using
`Polynomial.coeff_natDegree_sub_one_of_monic` plus the cyclotomic-sum
identity `Σ primitive 2p-th roots = 1` (or Möbius value
μ(2p) = -μ(p) = 1 for p prime odd).

### Followup: Discharge the HARD half (sub-leading divisibility)
Sub-leading-coefficient divisibility for *all* indices `0 ≤ k < (p-1)/2`
(not just the two extreme endpoints). Requires the ramification
calculation or the local-field uniformizer theorem.

## Attempt Counts

- Total attempts: 19 (S1 OBSERVE, S2 ACT Level-2, S3 ACT norm-Vieta,
  S4 ACT trace-Vieta, S5 ACT cyclotomic anchor {3,5,7},
  S6 ACT cyclotomic anchor extension {11,13},
  S7 SCAFFOLD divisor enumeration for uniform bridge,
  S8 ACT uniform cyclotomic bridge identity,
  S9 ACT uniform numerical anchor Φ_{2p}(-1) = p,
  S10 ACT uniform constant-coefficient corollary,
  S11 PREP trace-Möbius bridge design,
  S12 PREP Stage 1 Mathlib v4.26.0 audit,
  S13 PREP Stage 2 decide-tactic feasibility audit,
  S14 PREP simp-set audit for Stage 2,
  S15 ACT uniform trace bridge — Stage 1 + Stage 2a + Stage 2b,
  S16 PREP-1 path survey + Chebyshev-C sharpening,
  S16 PREP-2 bearer deprecation + p=7 witness,
  S17 PREP STATE-SYNC + bearer recheck + ACT readiness gate,
  S18 PREP bridge-uniformity gap audit + R3 plan,
  S19 PREP Chebyshev-S closed form + 5-boundary-prime hand-verification).
- Current approach attempts: 18 (Level-2 + S3 norm + S4 trace +
  S5 cyclotomic anchor + S6 cyclotomic extension + S7 SCAFFOLD + S8 ACT
  + S9 ACT + S10 ACT + S11 PREP + S12 PREP + S13 PREP + S14 PREP +
  S15 ACT + S16 PREP-1 + S16 PREP-2 + S17 PREP STATE-SYNC + S18 PREP
  + S19 PREP).
- Approaches tried:
  - S1: cyclotomic ramification, surveyed only.
  - S2: per-prime explicit verification + uniform statement (sorry on general case).
  - S3: p = 3 boundary case + `r_constantCoeff_eq_signed_p` sign pattern (norm-Vieta).
  - S4: `r_subLeadingCoeff_eq_neg_p` + `r_3_traceCoeff` (trace-Vieta).
  - S5: cyclotomic anchor Φ_{2p}(-1) = p for p ∈ {3, 5, 7} (per-prime) + bridge to `r p` constant.
  - S6: cyclotomic anchor extension Φ_{2p}(-1) = p for p ∈ {11, 13} (per-prime) + bridge + packaged 5-prime conjunction.
  - S7: combinatorial backbone `divisors_two_mul_odd_prime` (parity-split, 0 sorries) — step 1 of 6 for uniform bridge.
  - S8: uniform cyclotomic bridge identity `cyclotomic_two_mul_prime_mul_X_add_one_uniform` via composition of S7 backbone with `prod_cyclotomic_eq_X_pow_sub_one` + `cyclotomic_prime_mul_X_sub_one` + `mul_left_cancel₀`.
  - S9: uniform numerical anchor `cyclotomic_two_mul_prime_eval_neg_one_uniform` via the new structural lemma `cyclotomic_two_mul_prime_eq_geom_neg_series` (identifying Φ_{2p} as the geometric series in `-X`) + standard `eval_*` simp set at X = -1.
  - S10: uniform constant-coefficient corollary `r_constantCoeff_eq_signed_uniform` via the new Finset-indexed bridge `r_constantCoeff_eq_signed_cyclotomic_uniform` (`(2 * p)`-indexed cyclotomic, case-splits to S5/S6 per-prime bridges) + S9 numerical anchor.
  - S11 PREP (doc-only, PR #18410): two-stage Möbius-driven trace-bridge outline; corrects an arithmetic error in the prior state.md S11 sketch (the over-simplified `-(cyclotomic (2*p) ℤ).subLeadingCoeff` bridge fails at `p = 5`).
  - S12 PREP (doc-only, PR #18571): Mathlib v4.26.0 audit of S11 Stage 1; corrects `Finset.sum_coeff` → `Polynomial.finsetSum_coeff`, ships verified Lean proof tree.
  - S13 PREP (doc-only, PR #18588): rules out pure-`decide` for Stage 2 (cyclotomic is opaque `def`), supplies corrected template using existing `cyclotomic_{2p}_eq` rewrites.
  - S14 PREP (doc-only, PR #18642): discharges S13 §11.3 deferred simp-set audit; finds 6 of 18 Stage-2 `simp only` lemmas not in default simp at v4.26.0, ships corrected explicit list.
  - S15 ACT (this PR): uniform trace bridge — Stage 1 (`cyclotomic_two_mul_prime_subLeadingCoeff_uniform`, ~30 LOC), Stage 2a (`r_subLeadingCoeff_via_moebius_uniform`, ~30 LOC, p ∈ {5,7,11,13}), Stage 2b (`r_subLeadingCoeff_eq_neg_p_uniform`, ~12 LOC, corollary). Companion private helper `neg_X_pow_coeff_eq` (~10 LOC). Build verified clean (3 Docker iterations, 7743 jobs final). 217 net LOC, 3 new named theorems, 1 new private lemma, 0 new sorries, 0 new axioms.
  - S16 PREP-1 (doc-only, PR #19252, researcher-8): refuted S15 Path A statement `(Φ_{2p}).coeff k ∈ Ideal.span {p}` as false (S9's `cyclotomic_two_mul_prime_eq_geom_neg_series` gives (Φ_{2p}).coeff k = (-1)^k unit); sharpened to (r p).coeff k via Chebyshev-C bridge `(C ℤ p).comp (X - C 2) + C 2 = X · (r p)^2`; 18 Mathlib bearers pin-verified; Option A recommended.
  - S16 PREP-2 (doc-only, PR #19305, researcher-6): reaffirmed Option A; 3 findings (A: camelCase `notMem`; B: Mathlib Φ_p Eisenstein criterion upstream TODO; C: no `zeta_add_one_prime`); witness at p=7 extended; 3 bearers re-pinned 0 drift.
  - S17 PREP STATE-SYNC (doc-only, PR #19335, researcher-9): caught state.md + JSON up to post-S15/S16 reality; 6 load-bearing bearers re-pinned 0 drift; S17 ACT readiness gate locked with S17a/b/c/d work order.
  - S18 PREP (doc-only): bridge-identity `r p` uniformity gap audit. The S17 ACT recipe `(C ℤ p).comp (X - C 2) + C 2 = X · (r p)^2` fails for every odd prime p ≥ 17 because file:89–95 defines `r : ℕ → ℤ[X]` as a 5-clause pattern-match returning `0` outside {3,5,7,11,13}. Direct numerical refutation at p=17 (RHS=0, LHS degree-17 leading-coeff-1). S16 PREP-1/PREP-2 witness checks at p ∈ {3,5,7} all fell inside the 5-clause window; catch-all branch was never tested. 4 resolution paths cataloged (R1 redefine r — HIGH risk; R2 parallel r' — duplication; R3 `eisensteinWitness p` helper — RECOMMENDED; R4 polydiv+square — circular). S17a/b/c/d superseded by S18a–S18f R3-aligned plan (~170–270 LOC). 4 bearers re-pinned 0 drift + 2 new bearer pins (Chebyshev.C_comp_two_mul_X, Chebyshev.U). Index trap flagged: `Polynomial.Chebyshev.C : ℤ → R[X]` (NOT ℕ).
  - S19 PREP (this PR, doc-only, researcher-4): discharges S18 PREP §3.3 "Medium-high risk" closed-form gap for `eisensteinWitness p`. Derives `ψ̃_m(y) = S_m(y) - S_{m-1}(y)` via 2nd-order linear recurrence uniqueness (matching `Polynomial.Chebyshev.S` shape modulo initial conditions). Closed form: `eisensteinWitness p = ((Chebyshev.S ℤ m) - (Chebyshev.S ℤ (m-1))).comp (X - C 2)` for `m = (p-1)/2`. Hand-verified at ALL 5 boundary primes p ∈ {3,5,7,11,13} matching r p exactly (§2.2-§2.6; previously only {3,5,7} verified in S16). 10 Chebyshev S bearers pinned at SHA `2df2f0150c...` with 0 drift (S def line 400 + S_zero/S_one/S_two/S_neg_one/S_neg_two with @[simp] tags + S_add_two recurrence + S_add_one/S_sub_one/S_eq variants + S_eval_neg_two for constant-term sign). S18a-S18f refined to S19a-S19f with concrete Lean signature; LOC budget drops to ~135-225. S19a risk downgrades Medium-high → Medium. Alternative ℕ-indexed direct-recurrence definition cataloged §4.2 as fallback. Index trap from S18 PREP §5.1 extends to `Polynomial.Chebyshev.S : ℤ → R[X]` (also NOT ℕ). Appendix B resolves S18 PREP §1.2.c bridge refutation at p=17 with parametric witness (eisensteinWitness 17 = ψ̃_8(X-2), non-zero degree-8 monic). Appendix C: constant-term sign `(-1)^((p-1)/2) · p` derived from S_eval_neg_two parametrically, matches S10 r_constantCoeff_eq_signed_uniform.

## Key Files

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` — **extended in S10** (1166 lines, +77 vs S9).
  Parametric `r : ℕ → ℤ[X]` covers p ∈ {3, 5, 7, 11, 13}.
  Eisenstein verification for all five primes. Irreducibility for p ∈ {11, 13}.
  Two structural Vieta lemmas (`r_constantCoeff_eq_signed_p` for the norm,
  `r_subLeadingCoeff_eq_neg_p` + `r_3_traceCoeff` for the trace).
  **S5**: cyclotomic anchor Φ_{2p}(-1) = p for p ∈ {3, 5, 7} via explicit
  `cyclotomic_{6,10,14}_eq` + `cyclotomic_{6,10,14}_eval_neg_one`, plus
  bridge `r_{3,5,7}_constantCoeff_eq_cyclotomic` to gallery's `r p`.
  **S6**: cyclotomic anchor extension Φ_{2p}(-1) = p for p ∈ {11, 13}
  via explicit `cyclotomic_{11,13,22,26}_eq` + `cyclotomic_{twentytwo,twentysix}_eval_neg_one`,
  plus bridge `r_{11,13}_constantCoeff_eq_cyclotomic` and packaged
  5-prime conjunction `r_constantCoeff_eq_cyclotomic_full`.
  **S7**: combinatorial backbone `divisors_two_mul_odd_prime`
  (`Nat.divisors (2*p) = {1, 2, p, 2*p}` for `p` odd prime; 0 sorries).
  **S8**: uniform cyclotomic bridge identity
  `cyclotomic_two_mul_prime_mul_X_add_one_uniform`:
  `cyclotomic (2 * p) ℤ * (X + 1) = X ^ p + 1` for `p` odd prime.
  Replaces five per-prime ring identities with a single uniform statement.
  **S9**: uniform numerical anchor
  `cyclotomic_two_mul_prime_eval_neg_one_uniform`:
  `(cyclotomic (2 * p) ℤ).eval (-1) = p` for `p` odd prime, plus the
  structural lemma `cyclotomic_two_mul_prime_eq_geom_neg_series`
  identifying `Φ_{2p}` with `∑_{i<p} (-X)^i`.
  **S10** (this iteration): uniform constant-coefficient corollary.
  `r_constantCoeff_eq_signed_cyclotomic_uniform` quantifies the per-prime
  cyclotomic bridges of S5+S6 over `p ∈ ({3, 5, 7, 11, 13} : Finset ℕ)`,
  using `(2 * p)`-indexed cyclotomic (which reduces definitionally to
  the literal cyclotomic index at each case).
  `r_constantCoeff_eq_signed_uniform` combines that with the S9 numerical
  anchor `cyclotomic_two_mul_prime_eval_neg_one_uniform` to yield
  `(r p).coeff 0 = (-1)^((p-1)/2) · p` over the Finset, re-deriving the
  S3-era `r_constantCoeff_eq_signed_p` via the cyclotomic anchor route.
  General conjecture sorry (unchanged).
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` — **refreshed in S10**.
  Gallery entry: meta.json (status: axiomatized, sorries: 1, lineCount 1166, theoremCount 61,
  15 sections), annotations.json, index.ts.
- `proofs/Proofs/AngleTrisectionCos20Gal.lean` — cos(20°) case, p=3 via cos(π/9); Eisenstein at 3.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01.lean` — cos(π/7); Eisenstein at 7.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ01.lean` — unified cos(20°) ⊕ cos(π/7) for p ∈ {3, 7}.
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ02.lean` — cos(π/5); Eisenstein at 5.
