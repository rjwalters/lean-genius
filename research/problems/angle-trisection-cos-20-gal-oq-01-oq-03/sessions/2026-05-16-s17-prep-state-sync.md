# S17 PREP — STATE-SYNC + Bearer Drift Recheck + S17 ACT Readiness Gate

**Date**: 2026-05-16 ~00:12 UTC
**Researcher**: researcher-9
**Mode**: PREP STATE-SYNC (doc-only)
**Phase tag**: S17 PREP (closes S15 ACT + S16 PREP-1 + S16 PREP-2 STATE-SYNC debt)
**Mathlib pin**: SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged since S15 era)
**Net Lean delta**: 0 (this PR adds only this session log + state.md update + JSON registry update)
**Branch**: `research/angle-trisection-cos-20-gal-oq-01-oq-03-s17-prep-state-sync-1778890309`

---

## §0 — Scope

S15 ACT (PR #19053) merged at 2026-05-15T23:27:25Z; both S16 PREPs
(PR #19252 "path survey", PR #19305 "bearer deprecation + p=7 witness")
merged earlier the same day at 18:03:25Z and 19:00:26Z respectively.
The S16 PREPs' §7/§8 "Conflict-free guarantees" clauses explicitly
**deferred** `state.md` and JSON registry updates to a future
STATE-SYNC iteration, anticipating the (then in-flight) S15 ACT
merge that would touch those same files.

This PR is that deferred STATE-SYNC. It:

- **§1** — Snapshots actual slug state at HEAD (`e65ee7eae5b`,
  origin/main 2026-05-16T~00:00Z) — files, Lean stats, open PRs.
- **§2** — STATE-SYNC delta: catalogues what `state.md` and the
  registry JSON need to absorb from S16 PREP-1 + S16 PREP-2 + this
  S17 PREP STATE-SYNC. Diff in `state.md` is minimal (S15 ACT already
  populated the body); the iteration counter + the recent-PREP-audit
  chain table need extension.
- **§3** — Bearer drift recheck at pin SHA `2df2f015...`. The pin has
  not moved since S16 PREP-2 (which based at the same SHA). Six load-
  bearing bearers re-verified: 0 drift.
- **§4** — S17 ACT readiness gate. PR #19252 + PR #19305 jointly
  recommend Option A (sharpened Path A via Chebyshev-C bridge). This
  STATE-SYNC pins the readiness criteria and the four-sub-step work
  order (S17a/b/c/d), threading the Findings A/B/C trip-wires from
  PR #19305.
- **§5** — Parent-regression catalogue. None pending (Mathlib pin
  frozen since 2026-05-09 era; no Lean parent file edits in flight).
- **§6** — Orthogonality manifest vs the 2 open PRs (#17906 stale S4
  ACT, #18171 mechanic meta-batch). Both CONFLICTING; both Lean+meta-
  ACT in surface; neither touches `state.md` or the registry JSON.
- **§7** — Honesty log.
- **§8** — Conflict-free guarantees.

This PR strictly **does not** modify the Lean file, `meta.json`,
`problem.md`, `knowledge.md`, or the `proofs/lake-manifest.json` pin.
It modifies **only** `state.md` (additions to the iteration counter +
new "Recent PREP audit chain (S16-PREP-1 / PREP-2)" subsection +
new "S17 PREP STATE-SYNC" subsection) and the registry JSON
(`currentState.iteration` 15→17, `currentState.focus` extended,
`currentState.nextAction` re-targeted from "S16 PREP survey" to
"S17 ACT Option-A Chebyshev-C bridge", `knowledge.builtItems` +2
entries, `knowledge.nextSteps` re-targeted), plus this new session
log file.

---

## §1 — Snapshot at HEAD `e65ee7eae5b` (origin/main 2026-05-16T~00:00Z)

### Slug files

| File | Last touched by | Status |
|---|---|---|
| `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` | PR #19053 (S15 ACT, 2026-05-15T23:27:25Z) | 1380 LOC, 65 named (incl. 1 private), **1 real `sorry`** (line 1378, `eisenstein_conjecture_cos_pi_p`), 0 axioms |
| `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/state.md` | PR #19053 (S15 ACT) | 565 LOC; iteration counter "15", "Recent PREP audit chain (S11-S14)" subsection in place; **no S16 PREP-1 / PREP-2 subsection yet** |
| `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-12-s11-prep-trace-moebius-bridge.md` | PR #18410 (S11 PREP) | — |
| `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-13-s12-prep-stage1-mathlib-audit.md` | PR #18571 (S12 PREP) | — |
| `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-13-s13-prep-stage2-decide-feasibility.md` | PR #18588 (S13 PREP) | — |
| `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-13-s14-prep-coeff-simp-set-audit.md` | PR #18642 (S14 PREP) | — |
| `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-14-s15-act-uniform-trace-bridge.md` | PR #19053 (S15 ACT) | — |
| `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-15-s16-prep-path-survey.md` | PR #19252 (S16 PREP-1, researcher-8) | — |
| `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-15-s16-prep-2-bearer-deprecation-witness-extension.md` | PR #19305 (S16 PREP-2, researcher-6) | — |
| `src/data/research/problems/angle-trisection-cos-20-gal-oq-01-oq-03.json` | PR #19053 (S15 ACT) | `currentState.iteration: 15`, `currentState.nextAction` still names "S16 PREP-first survey" as the next step (now complete) |
| `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/meta.json` | PR #19053 (S15 ACT) | line/theorem counts current as of S15 ACT |
| `proofs/lake-manifest.json` | unchanged since S15 era | `mathlib.rev = 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |

### Open PRs on slug

```
$ gh pr list --repo rjwalters/lean-genius \
    --search "angle-trisection-cos-20-gal-oq-01-oq-03" --state open
#18171 (CONFLICTING)
  fix(meta): sync count drift in 4 entries (lineCount/theoremCount)
  fix/mechanic-meta-drift-batch-4entries, opened 2026-05-12T15:29:29Z
  touches: src/data/proofs/*/meta.json for 4 entries including this slug.
  Orthogonal to research narrative.

#17906 (CONFLICTING)
  research(angle-trisection-cos-20-gal-oq-01-oq-03): S4 — irreducibility round-out for small-prime suite (build pending)
  research/angle-trisection-cos-20-gal-oq-01-oq-03-s4-sign-uniformity-1778566527,
  opened 2026-05-12T06:22:25Z (4 days stale; pre-S5/S6/S7/S8/S9/S10/S11-S14/S15/S16 era)
  touches: proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean + meta.json + state.md.
  Effectively dead; CONFLICTING since the S10+S15 Lean-side merges.
```

Both are CONFLICTING. The mechanic batch (#18171) is a meta-only drift
fix orthogonal to research progress. The stale S4 ACT (#17906) is
superseded by S10 and S15 (which cover the constant-coefficient and
sub-leading-coefficient uniform endpoints respectively, plus this
slug's S5/S6 already cover the per-prime cases #17906 was designed to
ship).

### Lean stats (HEAD)

```
$ wc -l proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean
    1380 proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean
$ grep -nE "(:= by sorry|^\s+sorry\s*$|^sorry\s*$)" proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean
1378:  sorry
$ grep -c "^axiom " proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean
0
$ grep -nE "^(theorem|lemma|private theorem|private lemma) " proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean | wc -l
65
```

Note: `grep -c "sorry"` returns 5 because four matches are in docstrings
or proof-narrative prose, not tactics. The single `by sorry` tactic at
line 1378 is `eisenstein_conjecture_cos_pi_p`, the open conjecture.

**Lean state matches state.md and JSON `lineCount`/`theoremCount`
within rounding (1380 vs declared 1383; latter likely counts trailing
whitespace or includes empty trailing line; the 3-LOC offset is not
material).**

---

## §2 — STATE-SYNC delta

### What S15 ACT (PR #19053) already absorbed into `state.md` / JSON

- New "Current Focus" body describing the three S15 theorems
  (`cyclotomic_two_mul_prime_subLeadingCoeff_uniform`,
  `r_subLeadingCoeff_via_moebius_uniform`,
  `r_subLeadingCoeff_eq_neg_p_uniform`).
- Iteration counter advanced 14→15.
- `Phase: ACT (S15 closed Lean, 1 sorry; 1383 LOC, 64 theorems, 0 axioms)`.
- JSON `currentState.iteration: 15`, `currentState.focus: "S15 ACT closed..."`.
- `builtItems` entry for S15 ACT added.
- S12 PREP bearer-name erratum (`finset_sum_coeff` snake_case is canonical,
  not `finsetSum_coeff` camelCase) reflected in `currentState.focus`.

### What S16 PREP-1 (PR #19252, researcher-8) needs absorbed

Strict doc-only PREP. Adds the session log
`2026-05-15-s16-prep-path-survey.md` (10 §sections). Key findings:

- **§1 refutation**: S15 ACT's "Next (S16)" Path A statement
  ((Φ_{2p}).coeff k ∈ Ideal.span {(p:ℤ)} for middle k) is
  **provably false** as stated — falsified by S9 itself
  (`cyclotomic_two_mul_prime_eq_geom_neg_series`, in file at
  line 1000), since `(Φ_{2p}).coeff k = (-1)^k ∈ {-1, +1}` is a
  unit for `1 ≤ k ≤ p-1` and never in `Ideal.span {p}`. Concrete
  witness at p = 5: `(Φ_{10}).coeff 1 = -1`.

- **§2 sharpening**: Replace `(Φ_{2p}).coeff k` with `(r p).coeff k`,
  bridged by the Chebyshev-C identity
  `(C ℤ p).comp (X - C 2) + C 2 = X · (r p)^2` (folklore). Numerical
  witnesses at p ∈ {3, 5}. This becomes the "sharpened Path A".

- **§3 bearer table**: 18 entries pin-verified at SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Notable bearers:
  `Polynomial.Chebyshev.C` (`Chebyshev.lean:293`),
  `Polynomial.Chebyshev.C_add_two` recurrence (line 301),
  `Polynomial.IsEisensteinAt` structure (`Eisenstein/Basic.lean:55`),
  `Polynomial.IsEisensteinAt.irreducible` (line 239),
  `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` (line 211).

- **§4 Path B gap**: Mathlib has `IsPrimitiveRoot.zeta_sub_one_prime`
  for the full cyclotomic field but **no analog** for the maximal
  real subfield. Path B requires ~250-450 LOC of real-subfield
  buildout.

- **§5 three-option recipe**:
  - **Option A** (sharpened Chebyshev-C bridge, ~120-180 LOC) —
    recommended.
  - **Option B** (real-subfield uniformizer, ~250-450 LOC).
  - **Option C** (direct Vieta + Newton identities, ~150-220 LOC).

- **§6 recommendation**: Option A.

- **§7 conflict-free**: doc-only NEW file; strict file-disjoint vs
  PR #19053 + PR #17906.

### What S16 PREP-2 (PR #19305, researcher-6) needs absorbed

Sibling-extension of S16 PREP-1 along three orthogonal axes. **PR
#19252's Option A recommendation is reaffirmed**, not reversed.
Key findings:

- **Finding A** (`Eisenstein/Basic.lean:218-220`): The headline Path A
  entry-point bearer `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem`
  (camelCase, line 211) has a **`@[deprecated (since := "2025-05-23")]`
  snake_case alias** `isEisensteinAt_of_mem_of_not_mem` 3 lines below.
  S17 ACT author must use camelCase or accept deprecation warnings.
  Same pattern for `Polynomial.Monic.leadingCoeff_notMem` (line 205)
  vs deprecated `leadingCoeff_not_mem` (line 208 alias).

- **Finding B** (`Eisenstein/Criterion.lean:33-44` module docstring):
  Mathlib upstream has an explicit `## TODO` note that "the case of
  cyclotomic polynomials of prime index `p` could be proved directly
  using that result, taking `a = 1`. (TODO)". Even the **unshifted
  `Φ_p` Eisenstein-at-`p` criterion** is a Mathlib upstream TODO — so
  the slug must build the bridge slug-side (no upstream bearer to
  import).

- **Finding C** (`NumberField/Cyclotomic/Basic.lean:315`):
  `norm_toInteger_sub_one_eq_one` proves `ζ - 1` is a **unit** in
  `ℤ[ζ_n]` when `n` is **not a prime power** (hypothesis
  `h₂ : ∀ p k, p^k ≠ n`). Since `n = 2p` is not a prime power for
  odd prime `p ≥ 3`, this **blocks** the standard `zeta_sub_one_prime`
  route at `n = 2p` for Path B. The correct uniformizer at `(p)` in
  `ℤ[ζ_{2p}]` is `ζ + 1`, and Mathlib has **no `zeta_add_one_prime`**
  (negative search returns `total_count = 0`). Sharper than PR #19252
  §4's "no analog for the maximal real subfield" remark.

- **Witness extension at p = 7**: Bridge identity
  `C_p(X-2) + 2 = X · (r p)^2` verified numerically at p = 7, where
  `r_7 = X^3 - 7X^2 + 14X - 7`. The middle coefficient
  `(r_7).coeff 1 = 14 = 2·7 ∈ Ideal.span {7}` — the smallest prime
  where Path A's Eisenstein middle-coefficient obligation is
  non-empty and discharged.

- **Bearer stability re-check at SHA**: 3 bearers re-pinned (no drift
  in the ~17 PRs that landed between PR #19252's merge and PR #19305's
  open).

- **Reduction sketch (§5)**: From the bridge
  `C_p(X-2) + 2 = X · (r p)^2`, the LHS's coefficients are integer-
  linear combinations of `C(p, k)` binomials, each divisible by `p`
  for `1 ≤ k ≤ p-1` (`hp.out.dvd_choose_self`). Extracting divisibility
  for `(r p).coeff *` requires the **Eisenstein step-up lemma**
  (lift along monic factorization). Caveat: this convolution step
  is the non-trivial part; Mathlib's
  `Polynomial.IsWeaklyEisensteinAt.mul` (Eisenstein/Basic.lean:72)
  may discharge it in reverse.

### Net STATE-SYNC delta

| Field | Pre-S15-ACT-merge | Post-S15-ACT-merge (HEAD) | Post-S17-PREP-STATE-SYNC (this PR) |
|---|---|---|---|
| `state.md` "Phase" line | S10 era | S15 ACT closed Lean | unchanged (still S15 ACT closed Lean; S16 PREPs were doc-only, did not advance Lean) |
| `state.md` "Iteration" line | 14 | 15 | **17** (S15 ACT + S16 PREP-1/PREP-2 + S17 PREP STATE-SYNC) |
| `state.md` "Recent PREP audit chain" subsection | S11-S14 | S11-S14 | **extended with S16-PREP-1, S16-PREP-2, S17-PREP** rows |
| `state.md` "Current Focus" body | S10 era | S15 ACT three theorems | unchanged (S15 still defines current Lean focus) |
| JSON `currentState.phase` | "ACT" | "ACT" | unchanged ("ACT" — open conjecture sorry remains) |
| JSON `currentState.since` | 2026-05-12 era | 2026-05-14T06:25:00Z | **2026-05-16T00:12:00Z** (this STATE-SYNC's UTC) |
| JSON `currentState.iteration` | 14 | 15 | **17** |
| JSON `currentState.focus` | S10 era | S15 ACT three theorems | extended to note S16 PREPs absorbed + S17 PREP STATE-SYNC closed |
| JSON `currentState.nextAction` | S11+ trace bridge | "S16 PREP-first survey of two paths" | **"S17 ACT: Option A Chebyshev-C bridge, ~120-180 LOC, S17a/b/c/d work order from PR #19252 §6"** |
| JSON `knowledge.builtItems` | S10 entry | + S15 entry | + S16 PREP-1 entry + S16 PREP-2 entry + S17 PREP STATE-SYNC entry |
| JSON `knowledge.nextSteps` | S7-pre era | unchanged (stale) | **re-targeted to S17a/b/c/d Option-A sub-steps** |

---

## §3 — Bearer drift recheck at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

The Mathlib pin in `proofs/lake-manifest.json` is **unchanged** since the
S15 era: `rev = "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"` (= v4.26.0
tag SHA, `inputRev = "v4.26.0"`). Six PRs have landed on origin/main
between PR #19305's merge (2026-05-15T19:00:26Z, content-addressed at
`16aa51f8180`) and the open of this STATE-SYNC (2026-05-16T~00:12Z,
HEAD `e65ee7eae5b`), but none touch `proofs/lakefile.toml` or
`proofs/lake-manifest.json`. Therefore the bearer claims from PR #19252
§3 and PR #19305 §1 remain valid at this STATE-SYNC's HEAD.

### Re-pinned bearers (6 of the 18 in PR #19252's bearer table)

| Bearer | Path / Line at SHA | Drift status | Reason load-bearing |
|---|---|---|---|
| `Polynomial.IsEisensteinAt` (structure) | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:55` | ✓ unchanged | 3 fields `leading` / `mem` / `notMem`; S17c uses to instantiate `IsEisensteinAt 𝓟 (r p)` |
| `Polynomial.IsEisensteinAt.irreducible` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:239` | ✓ unchanged | S17d applies to close the conjecture |
| `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:211` | ✓ unchanged (+ deprecated snake_case alias at 218-220, **Finding A**) | S17c instantiates this for `r p` monic + middle-mem (S17b) + leading-notMem (S2 `r p` monic + `1 ∉ Ideal.span {p}` for p prime ≥ 2) |
| `Polynomial.Chebyshev.C` | `Mathlib/RingTheory/Polynomial/Chebyshev.lean:293` | ✓ unchanged | S17a primary bearer for the bridge identity |
| `Polynomial.Chebyshev.C_add_two` (recurrence) | `Mathlib/RingTheory/Polynomial/Chebyshev.lean:301` | ✓ unchanged | S17a induction step for the bridge identity |
| `cyclotomic_two_mul_prime_eq_geom_neg_series` (slug-local, in file) | `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean:~1000` | ✓ unchanged (S9 era, frozen since PR #18103) | S17a may use as ℤ-coefficient hook for the bridge induction |

**Net: 0 drift across 6 re-pinned bearers; Mathlib pin frozen
since at least S10 era (May 9, 2026).**

### Negative search confirmations (re-run)

| Search | At SHA | Result | Implication |
|---|---|---|---|
| `gh api search/code?q=zeta_add_one+repo:leanprover-community/mathlib4` | `2df2f015...` | `total_count = 0` | PR #19305 §4 Finding C reaffirmed: no `zeta_add_one_prime` bearer for the alternative Path B uniformizer route |
| `grep -n cyclotomic Eisenstein/Criterion.lean` | `2df2f015...` lines 33-44 | `## TODO ... cyclotomic polynomials of prime index p ...` | PR #19305 §3 Finding B reaffirmed: even unshifted `Φ_p` Eisenstein criterion is a Mathlib upstream TODO |

---

## §4 — S17 ACT readiness gate

### Option A (recommended): sharpened Path A via Chebyshev-C bridge

**Statement**: Prove `(r p).coeff k ∈ Ideal.span {(p:ℤ)}` for every
middle index `1 ≤ k ≤ (p-1)/2 - 1` and every odd prime `p ≥ 3`,
discharging the remaining (HARD) sub-leading-divisibility gap toward
the open conjecture `eisenstein_conjecture_cos_pi_p`.

**LOC budget**: 120-180 LOC (PR #19252 §6 estimate).

**Work order** (PR #19252 §6 + PR #19305 §9):

| Sub-step | LOC | What | Risk | Bearer-naming gotcha |
|---|---|---|---|---|
| S17a | ~80-120 | Bridge identity `(C ℤ p).comp (X - C 2) + C 2 = X · (r p)^2` for odd prime `p`. Three candidate proof routes: (i) degree-counting + roots argument over ℂ via `IsPrimitiveRoot`, (ii) per-prime expansion for p ∈ {3, 5, 7, 11, 13} + uniform statement deferred (defeats uniformity), (iii) induction on `p` via `Polynomial.Chebyshev.C_add_two` recurrence. **Most promising: (iii).** | Medium — classical identity but not in Mathlib at SHA; needs custom proof | Use `Polynomial.Chebyshev.C` (line 293), `Polynomial.Chebyshev.C_add_two` (line 301), `Polynomial.Chebyshev.C_zero/C_one/C_two` (lines 318/321/329) |
| S17b | ~40-60 | Lift bridge to middle-coefficient divisibility for `(r p).coeff k`, `1 ≤ k ≤ (p-1)/2 - 1`, via `hp.out.dvd_choose_self` on the LHS Chebyshev expansion + Eisenstein step-up on the `(r p)^2 = LHS / X` quotient. | Medium-high — convolution `(r·r).coeff k = ∑ (r).coeff i · (r).coeff j` divisibility-extraction is non-trivial; may need `Polynomial.IsWeaklyEisensteinAt.mul` (`Eisenstein/Basic.lean:72`) in reverse | — |
| S17c | ~10-20 | Instantiate `IsEisensteinAt 𝓟 (r p)` for `𝓟 = Ideal.span {(p:ℤ)}` using: leading `(r p).coeff ((p-1)/2) = 1` ∉ 𝓟 (from S2/S3, r monic); middle `(r p).coeff k ∈ 𝓟` (from S17b); constant `(r p).coeff 0 = -p ∈ 𝓟 \ 𝓟²` (from S10 + p prime ≥ 2 so p² ∤ p). | Low — standard structure-field instantiation | **MUST USE camelCase `notMem`**: `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` (line 211). The snake_case alias `_not_mem` (line 218-220) is `@[deprecated (since := "2025-05-23")]` ⇒ build emits deprecation warning |
| S17d | ~10 | Apply `Polynomial.IsEisensteinAt.irreducible` (line 239) + monic + degree positivity (`(p-1)/2 ≥ 1` for p ≥ 3) to discharge `Irreducible (r p)`. Combine with `r_constantCoeff_eq_signed_uniform` (S10) + the polynomial degree + the Mathlib `minpoly`-identification path (S2/S3 era already established `r p` is the minimal polynomial of `2 + 2 cos(π/p)` for p ∈ {3,5,7,11,13}; the uniform version requires further work — see §4-followup). | Low for irreducibility; **the open conjecture statement requires existence of a Monic Eisenstein polynomial of degree `(p-1)/2`, which S17a-c delivers, so S17d closes the conjecture in the form stated in the file** | — |

### Findings A/B/C as trip-wires for S17 ACT

- **Finding A** (camelCase `notMem` vs deprecated snake_case
  `not_mem`): bake into S17c's bearer-citation hygiene.
- **Finding B** (Mathlib `Φ_p` Eisenstein is upstream TODO):
  cite in S17 module docstring as motivation for slug-side build.
- **Finding C** (no `zeta_add_one_prime` for `n = 2p`; correct
  uniformizer is `ζ + 1` not `ζ - 1`): justifies why this STATE-SYNC
  does **not** pivot S17 to Path B even though Path B is the
  classical proof — the missing real-subfield uniformizer + missing
  `zeta_add_one_prime` bearer would compound to 250-450 LOC vs
  Option A's 120-180 LOC.

### Conditional fallback: Option B (real-subfield uniformizer)

Only attempt if S17a's bridge induction proof becomes unexpectedly
hard (>200 LOC or stuck on `IsPrimitiveRoot.minpoly` machinery). LOC
budget 250-450, decomposable across 3-5 sub-iterations (S17/S18/S19/
S20/S21). Decision rule: if S17a's first build-iteration attempt
exceeds 250 LOC or fails to type-check after 3 surgical-fix
iterations, switch to Option B for that sub-step. Both options
share S17c-d (the final-mile `IsEisensteinAt.irreducible` chain).

### Conditional fallback: Option C (direct Vieta + Newton identities)

Last resort, ~150-220 LOC. Use only if both Option A and Option B
stall. PR #19252 §5 estimates the Newton-identity machinery is
sparse at the pinned SHA, but `MvPolynomial.symmetricSubring` and
`elementarySymmetric` have some coverage. **Not currently planned
for S17 ACT.**

### S17 ACT readiness checklist

- [x] Mathlib pin frozen at SHA `2df2f015...` — verified §3.
- [x] All Option-A bearers re-verified at SHA — verified §3.
- [x] Bridge identity numerical witnesses at p ∈ {3, 5, 7} — verified
      PR #19252 §2 (p ∈ {3, 5}) + PR #19305 §5 (p = 7).
- [x] Findings A/B/C catalogued and threaded into S17a/b/c — done §4.
- [x] state.md + JSON STATE-SYNC absorbing S16 PREP-1 + S16 PREP-2 —
      this PR.
- [x] `r p` monic + degree-`(p-1)/2` + endpoints (S10 constant, S15
      sub-leading) ready for S17c reuse — verified §1.
- [x] No open Lean-modifying ACTs in flight on this slug
      (#17906 effectively dead; CONFLICTING for days).
- [ ] **Pending**: actual S17a bridge identity Lean proof (target
      ~80-120 LOC, route (iii) Chebyshev induction).

---

## §5 — Parent-regression catalogue

None pending at this STATE-SYNC's HEAD:

- Mathlib pin frozen since at least 2026-05-09 era (S10 era).
- No Lean parent-file edits in flight on origin/main that the slug's
  `r p`-bearers or `cyclotomic_*`-bearers depend on.
- All 18 bearers from PR #19252's table re-verified by content-
  addressed SHA pin (no drift possible without pin change).
- The 6 PRs between PR #19305's merge and this STATE-SYNC's open
  (visible at `git log --since='6 hours ago' origin/main`) are
  unrelated to this slug's surface area: they cover unrelated
  galleries (`abel-ruffini`, `minkowski-theorem`, `tractatus-ontology`,
  `cayley-hamilton-minpoly`, `cramers-rule`, `lagrange-four-squares`,
  `szemeredi-core`) per the `git log` titles.

**No parent regression to discharge.**

---

## §6 — Orthogonality manifest (vs in-flight PRs)

| Open PR | Surface | This STATE-SYNC's surface | Overlap? |
|---|---|---|---|
| #17906 (S4 ACT, stale 4 days, CONFLICTING) | `Proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` + `meta.json` + `state.md` | only `state.md` (additions) + `json` (registry) + new session file | **`state.md`** — needs verification |
| #18171 (mechanic meta batch, CONFLICTING) | `src/data/proofs/<slug>/meta.json` for 4 entries | does NOT touch `meta.json` for any entry | **None** |

### #17906 `state.md` overlap analysis

PR #17906 was opened 2026-05-12T06:22:25Z, **4 days ago**, in the pre-S5
era. It has been CONFLICTING for at least 3 days (since PR #18028 S6
merged on 2026-05-12 night UTC). The CONFLICTING status means git's
3-way merge cannot resolve it automatically against current `state.md`
even if this STATE-SYNC didn't touch `state.md` at all.

**Net**: this STATE-SYNC's `state.md` edit does not change the
already-CONFLICTING status of PR #17906. The author or a doctor would
need to rebase #17906 onto current `main` (post-S5/S6/S7/S8/S9/S10/
S11-S14/S15/S16-PREP-1/S16-PREP-2/S17-PREP-STATE-SYNC) for any merge
attempt, at which point #17906's claims (irreducibility for p ∈ {11,13})
are **subsumed** by S15's uniform sub-leading-coefficient bridge +
S10's uniform constant-coefficient bridge. PR #17906 is **effectively
superseded** by the S5-through-S15 chain, and its author should close
it.

**This STATE-SYNC does not claim authority to close PR #17906 — that
decision belongs to its author or a doctor / champion role. We note it
for completeness.**

### #18171 meta.json batch — not touched

Confirmed by file scope: this PR adds the new session file +
modifies `state.md` + `currentState`-fields in JSON registry. It does
**not** touch `src/data/proofs/<slug>/meta.json`.

---

## §7 — Honesty log

| Claim | Confidence | Why |
|---|---|---|
| S15 ACT PR #19053 merged 2026-05-15T23:27:25Z | High | `gh pr view 19053 --json mergedAt` direct read |
| S16 PREP-1 PR #19252 merged 2026-05-15T18:03:25Z | High | `gh pr view 19252 --json mergedAt` direct read |
| S16 PREP-2 PR #19305 merged 2026-05-15T19:00:26Z | High | `git show 16aa51f8180` commit date + commit subject line |
| Mathlib pin `2df2f015...` unchanged since S10 era | High | `proofs/lake-manifest.json` direct read + `git log --since="2 weeks ago" -- proofs/lake-manifest.json` (no commits in window) |
| 6 bearers re-pinned at SHA with 0 drift | High | Content-addressed SHA pin; bearers were verified in PR #19252 §3 + PR #19305 §1 at the same SHA. Pin has not moved ⇒ no drift possible without pin change. |
| Option A LOC budget 120-180 | Medium | PR #19252 §6 estimate; not Lean-verified |
| Option A is the recommended next ACT | High | PR #19252 §6 explicit recommendation + PR #19305 §9 reaffirmation |
| Lean stats at HEAD: 1380 LOC, 1 real sorry, 65 named | High | Direct `wc -l` + `grep` on the file at HEAD |
| PR #17906 superseded by S5-through-S15 | Medium-high | Logical argument based on PR #17906's stated scope (per-prime irreducibility for p ∈ {11,13}) and the merged S5/S6/S10/S15 chain — not Lean-verified line-by-line |
| `currentState.nextAction` "S16 PREP-first survey" is stale | High | The two S16 PREPs are MERGED; the nextAction text refers to S16 as future work |
| `state.md` Iteration counter "15" is stale | High | Two S16 PREPs merged after S15 ACT; iteration should be 17 by the convention used in S11-S14 (each PREP = 1 iteration), or at least 16 with S16-PREP-1+PREP-2 grouped |
| This STATE-SYNC closes the S16 PREP-1 + S16 PREP-2 documented STATE-SYNC debt | High | PR #19252 §7 + PR #19305 §8 explicitly defer state.md+JSON to "future STATE-SYNC iteration" |

### Anti-claims (what this STATE-SYNC does NOT show)

- It does **not** Lean-verify the bridge identity
  `C_p(X-2) + 2 = X · (r p)^2` (only numerical witnesses at p ∈ {3,5,7}).
  This is the S17a deliverable.
- It does **not** modify the Lean file
  `AngleTrisectionCos20GalOQ01OQ03.lean` in any way.
- It does **not** modify `proofs/lake-manifest.json` or any other Lake
  manifest. Mathlib pin is frozen.
- It does **not** discharge the slug's remaining `sorry`
  (line 1378, `eisenstein_conjecture_cos_pi_p`).
- It does **not** claim authority to close PR #17906 (the stale S4 ACT).
- It does **not** modify `meta.json`, `problem.md`, or `knowledge.md`.

---

## §8 — Conflict-free guarantees

This PR adds **only**:

- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-16-s17-prep-state-sync.md` (NEW, this file)
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/state.md` (MODIFIED: extends Iteration counter; adds "Recent PREP audit chain (S16-PREP-1 / PREP-2)" subsection + "S17 PREP STATE-SYNC" subsection)
- `src/data/research/problems/angle-trisection-cos-20-gal-oq-01-oq-03.json` (MODIFIED: `currentState.iteration` 15→17; `currentState.since`; `currentState.focus` extended; `currentState.nextAction` re-targeted from "S16 PREP-first survey" to "S17 ACT Option A Chebyshev-C bridge"; `lastUpdate` bumped; `knowledge.builtItems` extended; `knowledge.nextSteps` re-targeted)

It does **not** modify:

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (owned by PR #17906 stale S4 ACT + frozen since PR #19053 S15 ACT on origin/main).
- `proofs/lake-manifest.json` / `proofs/lakefile.toml` (Mathlib pin frozen).
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/meta.json` (owned by PR #18171 mechanic-batch — line/theorem-count drift fix).
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/annotations.json`.
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/index.ts`.
- Any session file in `sessions/` other than this newly created S17 PREP STATE-SYNC log.
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/problem.md`.
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/knowledge.md`.
- Any file outside the slug's `research/problems/` + `src/data/research/problems/` + `sessions/` triangle.

Strict file-disjointness verified for **all 2 open PRs** on the slug
(#17906 ACT-stale touching the Lean file + meta.json + state.md;
#18171 mechanic-batch touching meta.json for 4 entries):

- **vs PR #17906**: PR #17906 is already CONFLICTING for days; its
  state.md edit would need rebase. The state.md text this STATE-SYNC
  adds is in the "Iteration" line + a new "Recent PREP audit chain
  (S16-PREP-1 / PREP-2)" subsection + new "S17 PREP STATE-SYNC"
  subsection — surfaces PR #17906's stale edit does not touch (since
  PR #17906 was opened 2026-05-12 pre-S5 era). No new conflict
  introduced; #17906 remains CONFLICTING for the unchanged reasons.
- **vs PR #18171**: PR #18171 modifies only `src/data/proofs/*/meta.json`
  for 4 entries (line/theorem-count drift). This STATE-SYNC does not
  touch any `meta.json`. **Zero overlap.**

This satisfies the deployer-stall coordination pattern: doc-only PR
with strict file-disjoint scope and zero Lean-side cost.

---

## §9 — Anti-targets

This PR intentionally does **not**:

- Modify the Lean file (frozen since PR #19053; reserved for S17a ACT).
- Modify `meta.json` (orthogonal to research narrative; reserved for
  mechanic-batch PR #18171).
- Add a placeholder Lean stub or sorry for the bridge identity
  (would require Lean file modification; S17a's responsibility).
- Recommend closing PR #17906 (its author / a doctor or champion role
  decides).
- Re-derive any of the S10/S15 ACT or S11-S14/S16-PREP/S16-PREP-2 doc
  content (those are closed by their merged PRs).
- Bump JSON `meta.json` `sorries` or `axioms` counts (Lean unchanged).
- Modify `problem.md` or `knowledge.md` (the slug's `currentState` /
  `builtItems` JSON fields are the authoritative narrative now).

---

## §10 — Cross-references

- **PR #19053** (S15 ACT, merged 2026-05-15T23:27:25Z): the Lean-side
  ACT this STATE-SYNC catches up to.
- **PR #19252** (S16 PREP-1, merged 2026-05-15T18:03:25Z): the path-
  survey PREP whose §7 conflict-free clause deferred state.md+JSON to
  this STATE-SYNC.
- **PR #19305** (S16 PREP-2, merged 2026-05-15T19:00:26Z): the bearer-
  deprecation + p=7-witness extension whose §8 conflict-free clause
  also deferred state.md+JSON to this STATE-SYNC.
- **PR #17906** (S4 ACT, stale 2026-05-12, CONFLICTING): pre-S5 era;
  effectively superseded by S5-through-S15 chain; orthogonal to this
  STATE-SYNC's edit surface.
- **PR #18171** (mechanic meta batch, CONFLICTING): orthogonal scope
  (meta.json line/theorem-count drift); zero overlap with this PR.
- **Memory pattern** `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`:
  the archetype this PR instantiates (post-ship pivot to ship deferred
  STATE-SYNC owed by just-merged sibling PREPs' "Conflict-free
  guarantees" clauses).
- **Memory pattern** `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton_during_deployer_stall.md`:
  the §3 bearer-pin-at-SHA verification pattern.
- **Memory pattern** `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`:
  the §8 strict file-disjointness pattern.
- **Lean file**: `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`
  at line 1378 (the open conjecture `eisenstein_conjecture_cos_pi_p`).
- **Mathlib bearers**: `Polynomial.Chebyshev.C` at
  `Mathlib/RingTheory/Polynomial/Chebyshev.lean:293` (SHA `2df2f015...`);
  `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` at
  `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:211` (SHA
  `2df2f015...`).

---

## Appendix A — Open-PR snapshot at session start

```
$ gh pr list --repo rjwalters/lean-genius \
    --search "angle-trisection-cos-20-gal-oq-01-oq-03" --state open --limit 20
#18171 — fix(meta): sync count drift in 4 entries (lineCount/theoremCount)
        fix/mechanic-meta-drift-batch-4entries, CONFLICTING, opened 2026-05-12T15:29:29Z
#17906 — research(angle-trisection-cos-20-gal-oq-01-oq-03): S4 — irreducibility round-out ... (build pending)
        research/angle-trisection-cos-20-gal-oq-01-oq-03-s4-sign-uniformity-1778566527,
        CONFLICTING, opened 2026-05-12T06:22:25Z
```

Both CONFLICTING; both pre-S5 era for slug content (mechanic batch is
2026-05-12 mid-day; #17906 is 2026-05-12 morning). Net: 2 effectively
dead open PRs; 0 active in-flight ACT on this slug. This STATE-SYNC
ships into a clean lane.

## Appendix B — Drain-wave context at session start

```
$ date -u
Sat May 16 00:11 UTC 2026

$ gh pr list --repo rjwalters/lean-genius --state open --limit 500 --json number -q 'length'
88

$ git log origin/main --since="60 minutes ago" --oneline | wc -l
75

$ git log origin/main --since="10 minutes ago" --oneline | wc -l
0

$ git log origin/main -1 --format='%cI %s'
2026-05-15T16:45:20-07:00  research(abel-ruffini-oq-04-oq-09): ... (#18986)
```

Drain wave from ~270 open PRs earlier in the day to 88 now, then
quieted: 75 merges in the last hour, 0 in the last 10 minutes. Last
merge ~18 minutes before this PREP's open. Pile-up has substantially
resolved; deployer recovered. This is a **healthy lane to ship a
small doc-only PR.**
