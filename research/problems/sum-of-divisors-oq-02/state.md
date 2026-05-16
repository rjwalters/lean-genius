# Current State

**Phase**: PREP (S6 — Step 4 discharge recipe + 3 NEW bearer pins; runs in parallel with sibling S5 ACT PR #19562 which is build-pending under host Docker daemon hang)
**Since**: 2026-05-16T10:00:00Z (S6 PREP)
**Iteration**: 6
**Agent**: researcher-8 (S2, S3 PREP, S5 PREP, **S6 PREP this iter**); researcher-9 (S4); researcher-12 (S1); sibling agent (S5 ACT #19562, open + build-pending)

## Latest Iteration: S6 PREP — Step 4 discharge recipe + 3 NEW bearer pins (researcher-8, 2026-05-16T10:00Z)

Doc-only PREP closing S5 PREP's §"Next Action SECOND" pre-stage for
Step 4 (`mersenne_dvd_odd_part`). S5 PREP (PR #19467, merged
2026-05-16T08:54Z) named Step 4 as the next-after-Step-3 picker target;
a sibling agent picked up the **TOP** priority (S5 ACT, Step 3 discharge)
in PR #19562 at 2026-05-16T09:25Z (build-pending under same Docker daemon
hang documented in S5 PREP §6). Since Step 3 and Step 4 are structurally
orthogonal lemmas (different `sorry` stubs, no shared tactic body), this
S6 PREP advances the **SECOND** priority in parallel with the in-flight
S5 ACT.

This S6 PREP packages Step 4 as the natural next-ACT target with paste-ready
Lean + 3 NEW bearer pins:

1. **NEW bearer N1** — `Nat.Coprime.pow_right` at lean4 core
   `Init/Data/Nat/Coprime.lean:167` (v4.26.0). Signature
   `(n : Nat) (H1 : Coprime k m) : Coprime k (m ^ n)`. Boosts
   coprime-with-2 to coprime-with-`2^(k+1)`.
2. **NEW bearer N2** — `Nat.Coprime.dvd_of_dvd_mul_left` at lean4 core
   `Init/Data/Nat/Coprime.lean:41` (v4.26.0). Signature
   `(H1 : Coprime k m) (H2 : k ∣ m * n) : k ∣ n`. Extracts the
   divisibility from the coprime + mul-divides hypothesis.
3. **NEW bearer N3** — `mersenne_odd` at
   `Mathlib/NumberTheory/LucasLehmer.lean:58`. Signature
   `@[simp] : ∀ {p : ℕ}, Odd (mersenne p) ↔ p ≠ 0`. Simp-discharges
   `Odd (mersenne (k+1))` via `Nat.succ_ne_zero`.

Plus 1 inherited from S3 PREP §2.1 (re-verified ±1 line drift at SHA):

- `Odd.coprime_two_right` at `Mathlib/Data/Nat/Prime/Basic.lean:150`
  (S3 PREP cited L151; protected alias of `coprime_two_right`).

All four bearers re-verified at unchanged Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0) + lean4 core `v4.26.0` via `gh api …?ref=<SHA>` / raw GitHub content fetch — 0 drift.

### Construction recipe (math)

```
mersenne (k+1) * σ 1 m = 2^(k+1) * m
  ↦ Odd (mersenne (k+1))                       [mersenne_odd + Nat.succ_ne_zero, by simp]
  ↦ Coprime (mersenne (k+1)) 2                 [Odd.coprime_two_right]
  ↦ Coprime (mersenne (k+1)) (2^(k+1))         [.pow_right (k+1)]
  ↦ mersenne (k+1) ∣ 2^(k+1) * m               [Dvd.intro (σ 1 m) h_eq]
  ↦ mersenne (k+1) ∣ m                         [.dvd_of_dvd_mul_left]
```

Total ~5 LOC term-mode body. See `sessions/2026-05-16-s6-prep-step4-discharge-recipe.md`
§3 for the paste-ready Lean (verbatim from Archive line 81-82 template) and §3.1
for the 1-iteration build forecast.

### Build-pending caveat (host Docker daemon hung; same condition as #19562)

At PREP draft time, the host Docker daemon `Server:` section returns
empty (response not received within 30s timeout) while the Client section
responds fully. Same condition documented in PR #19562's "Docker daemon
hung" qualifier. Host disk: `/System/Volumes/Data` 6.8 Gi available
(100% capacity).

The S6 ACT picker must confirm `docker info` returns a populated Server
section before applying §3 and running the Docker build. PR #19562's
build verification depends on the same recovery.

### Race safety vs sibling PR #19562

|                          | This S6 PREP                              | #19562 (S5 ACT)                            |
|--------------------------|-------------------------------------------|--------------------------------------------|
| Files                    | `state.md`, JSON, NEW session memo        | `proofs/Proofs/SumOfDivisorsOQ02.lean`, NEW session memo |
| Lean line range touched  | none                                      | L67-70 (Step 3 body)                       |
| Sorry-stub addressed     | Step 4 (L77-80) — by S6 ACT picker        | Step 3 (L67-70)                            |
| Overlap                  | none — orthogonal Lean lemmas + distinct session-memo filenames |                            |

Merge order independence: this S6 PREP and #19562 can land in either order
without conflict; #19562's "Untouched" list explicitly excludes `state.md` /
JSON updates (deferred to "S5b BUILD-VERIFY").

### ACT-readiness gate (7/8 GREEN math + 1/8 RED INFRA + 1/8 AMBER INFRA)

| # | Item | Status |
|---|------|--------|
| 1 | Mathlib pin unchanged | GREEN |
| 2 | Step 4 hypothesis `h_eq` exposed by sorry-stub at L77-80 | GREEN |
| 3 | 3 NEW bearers pinned + content-verified at SHA | GREEN |
| 4 | Paste-ready ~5-LOC term-mode discharge | GREEN |
| 5 | 2 build-risk items + 2 fallback recipes | GREEN |
| 6 | Host Docker daemon healthy at S6 ACT pick time | **RED — INFRA** — must `docker info` Server-section recheck before ACT |
| 7 | No competing peer PRs on Step 4 lemma | GREEN — #19562 touches Step 3 only |
| 8 | Disk pressure resolved | **AMBER** — 6.8 Gi avail (100% capacity) |

### Next Action (S6 ACT picker priority)

**TOP — S6 ACT (Step 4 discharge, ~5 LOC term-mode + ~7 LOC docstring)**: single PR
replacing the existing `sorry` for `mersenne_dvd_odd_part`
with the §3 paste-ready body. Sorry count: 5 → 4 (independent of #19562) or 4 → 3
(if #19562 merges first). Single Docker iter expected once host is healthy.

**SECOND — Wait for #19562 build-verification**: safer if picker prefers a
known-good Lean state. Build-verification window for #19562 likely <30 min
once Docker recovers.

**THIRD — S7 PREP (Step 5, `sigma_eq_self_add_cofactor`)**: S3 PREP §5.3 has
a 5-line body with one final-tactic pin-PEND.

### Files touched (3 — doc-only)

1. `research/problems/sum-of-divisors-oq-02/sessions/2026-05-16-s6-prep-step4-discharge-recipe.md` (NEW, ~350 LOC).
2. `research/problems/sum-of-divisors-oq-02/state.md` (head replaced; S5 PREP block preserved verbatim below).
3. `src/data/research/problems/sum-of-divisors-oq-02.json` (`currentState.{phase preserved PREP, iteration 5→6, since, focus, nextAction}`, `attemptCounts.total/currentApproach 5→6`, `updatedAt`, `nextSteps` reorder).

### Honesty footprint

- 0 new Lean theorems (the §3 discharge is paste-ready but not committed).
- 0 axioms.
- 0 sorries added or removed.
- 0 `meta.json` edits (file does not yet exist for this slug).
- 0 `problem.md` / `knowledge.md` edits.
- 0 Mathlib pin changes.
- 3 NEW bearer pins + 1 inherited re-verified.

### Trail — what changed vs S3 PREP §8 Step 4 hint

S3 PREP §8 originally pointed at `Nat.Prime.coprime_pow_of_not_dvd` for the
coprime-with-`2^(k+1)` bridge (requiring an explicit `¬ 2 ∣ mersenne (k+1)`
detour). This S6 PREP adopts the Archive line 81 path:
`Odd.coprime_two_right ∘ mersenne_odd ∘ Nat.succ_ne_zero` via `(by simp)`
discharger — 2 LOC shorter; matches Archive verbatim.

---

## Previous Iteration: S5 PREP — Step 3 discharge recipe + bearer pin (researcher-8, 2026-05-16T05:00Z)

Doc-only PREP closing S3 PREP's §8 "Out of scope (deferred)" item for
Step 3 (`mersenne_mul_sigma_eq_two_pow_mul`). S3 PREP marked Step 3 as
"S4 follow-up (~6 LOC)" — but S4 ACT (PR #19357, MERGED 2026-05-16T03:53Z)
shipped only Step 1. This S5 PREP packages Step 3 as the natural next-ACT
target with paste-ready Lean + 2 NEW bearer pins:

1. **NEW bearer N1** — `Nat.perfect_iff_sum_divisors_eq_two_mul` at
   `Mathlib/NumberTheory/Divisors.lean:405`. Signature
   `(h : 0 < n) : Perfect n ↔ ∑ i ∈ divisors n, i = 2 * n`. Supplies
   the Perfect-to-`σ 1 = 2·n` bridge.
2. **NEW bearer N2** — `ArithmeticFunction.sigma_one_apply` at
   `Mathlib/NumberTheory/ArithmeticFunction/Basic.lean:169`. Signature
   `σ 1 n = ∑ d ∈ divisors n, d`. Rewrites the divisor sum into `σ 1`.

Both bearers re-verified at unchanged Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0) via `gh api …?ref=<SHA>` content fetch — 0 drift.

### Construction recipe (math)

```
Perfect (2^k * m)
  ↦ σ 1 (2^k * m) = 2 * (2^k * m)               [N1 + N2 + sigma_one_apply]
  ↦ σ 1 (2^k) * σ 1 m = 2 * (2^k * m)            [Step 1: sigma_two_pow_mul_odd]
  ↦ mersenne (k+1) * σ 1 m = 2 * (2^k * m)       [Step 2: sigma_two_pow_eq_mersenne]
  ↦ mersenne (k+1) * σ 1 m = 2^(k+1) * m         [← mul_assoc; ← pow_succ']
```

Total ~7 LOC tactic body. See `sessions/2026-05-16-s5-prep-step3-discharge-recipe.md`
§3 for the paste-ready Lean and §4 for the 1-iteration build forecast.

### Build-pending caveat (host Docker daemon corrupt)

At PREP draft time, the host Docker daemon was observed in a corrupt
state (`docker info` reports containerd blob I/O error). Two PREP-time
Docker build attempts failed at the host-infrastructure layer
(Mathlib cache invalidation + blob storage write error), not at the
Lean elaboration layer. The S5 ACT picker must confirm `docker info`
returns successfully before applying §3 and running the Docker build.

### ACT-readiness gate (6/7 GREEN + 1/7 AMBER)

| # | Item | Status |
|---|------|--------|
| 1 | Mathlib pin unchanged | GREEN |
| 2 | Steps 1+2 in scope (parent file) | GREEN |
| 3 | 2 NEW bearers pinned + content-verified at SHA | GREEN |
| 4 | Paste-ready ~7-LOC discharge | GREEN |
| 5 | 3 build-risk items + 3 fallback recipes | GREEN |
| 6 | Host Docker daemon healthy at S5 ACT pick time | **AMBER** — must `docker info` recheck before ACT |
| 7 | No open peer PRs on slug | GREEN |

### Next Action (S5 ACT picker priority)

**TOP — S5 ACT (Step 3 discharge, ~7 LOC + ~4 LOC docstring)**: single PR
replacing the existing `sorry` for `mersenne_mul_sigma_eq_two_pow_mul`
with the §3 paste-ready body. Sorry count: 5 → 4. Single Docker iter
expected once host is healthy.

**SECOND — S6 PREP (Step 4 discharge, `mersenne_dvd_odd_part`)**: ~5
LOC per S3 PREP §8; needs `Nat.Prime.coprime_pow_of_not_dvd` +
`.dvd_of_dvd_mul_left` bearer pins.

### Files touched (3 — doc-only)

1. `research/problems/sum-of-divisors-oq-02/sessions/2026-05-16-s5-prep-step3-discharge-recipe.md` (NEW, ~310 LOC).
2. `research/problems/sum-of-divisors-oq-02/state.md` (head replaced; S4 ACT block preserved verbatim).
3. `src/data/research/problems/sum-of-divisors-oq-02.json` (`currentState.{phase ACT→PREP, iteration 4→5, since, focus, nextAction}`, `updatedAt`, top-level `phase OBSERVE→ACT` drift fix).

### Honesty footprint

- 0 new Lean theorems (the §3 discharge is paste-ready but not committed)
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified (PREP-time build attempt edit reverted)
- 2 Docker build attempts (both failed at host-infrastructure layer)

## Previous Iteration (S4 ACT)

S4 ACT — discharged Step 1 (`sigma_two_pow_mul_odd`) verbatim from
`sessions/2026-05-14-s3-prep-step1-step5-discharge.md` §3.2 (term-mode body,
~3 LOC delta). Proof line:

```lean
isMultiplicative_sigma.map_mul_of_coprime
  ((Odd.coprime_two_right hm_odd).symm.pow_left k)
```

Bearers pin-cited at Mathlib v4.26.0 (`2df2f015...`):
`ArithmeticFunction.isMultiplicative_sigma` (`Mathlib/NumberTheory/ArithmeticFunction/Misc.lean:202`),
`ArithmeticFunction.IsMultiplicative.map_mul_of_coprime` (`Basic.lean`),
`Odd.coprime_two_right` (`Mathlib/Data/Nat/Prime/Basic.lean:151`),
`Nat.Coprime.symm` / `Nat.Coprime.pow_left` (core). All cited stable across
master→v4.26.0 history per S3 PREP audit. Sorry count: 6 → 5.

## Previous focus (S3 PREP)

S3 PREP (researcher-8, PR #19169 merged 2026-05-15T22:56:52Z) — doc-only
discharge plans for Step 1 (§3.2, 3-line term-mode) and Step 5 (§5.3, 5-line
tactic-mode with one pin-PEND `sorry` flagged on final-line reconciliation).
Bearer tables + risk register + Option A/B/C sequencing. New file
`sessions/2026-05-14-s3-prep-step1-step5-discharge.md` (~380 LOC). No
state.md/JSON/Lean edits.

## Previous focus (S2 SCAFFOLD)

S2 SCAFFOLD — landed `proofs/Proofs/SumOfDivisorsOQ02.lean` (110 LOC) with the
6-step pedagogical decomposition of Euler's converse for even perfect numbers.
Step 2 (sigma_two_pow_eq_mersenne) is proved as a direct Archive alias; Steps 1,
3, 4, 5, 6 and the top-level `euler_converse_self_contained` carry `sorry`
placeholders with documented S3+ discharge plans inline in each lemma's docstring.

Build verified at Mathlib v4.26.0 (`docker-build.sh Proofs.SumOfDivisorsOQ02`,
3063 jobs clean, 6 sorry warnings as expected).

### S4 deliverables

```lean
-- (i) Step 1 — sigma multiplicativity (PROVED, S4 ACT term-mode).
lemma sigma_two_pow_mul_odd (k m : ℕ) (hm_odd : Odd m) :
    σ 1 (2 ^ k * m) = σ 1 (2 ^ k) * σ 1 m :=
  isMultiplicative_sigma.map_mul_of_coprime
    ((Odd.coprime_two_right hm_odd).symm.pow_left k)
```

LOC delta: +6 / -4 (drops the `by sorry` stub, adds term-mode body + updated
docstring). Sorry count: 6 → 5. Build status: **Docker build clean at 3063
jobs** at Mathlib v4.26.0 pin `2df2f015...` (`docker-build.sh
Proofs.SumOfDivisorsOQ02`, 5 expected sorry warnings on Steps 3/4/5/6/top-level).

### S2 deliverables

```lean
-- (i) Step 1 — sigma multiplicativity over coprime factorizations.
lemma sigma_two_pow_mul_odd (k m : ℕ) (hm_odd : Odd m) :
    σ 1 (2 ^ k * m) = σ 1 (2 ^ k) * σ 1 m

-- (ii) Step 2 — sigma of a power of 2 (PROVED, Archive alias).
lemma sigma_two_pow_eq_mersenne (k : ℕ) :
    σ 1 (2 ^ k) = mersenne (k + 1)

-- (iii) Step 3 — perfect equation expansion.
lemma mersenne_mul_sigma_eq_two_pow_mul
    (k m : ℕ) (hm_odd : Odd m) (h_perfect : (2 ^ k * m).Perfect) :
    mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m

-- (iv) Step 4 — Mersenne factor divides the odd part.
lemma mersenne_dvd_odd_part
    (k m : ℕ) (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    mersenne (k + 1) ∣ m

-- (v) Step 5 — sigma identity post-substitution.
lemma sigma_eq_self_add_cofactor
    (k m c : ℕ) (hm : m = mersenne (k + 1) * c)
    (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    σ 1 m = m + c

-- (vi) Step 6 — two-divisor analysis forces primality + c = 1.
lemma cofactor_one_and_prime
    (m c : ℕ) (hc_dvd : c ∣ m) (hc_lt : c < m) (hm_lt : 1 < m)
    (h_sigma : σ 1 m = m + c) :
    c = 1 ∧ m.Prime

-- (vii) Top-level chain.
theorem euler_converse_self_contained
    (n : ℕ) (h_even : Even n) (h_perfect : n.Perfect) :
    ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1)
```

### Axiom bookkeeping

`axiomCount = 0` (no `axiom` declarations, no structure-encoded assumptions).
`sorryCount = 5` (Steps 3, 4, 5, 6 and the top-level chain — Step 1 discharged
S4, Step 2 was already an Archive alias). `theoremCount = 7`
(6 lemmas + 1 top-level theorem). `defCount = 0`. `lineCount = 114`.

### Build status

3063-job Docker build clean at Mathlib v4.26.0 pin `2df2f015...`
(`Theorems100.Nat.sigma_two_pow_eq_mersenne_succ` and the rest of the
Archive surface continue to resolve; no v4.26.0 surface regressions hit).

## Previous focus (S1)

S1 OBSERVE (researcher-12, PR #18220 merged) — Survey of Euler's converse,
decomposed into 7 algebraic steps. Identified all required Mathlib API as
available (Archive.sigma_two_pow_eq_mersenne_succ, isMultiplicative_sigma,
Odd.coprime_two_right, succ_mersenne, sum_properDivisors_*). S2-prep PR
#18311 audited Mathlib for duplicate-detection (none found beyond the
bundled Archive proof).

## Active Approach

Pedagogical self-contained refactor of
`Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect` into named
intermediate lemmas. Parent slug `perfect-numbers` already wraps the bundled
Archive proof via `PerfectNumbers.euler_even_perfect`; OQ-02 exposes the
algebraic skeleton.

## Blockers

None at S2. For S3 ACT (Step 1 discharge):
- Risk: `isMultiplicative_sigma.map_mul_of_coprime` may have renamed at v4.26.0;
  fall-back is direct application of `IsMultiplicative.sigma` (the underlying
  multiplicativity lemma) since Step 1 is a simple specialization.

## Next Action

**S5 ACT — Discharge Step 3 (`mersenne_mul_sigma_eq_two_pow_mul`)** OR
**S5 PREP — bearer audit + risk register for Step 3**.

Step 3 plan (from SCAFFOLD docstring + Archive line 79):

```lean
lemma mersenne_mul_sigma_eq_two_pow_mul
    (k m : ℕ) (hm_odd : Odd m) (h_perfect : (2 ^ k * m).Perfect) :
    mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m := by
  -- unfold perfect: σ(2^k * m) = 2 * (2^k * m)
  -- apply Step 1: σ(2^k) * σ(m) = 2 * (2^k * m)
  -- apply Step 2: M_{k+1} * σ(m) = 2 * (2^k * m)
  -- ← mul_assoc, ← pow_succ (or pow_succ'): M_{k+1} * σ(m) = 2^(k+1) * m
  sorry
```

Required Mathlib lemma: `Nat.perfect_iff_sum_divisors_eq_two_mul` for the
`Perfect → σ = 2n` unfold (and the converse). The Archive's Step 3 invocation
is at line 79: `rw [perfect_iff_sum_divisors_eq_two_mul (by positivity)] at h;`

S6+: discharge Step 4 (~5 LOC, Archive line ~82), Step 5 (use S3 PREP §5.3's
discharge plan, resolve the final-line `linarith`/`linear_combination`/`rw`
fallback at Docker time), Step 6 (deepest step, ~10 LOC + cases-k branch),
top-level chain (S8+, ~8 LOC glue).

After Step 6 is discharged, the slug should be **honestly closed as
documentation-only**: the named decomposition is structurally identical to
the Archive proof, so the gallery value is naming + docstrings, not novel math.

## Subsequent Iterations (deferred)

- S5: discharge Step 3 (`mersenne_mul_sigma_eq_two_pow_mul`).
- S6: discharge Step 4 (`mersenne_dvd_odd_part`).
- S7: discharge Step 5 (`sigma_eq_self_add_cofactor`) — S3 PREP §5.3 supplies
  body, picker resolves final-line tactic per R3.
- S8: discharge Step 6 (`cofactor_one_and_prime`).
- S9: chain in `euler_converse_self_contained`.
- S10 (final, optional): polish docstrings, register gallery entry under
  `src/data/proofs/sum-of-divisors-oq-02/` with annotations; close slug.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 4
- Approaches tried: 1 (self-contained pedagogical refactor)

## Session Log

- **S1 (2026-05-12, researcher-12)**: OBSERVE. Doc-only survey of Euler's
  converse, 7-step decomposition, Mathlib API inventory. No Lean changes.
  PR #18220 merged. Mathlib duplicate-detection audit shipped as PR #18311.
- **S2 (2026-05-14, researcher-8)**: ACT. New file
  `proofs/Proofs/SumOfDivisorsOQ02.lean` (110 LOC): 6 named lemmas + 1
  top-level theorem mirroring the 7-step plan. Step 2 (`sigma_two_pow_eq_mersenne`)
  proved as direct Archive alias (1-line term proof). Steps 1, 3, 4, 5, 6
  and `euler_converse_self_contained` are `sorry`-stubbed with discharge
  plans documented in docstrings. 0 axioms, 6 sorries, 7 theorems, 0 defs.
  3063-job Docker build clean at Mathlib v4.26.0 pin `2df2f015...`.
- **S3 PREP (2026-05-14, researcher-8, PR #19169 merged 2026-05-15T22:56Z)**:
  Doc-only memo `sessions/2026-05-14-s3-prep-step1-step5-discharge.md` (~380
  LOC). Pin-cited Mathlib bearer tables for Step 1 (§2: 5 lemmas) and Step 5
  (§4: 4 lemmas). Verbatim Step 1 term-mode discharge (§3.2, 3 LOC). Step 5
  outline + 5-line tactic-mode body (§5.3) with one pin-PEND `sorry` flagged
  on final-line reconciliation. Sequencing recommendation (§6 Option A/B/C),
  risk register (§7 R1–R3), out-of-scope deferral table (§8). Strictly
  orthogonal to PR #19131 (no state.md/JSON/Lean edits).
- **S4 (2026-05-16, researcher-9)**: ACT. Discharged Step 1
  (`sigma_two_pow_mul_odd`) verbatim from S3 PREP §3.2 (term-mode,
  `isMultiplicative_sigma.map_mul_of_coprime ((Odd.coprime_two_right
  hm_odd).symm.pow_left k)`). LOC delta +6/-4 (drops `by sorry`, adds 3-LOC
  term-mode body + updated docstring). Sorry count: 6 → 5. **Docker build
  clean** at 3063 jobs against Mathlib v4.26.0 pin `2df2f015...` (5 expected
  sorry warnings remain on Steps 3/4/5/6/top-level).
