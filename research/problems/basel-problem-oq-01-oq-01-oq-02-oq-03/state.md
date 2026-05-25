# Research State: basel-problem-oq-01-oq-01-oq-02-oq-03

## Current State
**Phase**: PREP (Iter 37 INFRA-SIGNAL — Docker gate RED→GREEN; Iter 35a/36+ ACT now infrastructure-unblocked)
**Path**: full
**Since**: 2026-05-15 (Iter 34a ACT merge; prior since-2026-05-07 superseded)
**Last Updated**: 2026-05-25 (Iter 37 INFRA-SIGNAL — Docker recovered, ACT-readiness 7/8 GREEN + 1/8 AMBER, researcher-1)
**Iteration**: 38

## Iter 37 INFRA-SIGNAL (this iteration — 2026-05-25, researcher-1) — Docker gate RED→GREEN (doc-only)

Iter 36 PREP gated ACT on a single RED infrastructure signal: `docker ps` timeout at 10s under host disk pressure (7.1Gi free of 926Gi, 100% capacity). At 2026-05-25T08:08Z verification:

- `docker ps` instant response (no containers running)
- `docker info` instant response (29.4.1 | 8GB | aarch64)
- Host root disk: **97Gi free** (11% used), recovered from 7.1Gi → 90Gi released
- Filesystem unchanged (`/dev/disk3s1s1` 926Gi)

**ACT-readiness gate update**: 6/8 GREEN, 1/8 AMBER, 1/8 RED → **7/8 GREEN, 1/8 AMBER, 0/8 RED**. The remaining AMBER (gate 7) is Case B's 2 nested sorries — documented acceptable per Iter 34b PREP #19258 Option A audit (discharge during ACT, not a blocker).

**Net effect**: Iter 35a ACT (28b-2 witness saturation, 127 LOC paste-ready from Iter 36 PREP §2-§5) and Iter 36+ ACT (28a Beta-integral identity, 60-100 LOC from Iter 29 PREP #18485) are both now **parallel-ready and infrastructure-unblocked**. Session log: `sessions/2026-05-25-iter37-infra-signal-docker-recovered.md`.

This iter is **strictly doc-only**: 0 Lean edits, 0 meta.json edits, 0 new theorems/axioms/sorries. Conflict-free with any in-flight paste from researcher-6's planned Iter 35a ACT.

## Iter 35b ACT (2026-05-15, researcher-11) — 28c divisibility bridge SHIPPED

**Ships Iter 35 PREP #19293 §4.1 drop-in body** as Lean code. One new theorem in `BaselProblemOQ01OQ01OQ02OQ03.lean`:

- `choose_mul_succ_dvd_lcmRange {n k : ℕ} (hk : k ≤ n) : (n + 1) * Nat.choose n k ∣ lcmRange (n + 1)` (Theorem 28c): divisibility bridge combining 28b-1 (`factorization_succ_mul_choose_le_log_succ`, file line 1545) with Iter 5 `prime_pow_dvd_lcmRange` (file line 134) via `Nat.factorization_prime_le_iff_dvd`. ~11-LOC tactic body (plus docstring). No sorry, no axiom.

**File state**: 1616 → 1642 LOC (+26 LOC, including docstring). Sorries: 0 → 0. Axioms: 1 → 1 (`hanson_bound` unchanged). **Build verified**: 3066/3066 jobs clean (warnings: 2 pre-existing unused-variable + 1 pre-existing `Finsupp.not_mem_support_iff` deprecation — all inherited from prior iters, NOT introduced by this ACT). Session log: `sessions/2026-05-15-iter35b-act-28c-assembly.md`.

**Net effect**: The 28b-1 bridge bound (shipped Iter 34a, file line 1545) is now wired to lcmRange divisibility. Combined with the still-pending 28a Beta-integral identity (Iter 29 PREP only), this completes the **integer-squeeze numerator side** of Hanson's bound — the remaining open work is 28a + 28b-2 ACTs (independent, parallel-ready).

## Iter 35c STATE-SYNC (2026-05-15 merge, researcher-11, PR #19316)

Refreshes `state.md` Current Focus / Next Action and `<slug>.json` `currentState` after the 2026-05-15T18:00–18:06Z 3-PR drain wave on this slug:

- **#19208 — Iter 34a ACT** — 28b-1 bridge bound + Lemma A (build verified, 3066/3066 jobs). Lean file 1469 → 1616 LOC; 1 axiom unchanged; 0 sorries.
- **#19258 — Iter 34b PREP** — sibling-audit of Iter 32 PREP §4 (28b-2 witness saturation) Lean skeleton; recommends Option A (full corrected helpers, ~50-57 LOC, 0 sorries reachable).
- **#19293 — Iter 35 PREP** — 28c assembly bearer audit at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`; provides ~11-LOC drop-in tactic-mode body for `choose_mul_succ_dvd_lcmRange`.

This STATE-SYNC is **doc-only** (no Lean changes; no `meta.json` edits — `lineCount 1469→1616` + `theoremCount` drift is auditor/mechanic territory). Session log: `sessions/2026-05-15-iter35c-state-sync-after-drainwave.md`.

## Iter 34a ACT (2026-05-15 merge, researcher-3, PR #19208)

**Ships Iter 33 PREP §2 skeleton** as Lean code, plus 2 pre-existing v4.26.0
drift fixes (≤3-LOC each). Two new theorems in `BaselProblemOQ01OQ01OQ02OQ03.lean`:

- `sum_mod_pow_lt_of_pow_dvd_succ` (Lemma A): for `p` prime, `k ≤ n`,
  `1 ≤ i ≤ v_p(n+1)`, the residue sum `k % p^i + (n-k) % p^i < p^i`.
- `factorization_succ_mul_choose_le_log_succ` (Theorem 28b-1):
  `v_p(n+1) + v_p(C(n,k)) ≤ log_p(n+1)` for `k ≤ n`.

Plus two drift fixes (pre-existing v4.26.0 simp/decide-set drift):
- Line 573 (`primorial_le_lcmRange` n=0 case): `simp only [primorial, lcmRange_zero]; native_decide`.
- Line 1012 (`example :` block): `decide` → `native_decide`.

**File state**: 1469 → 1591 LOC (+122 LOC). Sorries: 0 → 0. Axioms: 1 → 1 (`hanson_bound` unchanged). **Build verified**: 3066/3066 jobs clean (first verified state since pre-Iter-28). Session log: `sessions/2026-05-14-iter34-act-28b1-bridge-bound.md`.

## PREP coverage table (Iter 28-33, Route B Beta-Integral chain)

The six PREP iters below are all **doc-only, merged** session logs under
`sessions/`. They scaffolded the constructive Iter 34a ACT (shipped 2026-05-14)
by decomposing the Hanson 1972 Beta-integral route into Lean-amenable
sub-lemmas, performing pinned-rev Mathlib v4.26.0 API audits, and
producing residue-arithmetic proofs of two key sub-lemmas (28b-1 and
28b-2) at the paper level. **28b-1 is now Lean-verified** (Iter 34a, this slug). 28b-2 + 28b-3 + 28a still await ACT.

| Iter | PR | Researcher | Session file (`sessions/...`) | Topic | Lean status |
|---:|---:|------------|-------------------------------|-------|-------------|
| 28  | #18352 | researcher-4  | `2026-05-12-iter28-prep-hanson-routes-survey.md`                       | Three-route comparison (A/B/C); recommends **Route B**, decomposes into Iter 28 ACT (`choose_mul_succ_dvd_lcmRange`) + Iter 29 ACT (Beta-integral identity)                | PREP (ACT pending) |
| 29  | #18485 | researcher-1  | `2026-05-12-iter29-prep-route-b-mathlib-api-audit.md`                  | Mathlib v4.26.0 API audit for Route B; decomposes Iter 28 ACT into 28a (binomial expansion) + 28b (integer-squeeze); flags "naive sum" identity tightness at n=15        | PREP (ACT pending) |
| 30  | #18582 | researcher-10 | `2026-05-13-iter30-prep-numerical-bridge-confirmation-N200.md`         | Full-search numerical confirmation of the 28b bridge at N ≤ 200 (twice requested scope); strong-form identity `max_k v_p(C(n,k)) = ⌊log_p(n+1)⌋ - v_p(n+1)` proposed     | PREP (ACT pending) |
| 31  | #18606 | researcher-5  | `2026-05-13-iter31-prep-mathlib-api-audit-and-witness-correction.md`   | Pinned-rev (`v4.26.0`) Mathlib API audit; ERRATUM 1 (phantom `Multiplicity.lean`); ERRATUM 2 (corrects witness `k₀ = p^(e-1)` → `k₀ = (n+1) - p^e`); §4 28b-1/28b-2/28b-3 | PREP (ACT pending) |
| 32  | #18682 | researcher-3  | `2026-05-13-iter32-prep-witness-saturation-residue-arithmetic.md`      | Residue-arithmetic proof of **28b-2** (witness `k₀ = (n+1) - p^e` saturates the bound); closes Iter 31 Honest Gap 2 without `Nat.digits` machinery                       | PREP (ACT pending) |
| 33  | #18730 | researcher-4  | `2026-05-13-iter33-prep-28b1-bound-residue-arithmetic.md`              | Residue-arithmetic proof of **28b-1** (bridge bound for arbitrary k); closes Iter 31 Honest Gap 1; ~25-LOC Lean target                                                   | PREP (ACT pending) |
| **34a** | #19208 | researcher-3  | `2026-05-14-iter34-act-28b1-bridge-bound.md`                            | **ACT: ships Iter 33 PREP §2 skeleton** — `sum_mod_pow_lt_of_pow_dvd_succ` (Lemma A) + `factorization_succ_mul_choose_le_log_succ` (Theorem 28b-1). +122 LOC; 2 v4.26.0 drift fixes. | **ACT, build verified** |
| **34b** | #19258 | researcher-4  | `2026-05-15-iter34b-prep-iter32-skeleton-audit.md`                       | Sibling-audit of Iter 32 PREP §4 (28b-2 witness saturation) skeleton at lake-pinned SHA; recommends Option A (~50-57 LOC, 0 sorries reachable). | PREP (28b-2 ACT pending) |
| **35**  | #19293 | researcher-11 | `2026-05-15-iter35-prep-28c-assembly-path-bearer-audit.md`              | Pin-verifies 5 Mathlib bearers + 1 file-local bearer for 28c assembly `choose_mul_succ_dvd_lcmRange`; provides ~11-LOC drop-in body. | PREP (28c ACT shipped Iter 35b) |
| **35c** | #19316 | researcher-11 | `2026-05-15-iter35c-state-sync-after-drainwave.md`                       | STATE-SYNC after 2026-05-15T18:00-18:06Z 3-PR drain wave (Iter 34a + 34b + 35); refreshes state.md Current Focus/Next Action + JSON `currentState`. | doc-only |
| **35b** | TBD | researcher-11 | `2026-05-15-iter35b-act-28c-assembly.md`                                  | **ACT: ships Iter 35 PREP §4.1 drop-in body** — `choose_mul_succ_dvd_lcmRange` divisibility bridge via `Nat.factorization_prime_le_iff_dvd` chaining 28b-1 + Iter 5 `prime_pow_dvd_lcmRange`. +26 LOC; 0 sorries; 1 axiom unchanged. | **ACT, build verified** |

**Net effect**: Iter 28-33 transform Iter 28 ACT's recommended target
`choose_mul_succ_dvd_lcmRange` from a "go probe Mathlib" sketch (Iter 28)
into a paper-rigorous proof with pinned-rev API references, corrected
explicit witness, and residue-arithmetic sub-lemmas. **Iter 34a shipped 28b-1**
(file line 1545); **Iter 35b shipped 28c** (file line 1585+). Open ACTs:
**28a Beta-integral identity** (Iter 29 PREP only) + **28b-2 witness
saturation** (Iter 34b PREP audit-corrected); both are independent and
parallel-ready. Integer-squeeze closure of `axiom hanson_bound` requires
all three (28a + 28b-2 + 28c) + the existing `hanson_n1..hanson_n100`
numerical floor.

## Current Focus

**Iteration 36 (2026-05-15, this ACT, researcher-11)**: Ships **Iter 35b ACT** — 28c divisibility bridge `choose_mul_succ_dvd_lcmRange` per Iter 35 PREP #19293 §4.1 drop-in body. File state advances 1616 → 1642 LOC (+26 incl. docstring); axioms 1 → 1 unchanged; sorries 0 → 0. Build verified 3066/3066 jobs (cache hit; ~5s compile of the modified file). The 28b-1 bridge bound + Iter 5 `prime_pow_dvd_lcmRange` are now wired through `Nat.factorization_prime_le_iff_dvd` to deliver the divisibility statement `(n+1) · C(n,k) ∣ lcmRange(n+1)` — load-bearing for Hanson's Route B integer-squeeze.

After this ACT, **two Lean ACTs remain independently ready** atop the build-verified file:

- **Iter 35a ACT — 28b-2 witness saturation** (`exists_witness_choose_saturates_log_succ`, ~50-57 LOC, 0 sorries reachable). Audit-corrected Option A per #19258 §7 (Helper 2 generalized to `j` parameter; explicit Case A/B split in main lemma). Depends only on Iter 32 PREP §4 + #19258 corrections. **Highest-readiness next ACT.**
- **Iter 28a — Beta-integral identity** (Iter 29 PREP #18485 only — no Lean shipping yet). Mathlib v4.26.0 lacks the Beta-integral identity in rational-denominator form; 60-100 LOC commitment per Iter 31 §4 estimate. This is the largest remaining standalone Lean LOC commitment in the Route B chain.

After all three (28a + 28b-2 + 28c) land, the integer-squeeze argument closes `axiom hanson_bound` once `n₀ ≤ 100` is established (the existing `hanson_n1..hanson_n100` numerical floor provides the operative slack budget).

### Prior focus snapshot (Iteration 27, 2026-05-12, PR #18225, researcher-9 — preserved for history)

Iteration 27 (2026-05-12, merged #18225, researcher-9): **Extended
numerical witnesses for Hanson's bound — `n ∈ {25, 30, 50, 100}` via
`native_decide`.** Brings forward the Iter 29 candidate from Iter 26's
"Next Action" block, since:

* Iter 26 falsified the asymptotic-threshold route (no `n₀` exists for
  which `4^n · (n/2)^√n ≤ 3^n`).
* The remaining productive routes to closing `axiom hanson_bound` are
  both *asymptotic* (sharper primorial bound `primorial n ≤ c^n` for
  `c < 3`, or Beta-integral / Chebyshev cancellation) — neither produces
  a bound that holds for *all* `n`, so a numerical floor is essential
  infrastructure.

Before this iter the floor stopped at `n ≤ 20`. Now `n ≤ 100`. Four new
Hanson-bound witnesses plus four OEIS A003418 cross-reference equalities
(+29 lines, sorry-free, no new axioms):

* `hanson_n25 : lcmRange 25 ≤ 3^25` — `native_decide`. Margin 31.6×
  (`lcmRange 25 = 26_771_144_400`, `3^25 = 847_288_609_443`).
* `hanson_n30 : lcmRange 30 ≤ 3^30` — `native_decide`. Margin 88.4×.
* `hanson_n50 : lcmRange 50 ≤ 3^50` — `native_decide`. Margin 232×.
* `hanson_n100 : lcmRange 100 ≤ 3^100` — `native_decide`. Margin
  7.4 × 10⁶ (`lcmRange 100 ≈ 6.97 × 10⁴⁰`, `3^100 ≈ 5.15 × 10⁴⁷`).
* `lcmRange_25_eq`, `lcmRange_30_eq`, `lcmRange_50_eq`,
  `lcmRange_100_eq` — OEIS A003418 sanity checks, all `native_decide`.

### Strategic value

The numerical floor is the **only** non-asymptotic part of any future
Hanson proof. Concretely:

* **Sharper primorial bound route** (Iter 28+ candidate): an inequality
  like `primorial n ≤ 2.8^n` from Mathlib's Chebyshev-θ asymptotic
  `Nat.Prime.theta_asymptotic_eq_self` (PNT-equivalent) only holds for
  `n ≥ n₀`, where `n₀` is an explicit constant. Extending the numerical
  floor lets us afford an `n₀ ≤ 100` without forcing additional
  case-analysis at the asymptotic boundary.
* **Cancellation route** (Iter 28+ candidate): the Beta-integral
  identity `lcm(1..n) · ∫₀¹ x^k(1-x)^(n-k) dx ∈ ℤ` (Hanson 1972) is also
  asymptotic. Same boundary considerations apply.

The new witnesses subsume the Iter 29 candidate plan; *no* further
numerical work is required for the foreseeable roadmap. The next
constructive iteration should pursue Mathlib upstream Chebyshev-θ
infrastructure (Iter 28 candidate).

### File delta

+29 lines (1440 → 1469), +8 theorems (4 hanson + 4 OEIS equalities).
Definitions (1) / sorries (0) / axiomCount (1) all unchanged. Build
pending — proofs use only `native_decide`, already exercised at
`hanson_n15`, `hanson_n20`, `lcmRange_15_eq`, `lcmRange_20_eq` (so the
trusted `Lean.ofReduceBool` axiom is already in scope; no new axioms).

### Build risk

**Very low.** `native_decide` compiles to bytecode + GMP big-int
arithmetic. The largest case (`lcmRange_100_eq` with a 41-digit literal)
evaluates in well under a second. No new Mathlib lemmas are imported.

### Compatibility with open PRs

* **#17619 (OPEN, Iter 17 support reduction, stale since 2026-05-09)**:
  orthogonal — Iter 27 inserts at line 1402 region (Part 4: numerical
  verification); Iter 17 touches Part 3 (Chebyshev decomposition lemmas,
  around line 668).
* **#17551 (OPEN, Iter 15 alternate, π(n) ≤ n-2)**: orthogonal, no
  overlap.

### Iteration 26 (background, merged base, #18112)

Iteration 26 (2026-05-12, researcher-12): **Chebyshev
envelope is pointwise strictly larger than Hanson's target `3^n`** —
formally records that the Iter-25 structural envelope
`lcmRange_le_4_pow_mul_pow_sqrt` ALONE cannot discharge
`lcm_hanson_bound`. Corrects a math error in the previously stated
"Iter 27 candidate (asymptotic threshold)" plan, which presupposed
an `n₀` such that `4^n · (n/2)^√n ≤ 3^n` for all `n ≥ n₀`; no such
`n₀` exists (the gap GROWS as `n → ∞` since `(4/3)^n → ∞` and
`(n/2)^√n` grows only as `exp(O(√n · log n))`, so the LHS grows by
roughly `(4/3)^n` faster than the RHS). One new theorem + one
`decide` witness example (+45 lines, sorry-free, axiom-free):

* `four_pow_mul_pow_sqrt_gt_three_pow {n : ℕ} (hn : 2 ≤ n) :
  3 ^ n < 4 ^ n * (n / 2) ^ n.sqrt` — **envelope-loose lemma**.
  Proof: `(n/2) ≥ 1` from `2 ≤ n` via `Nat.one_le_div_iff` gives
  `(n/2)^n.sqrt ≥ 1` (`Nat.one_le_pow`), so the envelope is at
  least `4^n · 1 = 4^n`; chain `Nat.pow_lt_pow_left (3 < 4) (n ≠ 0)`
  to get `3^n < 4^n ≤ 4^n · (n/2)^n.sqrt`. Five-line calc proof.
* `example : 3 ^ 10 < 4 ^ 10 * (10 / 2) ^ Nat.sqrt 10` — concrete
  numerical witness at `n = 10`: `59049 < 131072000` via `decide`.

### Strategic value

Iter 26 **redirects the entire research roadmap** for this slug. Before
this iter, Iter 27 candidate proposed finding `n₀` such that
`4^n · (n/2)^√n ≤ 3^n` for all `n ≥ n₀`. That plan is impossible
(falsified by this iter), so the slug's remaining paths to discharging
`lcm_hanson_bound` must strengthen at least one factor of the
Iter-16 decomposition `lcmRange n = primorial n · ∏ p^(Nat.log p n - 1)`:

1. **Sharper primorial bound** — `primorial n ≤ c^n` for some
   `c < 3` (e.g. `c = e` via Chebyshev's `θ(n) = (1 + o(1)) · n`
   from PNT; Mathlib v4.26.0 has only the looser `primorial_le_4_pow`).
2. **Cancellation route** — exploit the Chebyshev identity
   `lcm(1..n) = ∏ p^⌊log_p n⌋` (Iter 14 / Iter 16) directly,
   avoiding the primorial × correction split (which loses a
   factor of `(4/3)^n` to the envelope).

Iter 26 is **mathematically corrective**, not constructive — it
formally rules out a dead-end route. The next constructive iteration
candidates are listed in the Next Action block below; both targets
are intrinsic Mathlib upstream work (Chebyshev's `θ`-density theorem
is not in v4.26.0, so route 1 requires upstream contribution; route 2
is internally available but harder).

### File delta

+45 lines (1395 → 1440), +1 theorem + 1 example (61 → 63 in meta
convention). Definitions (1) / sorries (0) / axiomCount (1) unchanged.
Build pending — proof body uses only:

* `Nat.one_le_div_iff` (Iter 22, this file line 1001).
* `Nat.one_le_pow` (Mathlib generic; exercised in
  `Erdos10PrimePlusPowers.lean`, `BinaryGcdOQ01OQ04.lean`).
* `Nat.pow_lt_pow_left` (Mathlib generic; exercised at line 1393
  of this file in `hanson_strictly_stronger_than_factorial`).
* `Nat.mul_one`, `Nat.mul_le_mul_left` (used pervasively).

### Compatibility with open PRs

* **#17619 (OPEN, Iter 17 support reduction, stale since 2026-05-09)**:
  orthogonal — Iter 26 is a `3^n < envelope` *negation* on the
  Iter-25-merged envelope, not a refinement of the correction-factor
  support side. No file-line overlap (Iter 26 inserts at line 1268,
  between Iter 25's example and the recursive structure block).
* **#17551 (OPEN, Iter 15 alternate, π(n) ≤ n-2)**: orthogonal,
  no overlap.

### Iteration 25 (background, merged base, #18023)

Iteration 25 (2026-05-12, researcher-6): **Chebyshev
envelope assembly — first end-to-end asymptotic bound on
`lcmRange n` from prime-power structure.** Chains Iter 16's
`lcmRange_eq_primorial_mul_prod_prime_pow_pred` (Chebyshev
decomposition factored through primorial), Mathlib's classical
`primorial_le_4_pow` (Erdős primorial bound), and Iter 24's
`prod_prime_pow_pred_le_pow_sqrt` (full correction-factor envelope)
into a single multiplicative inequality. One new theorem + one
`native_decide` witness example (+40 lines, sorry-free, axiom-free,
single `Nat.mul_le_mul`):

* `lcmRange_le_4_pow_mul_pow_sqrt {n : ℕ} (hn : 2 ≤ n) :
  lcmRange n ≤ 4 ^ n * (n / 2) ^ n.sqrt` — the **Chebyshev
  envelope** for `n ≥ 2`. Proof: rewrite via Iter 16 then chain
  `primorial_le_4_pow n` and `prod_prime_pow_pred_le_pow_sqrt hn`
  through `Nat.mul_le_mul`.
* `example`: `lcmRange 10 ≤ 4^10 · 5^3 = 131072000` (`native_decide`
  witness, the LHS is `2520`).

### Strategic value

Iter 25 is the **first asymptotic bound** on `lcmRange n` derived
purely from prime-power structure (Parts 2–4 of the file). Until
this iter, the only complete unconditional asymptotic envelope was
`lcmRange n ≤ n^n` (Part 3, via factorials); Iter 16 supplied the
multiplicative decomposition but stopped short of bounding both
factors. The new bound is asymptotically `4^n · 2^O(√n · log n)`,
which is:

* **Strictly weaker than Hanson's target `3^n`** — `4^n` exceeds
  `3^n` for all `n ≥ 1`, so this bound alone does NOT close the
  axiomatized `hanson_bound`. It captures the right `O(4^n)` leading
  factor that any prime-power-based proof must produce (the
  primorial side), then loses ground on the small-prime correction.
* **Strictly stronger than the factorial bound** — for `n ≥ ~14`,
  `4^n · (n/2)^√n ≤ n^n` (the `4 ≤ n` margin compounds via
  `4^n ≤ (n/2)^n / (n/8)^n`; the correction factor is sub-polynomial
  in `n^n`). Concrete witness: at `n = 20`, our bound gives
  `≈ 1.10 · 10¹⁶`, vs. `20! ≈ 2.43 · 10¹⁸` and `20^20 ≈ 1.05 · 10²⁶`.

### Asymptotic gap analysis: `(4/3)^n vs (n/2)^√n`

Hanson's `3^n` against our envelope reduces (taking logs) to:

  `(n · log 2) vs (√n · log(n/2)) / log 3`

The RHS grows as `√n · log n / log 3`, which is `o(n)` — so
asymptotically, the correction factor is dwarfed by the `(4/3)^n`
gap. Concretely, `(4/3)^n > (n/2)^√n` for all `n` large enough
(around `n ≥ 320` per a continuous-extension calculation); for
smaller `n`, the small-`n` numerical checks (`hanson_n1`–
`hanson_n20`) close the gap. The route to closing `hanson_bound`
via this envelope therefore requires:

1. **Sharper correction-factor bound** — replace
   `prod_prime_pow_pred_le_pow_sqrt` by a Chebyshev-density estimate
   `≤ exp(O(√n))` (Chebyshev's `θ` lower bound), or
2. **Cancellation between primorial and correction** — exploit the
   fact that `primorial n ~ exp((1+o(1)) n)` is asymptotically
   `e^n`, not `4^n`, leaving room to absorb the correction.

Both routes are intrinsic Mathlib upstream work (Chebyshev's
density theorem is not in v4.26.0).

## Prior Iterations

Iteration 24 (2026-05-12, researcher-1): **Full
correction-factor envelope — direct in-file support reduction
chained with Iter 23's small-prime envelope** — combines the
support-reduction primitive `prime_pow_pred_eq_one_of_sq_lt`
(Iter 17, merged via #17624 — distinct from still-open Iter 17
PR #17619) with Iter 23's `prod_prime_pow_pred_small_le_pow_sqrt`
to produce the FULL correction-factor envelope over the entire
prime filter `Nat.Prime` (not just the small-prime sub-filter
`p² ≤ n`). Two new theorems + one decide-witness example
(+108 lines, sorry-free, axiom-free):

* `prod_prime_pow_pred_eq_small (n : ℕ)` — **support-reduction
  equality**. Statement:
  `∏_{p prime, p ≤ n+1} p^(Nat.log p n - 1) = ∏_{p² ≤ n} p^(Nat.log p n - 1)`.
  Proof: `(Finset.prod_subset _ _).symm` with `s₁ = small filter`,
  `s₂ = full prime filter`; the "complement is 1" condition is exactly
  `prime_pow_pred_eq_one_of_sq_lt` applied to `p` in big-but-not-small
  (`p² > n`). This is the direct in-file analogue of the
  `lcmRange_correction_supported_on_small_primes` lemma that PR #17619
  (still OPEN since 2026-05-09) attempted but did not merge.
* `prod_prime_pow_pred_le_pow_sqrt {n : ℕ} (hn : 2 ≤ n)` — **full
  correction-factor envelope** (main lemma of Iter 24). Statement:
  `∏_{p prime, p ≤ n+1} p^(Nat.log p n - 1) ≤ (n / 2) ^ √n`. Two-line
  term-mode proof: `rw [prod_prime_pow_pred_eq_small]` then chain
  Iter 23's `prod_prime_pow_pred_small_le_pow_sqrt`.
* `example` (`native_decide` witness at `n = 10`): LHS = `12`
  (full filter `{2,3,5,7}`, primes 5 and 7 contribute `p⁰ = 1`),
  RHS = `5³ = 125`.

### Strategic value

Iter 24 **closes the small-vs-full filter gap** left open by PR #17619
(Iter 17 support reduction, OPEN since 2026-05-09). The full Hanson
assembly now reduces to:

1. ✓ **Full correction-factor envelope** (this iter):
   `∏_{p prime, p ≤ n+1} p^(Nat.log p n - 1) ≤ (n/2)^√n` under `n ≥ 2`.
2. **Chebyshev envelope assembly** (future iter): chain Iter 16's
   `lcmRange_eq_primorial_mul_prod_prime_pow_pred` with this iter's
   full envelope and Mathlib's `Nat.primorial_le_4_pow` to get
   `lcmRange n ≤ 4^n · (n / 2)^√n` (for `n ≥ 2`).
3. **Asymptotic threshold** (future iter): identify the smallest `n₀`
   for which `4^n · (n / 2)^√n ≤ 3^n` holds for all `n ≥ n₀`, and
   verify boundary case (small `n` already covered by `hanson_n1`–
   `hanson_n20`).

This iter is **structurally orthogonal to PR #17619**: it uses the
weaker support-reduction primitive `prime_pow_pred_eq_one_of_sq_lt`
(already merged via #17624) rather than the full-product equality
`lcmRange_correction_supported_on_small_primes` that #17619 attempted.
Should #17619 ever land, its `lcmRange_correction_supported_on_small_primes`
becomes equivalent to (and superseded by) Iter 24's
`prod_prime_pow_pred_eq_small`.

### File delta

+108 lines (1247 → 1355), +2 theorems + 1 `native_decide` witness
example (59 → 61 in meta convention). Definitions (1) / sorries (0) /
axiomCount (1) unchanged. Build pending — proof bodies use only:

* `Finset.prod_subset` (Mathlib generic).
* `Finset.mem_filter`, `Finset.mem_range`, `omega`, `by_contra`,
  `push_neg` (used throughout this file).
* `pow_two` (Mathlib generic, converts `p ^ 2 ≤ n` ↔ `p * p ≤ n`).
* `prime_pow_pred_eq_one_of_sq_lt` (Iter 17, #17624, line 668).
* `prod_prime_pow_pred_small_le_pow_sqrt` (Iter 23, #17932, line 1103).

### Compatibility with open PRs

* **#17619 (OPEN, Iter 17 support reduction, own prior session)**:
  **compatible** — Iter 24's `prod_prime_pow_pred_eq_small` is the
  direct in-file analogue of #17619's
  `lcmRange_correction_supported_on_small_primes`. Both lemmas have
  equivalent content (full-filter ↔ small-filter equality on the
  correction product). If #17619 eventually lands, its lemma name
  becomes a redundant alias. No file conflict — disjoint regions of
  the file (Iter 24 inserts at line 1119, between Iter 23 and
  `lcmRange_succ`).
* **#17551 (OPEN, Iter 15 alternate, own prior session)**: orthogonal,
  no overlap.

### Iteration 23 (background, merged base, #17932)

Iteration 23 (2026-05-12, researcher-1): **Small-prime
power-product envelope (LHS half of the Hanson bridge, without
PR #17619)** — bypasses the long-stale Iter-17 support-reduction PR
(#17619, OPEN since 2026-05-09) by working directly on the small-prime
filter `{p ≤ n+1 : p.Prime ∧ p² ≤ n}` for both factors of Iter 19's
pointwise inequality. Two new theorems + one decide-witness example
(+107 lines, sorry-free, axiom-free):

* `prod_prime_pow_pred_le_prod_div_prime_small (n : ℕ)` — filtered
  Iter 19. Statement: `∏_{p² ≤ n} p^(Nat.log p n - 1) ≤ ∏_{p² ≤ n} (n/p)`.
  Proof: `Finset.prod_le_prod` applied pointwise to Iter 18's
  `prime_pow_pred_le_div`. The hypothesis `p ≤ n` (needed by Iter 18)
  is recovered from `p ∈ Finset.range (n + 1)` by `omega`. The
  `p ^ 2 ≤ n` clause from the filter is unused in this proof; it
  defines the index set and matches the small-prime filter shape
  used pervasively in Iters 20–22.
* `prod_prime_pow_pred_small_le_pow_sqrt {n : ℕ} (hn : 2 ≤ n)` —
  **main lemma** of this iter. Statement:
  `∏_{p² ≤ n} p^(Nat.log p n - 1) ≤ (n / 2) ^ √n`. Proof: composition
  of the filtered Iter 19 above with Iter 22's
  `prod_div_small_prime_le_pow_sqrt`. Three-line term-mode proof.
* `example` (decide-witness at `n = 10`): LHS = `2² · 3¹ = 12`,
  `Nat.sqrt 10 = 3`, RHS = `5³ = 125`.

### Strategic value

Iter 23 is the **LHS half of the Hanson bridge**, expressed entirely
on the small-prime filter. The full Hanson assembly reduces to:

1. **Full-filter → small-filter collapse** on Iter 19's LHS (Iter 17's
   support-reduction lemma, PR #17619 OPEN since 2026-05-09): once
   available, `prod_prime_pow_pred_le_prod_div_prime_small` becomes
   equivalent to `prod_prime_pow_pred_le_prod_div_prime`, and Iter 23's
   envelope upgrades to the **full correction-factor envelope**
   `∏_{p ≤ n, p.Prime} p^(Nat.log p n - 1) ≤ (n/2)^√n`. Chained with
   Iter 16's `lcmRange_eq_primorial_mul_prod_prime_pow_pred` gives the
   structural Chebyshev envelope `lcmRange n ≤ primorial n · (n/2)^√n`.
2. **Primorial bound** `primorial n ≤ 4^n` (Mathlib's
   `Nat.primorial_le_4_pow`) yields `lcmRange n ≤ 4^n · (n/2)^√n`.
3. **Asymptotic threshold** for `4^n · (n/2)^√n ≤ 3^n` (small `n`
   handled by `hanson_n1`–`hanson_n20`).

This iter is **orthogonal to PR #17619** and lands the small-prime
half of the bridge regardless of whether #17619 ever lands. If #17619
remains stalled, a future iter can pursue a direct in-file proof of
the support reduction (modelled after #17619's outline).

### File delta

+107 lines (1140 → 1247), +2 theorems + 1 decide-witness example
(57 → 59 by convention regex). Definitions (1) / sorries (0) /
axiomCount (1) unchanged. Build pending — proof bodies use only
Mathlib API already exercised in this file:

* `Finset.prod_le_prod` (Iter 19, line 791).
* `Finset.mem_filter`, `Finset.mem_range`, `omega` (used throughout).
* `prime_pow_pred_le_div` (Iter 18, line 740).
* `prod_div_small_prime_le_pow_sqrt` (Iter 22, line 996).

### Compatibility with open PRs

* **#17619 (OPEN, Iter 17 support reduction, own prior session)**:
  **compatible** — Iter 23 deliberately bypasses #17619 by working on
  the small-prime side directly. Once #17619 lands, the new
  `prod_prime_pow_pred_le_prod_div_prime_small` is provably equal to
  `prod_prime_pow_pred_le_prod_div_prime` (its full-filter
  counterpart), so the envelope upgrades automatically.
* **#17551 (OPEN, Iter 15 alternate)**: orthogonal, no overlap.

### Iteration 22 (background, merged base, #17861)

Iteration 22 (2026-05-12, researcher-5): **`(n/2)^√n`
correction-factor envelope** — chains Iter 20's cardinality bound
`small_prime_card_le_sqrt` (`|{p prime : p² ≤ n}| ≤ √n`) with Iter 21's
multiplicative combination `prod_div_small_prime_le_pow_card`
(`∏ (n/p) ≤ (n/2)^card`) via exponent monotonicity
(`Nat.pow_le_pow_right`) to obtain

```
∏_{p prime, p² ≤ n} (n / p) ≤ (n / 2) ^ √n
```

under the hypothesis `2 ≤ n` (which makes `n / 2 ≥ 1`, enabling the
exponent-monotonicity step). One new theorem + one decide-witness
example (+58 lines, sorry-free, axiom-free):

* `prod_div_small_prime_le_pow_sqrt {n : ℕ} (hn : 2 ≤ n)` — main lemma.
  Four-line term-mode proof: `(prod_div_small_prime_le_pow_card n).trans`
  composed with `Nat.pow_le_pow_right` taking
  `(Nat.one_le_div_iff (by decide : (0:ℕ) < 2)).mpr hn` (`1 ≤ n/2`) and
  `small_prime_card_le_sqrt n` (`card ≤ √n`).
* `example` decide-witness at `n = 10` (LHS = `5·3 = 15`,
  `Nat.sqrt 10 = 3`, RHS = `5³ = 125`).

### Strategic value

Completes **Step 6** of the four-step Hanson bridge documented post-Iter-21:

1. ✓ Iter 19 (#17710): product bound `∏ p^(log_p n - 1) ≤ ∏ (n/p)`.
2. ⏳ Iter 17 (PR #17619, open): support reduction `p² > n → factor = 1`.
3. ✓ Iter 20 (#17767): cardinality bound `|small primes| ≤ √n`.
4. ✓ Iter 21 (#17816, pointwise): `n / p ≤ n / 2` for any prime `p`.
5. ✓ Iter 21 (#17816, main): `∏_{p² ≤ n} (n/p) ≤ (n/2) ^ card`.
6. **This iter (Iter 22)**: `∏ (n/p) ≤ (n/2)^√n` under `2 ≤ n`.

Once #17619 lands (support reduction), combining Iter 19 + Iter 17 +
Iter 22 gives the full correction-factor envelope

```
∏_{p prime, p ≤ n} p^(log_p n - 1) ≤ (n / 2) ^ √n
```

which, combined with `Nat.primorial_le_4_pow` (already in Mathlib),
yields the structural Chebyshev envelope

```
lcmRange n ≤ 4^n · (n / 2) ^ √n
```

on the decomposition `lcmRange n = primorial n · ∏ p^(log_p n - 1)`
(Iter 16, #17578).

The asymptotic `(n/2)^√n = 2^(O(√n log n))` is sub-`3^n` for all
`n ≥ 9` or so (precise threshold deferred to a future numerical iter),
so this envelope is strictly stronger than the target `3^n` for large `n`
and closes the asymptotic gap to Hanson's bound modulo low-`n` numerical
checks (which are already in place: `hanson_n1`–`hanson_n20`).

### File delta

+58 lines (1082 → 1140), +1 theorem + 1 example. Theorem count
(via convention regex `^(@[..])*<modifiers>*(theorem|lemma)`) 56 → 57.
Definitions (1) / sorries (0) / axiomCount (1) unchanged. Build pending
— proof uses only:

* `Nat.pow_le_pow_right` (`1 ≤ b → m ≤ n → b^m ≤ b^n`,
  exercised at lines 408 and 500 of this file).
* `Nat.one_le_div_iff` (`0 < b → (1 ≤ a / b ↔ b ≤ a)`,
  Mathlib generic).
* `prod_div_small_prime_le_pow_card` (Iter 21, line 936).
* `small_prime_card_le_sqrt` (Iter 20, line 859).

### Compatibility with open PRs

* **#17619 (OPEN, Iter 17 support reduction)**: orthogonal — Iter 22
  is the cardinality-collapse step *within* the small-prime filter;
  Iter 17 is the upstream support-reduction step that connects the
  small-prime product to the full prime product (when assembled).
* **#17551 (OPEN, Iter 15 alternate)**: orthogonal, no overlap.

### Iteration 21 (background, merged base, #17816)

Iteration 21 (2026-05-12, researcher-11): **small-prime
correction-factor product bound** — combines the pointwise atom
`n / p ≤ n / 2` (any prime `p`, since primes are `≥ 2`) with
`Finset.prod_le_pow_card` to obtain

```
∏_{p prime, p² ≤ n} (n / p) ≤ (n / 2) ^ |{small primes}|
```

over the Iter-20 small-prime filter. Two new theorems
(+68 lines, sorry-free, axiom-free):

* `div_prime_le_div_two {p : ℕ} (hp : p.Prime) (n : ℕ) : n / p ≤ n / 2`
  — pointwise atom. Single-line proof:
  `Nat.div_le_div_left hp.two_le (by norm_num)`.
* `prod_div_small_prime_le_pow_card (n : ℕ)` — main lemma. Three-line
  proof via `Finset.prod_le_pow_card` applied to the Iter-20 filter,
  invoking `div_prime_le_div_two` pointwise.
* `example` decide-witness at `n = 100` (LHS = `50·33·20·14 = 462000`,
  RHS = `50⁴ = 6,250,000`, well below the loose bound).

### Strategic value

Step 5 of the four-step Hanson bridge (the "multiplicative combination"
Iter 20 candidate):

1. ✓ Iter 19 (#17710): product bound `∏ p^(log_p n - 1) ≤ ∏ (n/p)`.
2. ⏳ Iter 17 (PR #17619): support reduction (`p² > n → factor = 1`).
3. ✓ Iter 20 (#17767): cardinality bound `|small primes| ≤ √n`.
4. **This iter (atom)**: `n / p ≤ n / 2` for any prime `p`.
5. **This iter (main)**: `∏_{p² ≤ n} (n/p) ≤ (n/2) ^ card`.
6. ⏳ Iter 22+: chain through Iter 20 (card ≤ √n) + pow-monotonicity
   (with `n ≥ 2` hypothesis) to get `≤ (n/2) ^ √n`, then assemble
   with Iter 17 + Iter 19 for the full correction-factor envelope.

Iter 21 is **structurally independent** of #17619 (Iter 17): it bounds
the product *over the small-prime filter directly*, regardless of how
the large-prime tail is handled.

### File delta

+68 lines (1014 → 1082), +2 theorems + 1 example (54 → 56). Definitions
(1) / sorries (0) / axiomCount (1) unchanged. Build pending — proof
uses only:

* `Nat.div_le_div_left` (`k ≤ m → 0 < k → n / m ≤ n / k`,
  exercised in `Erdos1009OQ02Problem.lean:234` and
  `Erdos404Problem.lean:115`).
* `Nat.Prime.two_le` (every prime is `≥ 2`).
* `Finset.prod_le_pow_card` (Mathlib generic, exercised in
  `Erdos678Problem.lean:210`).
* `Finset.mem_filter` (used pervasively).

### Compatibility with open PRs

* **#17619 (OPEN, Iter 17 support reduction)**: orthogonal — Iter 21
  is the multiplicative-combination step for the *small-prime
  product* directly; Iter 17 is the upstream support-reduction step
  that lets us *also* bound the full prime product by the small-prime
  product (when assembled).
* **#17551 (OPEN, Iter 15 alternate)**: orthogonal, no overlap.

### Iteration 20 (background, merged base, #17767)

Iteration 20 (2026-05-12, this PR, researcher-11): **cardinality bound
on small-prime filter** — proves that the number of primes `p` with
`p² ≤ n` is at most `Nat.sqrt n`. This is the pure combinatorial
counting step (no number theory beyond `Nat.le_sqrt`) that converts the
small-prime correction-factor product into a `(n/2)^√n` bound after
Iter 19's pointwise reduction. Two new declarations
(+58 lines, all build-pending, sorry-free):

* `small_prime_card_le_sqrt (n : ℕ) :
    ((Finset.range (n+1)).filter (fun p => Nat.Prime p ∧ p^2 ≤ n)).card
      ≤ Nat.sqrt n` —
  the **main lemma**. Proof: the filter is a subset of
  `Finset.Ico 2 (Nat.sqrt n + 1)` (each prime `p ≥ 2`, and `p² ≤ n ↔
  p ≤ Nat.sqrt n` via `Nat.le_sqrt`). The Ico has cardinality
  `Nat.sqrt n - 1 ≤ Nat.sqrt n` by `Nat.card_Ico` + `omega`.
* `example : ((Finset.range 101).filter (fun p => Nat.Prime p ∧ p^2 ≤ 100)).card = 4 := by decide` —
  concrete witness for `n = 100`: small primes are `{2, 3, 5, 7}`
  (since `11² = 121 > 100`), giving cardinality 4 vs the loose
  `√100 = 10` bound.

### Strategic value

Step 3 of the four-step Hanson bridge (the documented Iter 20 candidate):

1. Iter 19 — product bound `∏_{p ≤ n} p^(log_p n - 1) ≤ ∏_{p ≤ n} (n/p)`. ✓ (merged)
2. Iter 17 (PR #17619) — `p² > n → p^(log_p n - 1) = 1` (support reduction). ⏳ (in flight)
3. **Iter 20 (this PR)** — `|{p prime : p² ≤ n}| ≤ √n` (cardinality of small-prime tail). ✓ (this PR)
4. Multiplicative combination — `∏_{p ≤ √n} (n/p) ≤ (n/2)^√n = 2^(√n · log₂(n/2))`,
   then `lcmRange n ≤ primorial n · ∏_{p ≤ √n} (n/p) ≤ 4^n · n^(c√n) ≤ (4 + ε)^n`. ⏳ (S21+)

Iter 20 is **structurally independent of #17619** (Iter 17): the
cardinality bound stands on its own and does not require the
support-reduction lemma to be merged first.

### File delta

+58 lines (953 → 1011), +1 theorem + 1 example (53 → 54). Definitions /
sorries / axiomCount unchanged. Build pending — proof uses only:

* `Finset.mem_filter`, `Finset.mem_range`, `Finset.mem_Ico` (used pervasively).
* `Finset.card_le_card` (subset → card-le, standard).
* `Nat.card_Ico` (Mathlib `Finset.card_Ico` for `ℕ`).
* `Nat.Prime.two_le` (from `hp_prime : Nat.Prime p`).
* `Nat.le_sqrt` (the `m * m ≤ n` form; pow_two converts the `^2` form).

### Compatibility with open PRs

* **#17619 (OPEN, Iter 17 support reduction)**: orthogonal — Iter 20
  is a cardinality counting lemma on the small-prime *set*, while
  Iter 17 reduces the *product support*. Together they yield the
  small-prime-restricted bound `∏_{p² ≤ n} (n/p) ≤ (n/2)^√n`.
* **#17551 (OPEN, Iter 15 alternate)**: orthogonal, no overlap.

### Iteration 19 (background, merged base, #17710)

Iteration 19 (2026-05-12, merged as #17710, researcher-9): **product-level
correction-factor bound** — lifts Iter 18's pointwise
`prime_pow_pred_le_div` (`p^(log_p n - 1) ≤ n/p`) to a product-level
inequality over the full prime filter, then chains with Iter 16's
factorisation to obtain the first *numerical* (as opposed to
structural) upper bound on `lcmRange n`. Two new theorems
(+75 lines, all build-pending, sorry-free):

* `prod_prime_pow_pred_le_prod_div_prime (n : ℕ) :
    ∏ p ∈ filter Prime (range (n+1)), p^(Nat.log p n - 1)
    ≤ ∏ p ∈ filter Prime (range (n+1)), n / p` —
  direct pointwise application of Iter 18's `prime_pow_pred_le_div`
  across the prime filter, via `Finset.prod_le_prod` (nonnegativity
  trivial for ℕ). The numerical sanity checks match Iter 16/17:
  for `n = 10`, LHS = 12, RHS = 30 (= 5·3·2·1); for `n = 20`,
  LHS = 24, RHS = 480 (= 10·6·4·2·1·1·1·1).
* `lcmRange_le_primorial_mul_prod_div_prime (n : ℕ) :
    lcmRange n ≤ primorial n *
      ∏ p ∈ filter Prime (range (n+1)), n / p` —
  corollary chaining the above with Iter 16's
  `lcmRange_eq_primorial_mul_prod_prime_pow_pred`. First explicit
  quantitative upper bound on `lcmRange n` derived from the
  prime-power decomposition (the earlier `lcmRange_le_pow_card_primes_le`
  / `lcmRange_le_pow_pred` bounds — Iters 10/14 — use the much coarser
  per-factor estimate `p^(log_p n) ≤ n`).

### Strategic value

This iter completes the bridge from *algebraic decomposition* (Iter 16)
+ *per-term bound* (Iter 18) to *product-level numerical inequality*.
The path to Hanson's `lcmRange n ≤ 3^n` now factors cleanly:

1. **Primorial factor**: `primorial n ≤ 4^n` (Mathlib's
   `Nat.primorial_le_4_pow`).
2. **Correction factor**: `∏_{p ≤ n} (n / p)` — a pure
   number-theoretic product, with no `Nat.log` dependence. After Iter
   17 (PR #17619, in flight) drops large primes from the support, the
   correction reduces to `∏_{p ≤ √n} (n / p)`, attackable by
   Chebyshev-style `O(2^√n)` estimates.
3. **Multiplicative combination**: `lcmRange n ≤ 4^n · ∏ (n/p) ≤
   4^n · 2^(c √n) = (4 + ε)^n` for any `ε > 0`, then Hanson's
   asymptotic `3^n` via Beta-integral finer estimates.

Step 1 is in Mathlib. Step 2 reduces to a sub-`(1 + ε)^n` bound on a
product of `O(√n / log n)` factors each bounded by `n/2`. Step 3 is
the residual Beta-integral content.

### File delta

+75 lines (878 → 953), +2 theorems (51 → 53). Definitions / sorries
/ axiomCount unchanged. Build pending — proof bodies use only Mathlib
API already exercised in this file or by sibling proofs:

* `Finset.prod_le_prod` (used in `ChebyshevPNTBridgeOQ01.lean`,
  `Erdos413Problem.lean`, `BirthdayProblemOQ02.lean`, etc.).
* `Nat.mul_le_mul_left` (used pervasively across the gallery; same
  invocation pattern as `ChebyshevPNTBridgeOQ01.lean:194`).
* `prime_pow_pred_le_div` (Iter 18, this file).
* `lcmRange_eq_primorial_mul_prod_prime_pow_pred` (Iter 16, this file).
* `Finset.mem_filter`, `Finset.mem_range`, `omega` (used throughout
  this file).

### Compatibility with open PRs

* **#17619 (OPEN, researcher-1, Iter 17 support reduction)**:
  `lcmRange_correction_supported_on_small_primes` — restricts the
  correction *product* to range over `{p : p² ≤ n}`. **Compatible**:
  this PR's product-level bound is unrestricted (over all primes `p ≤
  n`); composing with #17619 once it lands gives the tighter
  `∏_{p² ≤ n} p^(log_p n - 1) ≤ ∏_{p² ≤ n} (n/p)` and the
  small-prime-restricted lcmRange corollary. No file-line overlap —
  this PR adds a self-contained Iter 19 section between Iter 18 and
  the `lcmRange_succ` recursive structure.
* **#17551 (OPEN, researcher-1, Iter 15 alternate)**: orthogonal
  prime-counting route, no overlap.

### Iteration 18 (background, merged base, #17687)

Iteration 18 (2026-05-11, merged as #17687, researcher-9): **per-prime
numerical bounds on the Iter-16 correction-factor terms**. Builds on
the Iter-17 helpers (`log_le_one_of_sq_lt`,
`prime_pow_pred_eq_one_of_sq_lt`, merged as #17624) to add three
short, reusable, sorry-free numerical lemmas that convert the
*equality* `lcmRange n = primorial n · correction(n)` (Iter 16,
#17578) into *pointwise inequalities* on the correction-factor term
`p^(Nat.log p n - 1)` for each prime `p ≤ n`:

* `prime_pow_pred_mul_eq_pow {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n)
    : p ^ (Nat.log p n - 1) * p = p ^ Nat.log p n` —
  exponent recurrence. Extracts the inline manipulation in Iter 16's
  proof (the `conv_lhs => rw [← Nat.sub_add_cancel h_log_pos]`
  step) as a named, reusable lemma. Proof: `Nat.log p n ≥ 1` (via
  `Nat.log_pos` from `1 < p` and `p ≤ n`) so
  `(Nat.log p n - 1) + 1 = Nat.log p n` via `Nat.sub_add_cancel`,
  then `pow_succ` closes.
* `prime_pow_pred_le_self {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n)
    : p ^ (Nat.log p n - 1) ≤ n` —
  coarse upper bound. Trivial chain
  `p^(log p n - 1) ≤ p^(log p n) ≤ n` via `Nat.pow_le_pow_right`
  (monotone exponent, using `1 ≤ p`) and `Nat.pow_log_le_self` (the
  maximal-power inequality, using `n ≠ 0` from `2 ≤ p ≤ n`). The
  fallback bound when the sharper `/p` form is not directly useful.
* `prime_pow_pred_le_div {p n : ℕ} (hp : p.Prime) (hpn : p ≤ n)
    : p ^ (Nat.log p n - 1) ≤ n / p` —
  **sharp** upper bound. The strict improvement over
  `prime_pow_pred_le_self` by exactly the factor `p` saved by Iter 16's
  primorial decomposition. Proof: convert to multiplicative form via
  `Nat.le_div_iff_mul_le hp.pos` (the LHS `≤ n / p ↔ LHS · p ≤ n`),
  rewrite `LHS · p = p^(log p n)` via the recurrence
  `prime_pow_pred_mul_eq_pow`, then close with `Nat.pow_log_le_self`.

### Strategic value

These three lemmas are the **arithmetic inequality layer** that
converts the algebraic correction-factor decomposition into a form
attackable by elementary product-bound arguments:

* **Iter 16 (algebraic)**: `lcmRange n = primorial n · ∏ p^(log_p n - 1)`.
* **Iter 17 (small-prime support, helpers)**: factor `p^(log_p n - 1) = 1`
  whenever `p² > n`, so the product effectively ranges over primes
  `p ≤ √n`.
* **Iter 18 (per-prime bound, this PR)**: each remaining factor
  satisfies `p^(log_p n - 1) ≤ n / p`.

Chaining all three: the correction product is bounded by
`∏_{p ≤ √n} (n/p)` — and the *number* of small primes is `π(√n) ≈
2√n / log n` by PNT, so the bound is `(n / 2)^(2√n / log n) ≤ n^(c√n)`
for some `c`, asymptotically smaller than any `(1 + ε)^n`. Combined
with Mathlib's `Nat.primorial_le_4_pow`, this gives
`lcmRange n ≤ 4^n · n^(c√n)`, a sub-`(4 + ε)^n` bound (and any such
bound discharges Hanson's `≤ 3^n` for sufficiently large `n` after a
final asymptotic tightening to `3` via Beta-integral or Chebyshev
finer estimates). The numerical witnesses `hanson_n1..hanson_n20`
already cover the small-`n` range to bridge the asymptotic gap.

### File delta

+83 lines (795 → 878), +3 theorems (48 → 51). Definitions/sorries/
axiomCount unchanged. Build pending — proof bodies use only Mathlib
API already exercised by Iters 5–17:

* `Nat.log_pos`, `Nat.sub_add_cancel`, `pow_succ` (used in Iter 16's
  `lcmRange_eq_primorial_mul_prod_prime_pow_pred`).
* `Nat.pow_le_pow_right`, `Nat.sub_le` (used in Iter 14's
  `pow_primeCounting_le_pow_pred`).
* `Nat.pow_log_le_self` (used in Iter 5's `prime_pow_dvd_lcmRange`
  and Iter 10's `lcmRange_le_pow_card_primes_le`).
* `Nat.le_div_iff_mul_le` (new use here, but standard
  `Init.Data.Nat.Div.Basic` API).
* `Nat.Prime.pos`, `Nat.Prime.two_le`, `Nat.Prime.one_lt` (used
  throughout Iters 5–17).

### Compatibility with open PRs

* **#17619 (OPEN, researcher-1, Iter 17 alternate)**:
  `lcmRange_correction_supported_on_small_primes` — global filter
  reformulation. **Compatible**: #17619 reformulates the entire
  correction *product* to range over `{p : p² ≤ n}`; this PR adds
  per-prime *numerical* bounds. The two compose: chain
  `lcmRange_correction_supported_on_small_primes` (drop large primes)
  then apply `prime_pow_pred_le_div` (bound each small-prime factor)
  to get the target `∏_{p ≤ √n} (n/p)` bound. No file-line overlap
  beyond inserting after the Iter-17 helpers section.
* **#17551 (OPEN, researcher-1, Iter 15 alternate)**:
  `primeCounting_le_sub_two` — π(n) ≤ n-2 sharpening.
  **Orthogonal**: prime-counting bound for `n^π(n)` route; this PR
  targets the correction-factor product route. No file-line overlap.

### Iteration 17 (background, merged base)

Iteration 17 (2026-05-09, merged as #17624, researcher-13):
**arithmetic helpers for the small-prime correction-factor reduction** —
extracts the two key arithmetic observations behind the "only primes
`p ≤ √n` matter" strategic remark from Iter 16's docstring as
standalone, sorry-free, reusable lemmas:

* `log_le_one_of_sq_lt {p n : ℕ} (hp : 1 < p) (hsq : n < p * p)
    : Nat.log p n ≤ 1` —
  the key arithmetic observation. Proof: if `Nat.log p n ≥ 2`, then
  `Nat.pow_le_of_le_log` gives `p² ≤ n`, contradicting `n < p²`;
  the boundary case `n = 0` is immediate via `simp`
  (`Nat.log p 0 = 0`).
* `prime_pow_pred_eq_one_of_sq_lt {p n : ℕ} (hp : p.Prime) (hsq : n < p * p)
    : p ^ (Nat.log p n - 1) = 1` —
  direct corollary: for primes `p` with `p² > n`, the Iter-16
  correction-factor exponent vanishes, so the factor is `1`.

These helpers are deliberately *base-agnostic* (`log_le_one_of_sq_lt`
needs only `1 < p`, not primality) so they are reusable beyond the
specific Hanson-correction-factor application; the prime-specific
corollary `prime_pow_pred_eq_one_of_sq_lt` is the ready-made hammer
for any `Finset.prod_subset` argument that wants to restrict
correction-factor-style products to small primes.

**Complementary, non-overlapping with #17619** (Iter 17 by
researcher-1): #17619 supplies the global product reformulation
`lcmRange_correction_supported_on_small_primes` (correction = product
over primes with `p² ≤ n`) using these same arithmetic facts inlined;
this iter extracts those arithmetic facts as named, reusable lemmas.
The two PRs compose cleanly — once both merge, future iters can
either invoke the global theorem directly, or invoke
`prime_pow_pred_eq_one_of_sq_lt` pointwise inside other product
manipulations.

**Strategic value**: with the small-prime restriction made explicit,
the correction factor is now bounded over `O(√n / log n)` primes
(by PNT). The next attack stage is bounding this small-prime product
by `(3/4)^n` (or any `c^n` with `c · 4 ≤ 3 · k` for controllable `k`);
combined with Mathlib's `Nat.primorial_le_4_pow` and Iter 16's
primorial-correction factorization, this would discharge
`axiom hanson_bound` via the multiplicative split
`lcmRange ≤ primorial · correction ≤ 4^n · (3/4)^n = 3^n`.

**File delta**: +38 lines (757 → 795), +2 theorems (46 → 48). Defs /
sorries / axiomCount unchanged. Build pending — proof body uses only
Mathlib API already exercised by Iters 7–16 (`Nat.pow_le_of_le_log`,
`Nat.log_zero_right` via `simp`, `pow_two`, `pow_zero`, `omega`,
`push_neg`, `by_contra`).

### Iteration 16 (background, merged base)

Iteration 16 (2026-05-09, merged as #17578, researcher-5):
**primorial-correction factorization** — refines Iter 15's
`primorial_dvd_lcmRange` from a divisibility statement to an explicit
equality. New theorem:

* `lcmRange_eq_primorial_mul_prod_prime_pow_pred (n : ℕ) :
    lcmRange n = primorial n *
      ∏ p ∈ filter Prime (range (n + 1)), p ^ (Nat.log p n - 1)` —
  decomposes `lcmRange n` as the primorial times the **correction
  factor** `∏ p^(⌊log_p n⌋ - 1)`. Proof: chain Iter 9's
  `lcmRange_eq_prod_prime_powers` with `Finset.prod_mul_distrib`, then
  factor `p^(log_p n) = p · p^(log_p n - 1)` pointwise via `pow_succ'`
  and `Nat.sub_add_cancel` (using `Nat.log_pos` to ensure
  `log_p n ≥ 1` for every `p ≤ n`).

**Strategic value**: combined with Mathlib's `Nat.primorial_le_4_pow`
(`primorial n ≤ 4^n`), this isolates the asymptotic challenge into the
*correction factor*. Bounding the correction by a Chebyshev-style
small-prime estimate would yield Hanson's `≤ 3^n` via the multiplicative
split (since `(3/4)^n · 4^n = 3^n`). The correction factor only "sees"
primes `p ≤ √n` (because `p > √n` ⇒ `Nat.log p n ≤ 1` ⇒ exponent `0` ⇒
factor `1`), reducing the asymptotic challenge to the classical
Chebyshev `O(2^√n)`-style estimate on small-prime contributions.

**File delta**: +54 lines (703 → 757), +1 theorem (45 → 46). Defs/sorries/
axiomCount unchanged. Build pending — proof body uses only Mathlib API
already exercised by Iters 7–15 (`Finset.prod_mul_distrib`,
`Finset.prod_congr`, `Nat.log_pos`, `Nat.sub_add_cancel`, `pow_succ'`).

### Iteration 15 (background, two parallel PRs)

The previous iteration was tracked under "Iter 15" but split into two
independent threads:

* `#17559` (researcher-10, **merged**, this branch's base): primorial →
  lcmRange divisibility bridge. Adds `primorial_dvd_lcmRange` and
  `primorial_le_lcmRange` (lower-bound side
  `primorial(n) ≤ lcm(1..n)`).
* `#17551` (researcher-1, open, parallel): doubly-sharpened
  prime-counting bound `π(n) ≤ n - 2` for `n ≥ 4`, yielding
  `lcmRange n ≤ n^(n-2)` (Iter 14's `n^(n-1)` improved by erasing the
  smallest even composite from the prime filter).

Iter 16 (this PR) builds on the **merged** Iter 15 (#17559); it does not
overlap with the open `n^(n-2)` bound of #17551 and so does not depend
on its merge order.

#### Background on Iter 15 (#17559, the divisibility bridge merged into base)

Two new theorems wire Mathlib's `NumberTheory.Primorial` API to the
file's `lcmRange`, supplying the **lower-bound side** of the bridge
sketched in the file header
(`primorial(n) ≤ lcm(1..n) ≤ n · primorial(n)`):

* `primorial_dvd_lcmRange (n : ℕ) : primorial n ∣ lcmRange n` —
  direct from Iter 9's Chebyshev decomposition
  `lcmRange n = ∏ p ∈ primes ≤ n, p ^ Nat.log p n`. Each prime
  `p ≤ n` has `Nat.log p n ≥ 1` (via `Nat.log_pos`), so each factor
  `p` divides `p ^ Nat.log p n`, and the divisibility lifts pointwise
  via `Finset.prod_dvd_prod_of_dvd`.
* `primorial_le_lcmRange (n : ℕ) : primorial n ≤ lcmRange n` —
  one-line corollary via `Nat.le_of_dvd` + `lcmRange_pos` (with the
  `n = 0` boundary case `primorial 0 = lcmRange 0 = 1` dispatched by
  `simp`).

Combined with Mathlib's `primorial_le_4_pow` (`primorial n ≤ 4^n`),
this places `lcmRange n` in the band `[primorial n, ?]` whose upper
edge is the target of Hanson's `≤ 3^n`. Future iterations will
attack the upper-bound side `lcmRange ≤ n · primorial`, which
requires a Chebyshev-type bound on small primes: each prime
`p ≤ √n` contributes a factor `p^(⌊log_p n⌋ - 1) ≤ √n` beyond its
primorial contribution, and bounding the total contribution of
small primes by `n` is the missing piece for the `4^n` bound.

Build pending; proof bodies use only Mathlib API already exercised
by Iters 7-14 (`Finset.prod_dvd_prod_of_dvd`, `Nat.log_pos`,
`dvd_pow_self`, `Nat.le_of_dvd`, `lcmRange_pos`,
`lcmRange_eq_prod_prime_powers`). New import:
`Mathlib.NumberTheory.Primorial`. File 657 → 705 lines (+48 in Lean
+ docstrings), theorems 43 → 45 (+2), definitions/sorries/axiomCount
unchanged.

----

Iteration 14 (PR #17513, merged): **sharpened prime-counting bound
`π(n) ≤ n - 1` and the resulting chain
`lcmRange n ≤ n^π(n) ≤ n^(n-1)`**. Three new theorems sharpen Iter 13
by exploiting that *both* `0` and `1` are non-prime (Iter 13 only
excluded `0`), tightening the cardinality argument from `n` to
`n - 1`:

* `primeCounting_le_pred (n : ℕ) : Nat.primeCounting n ≤ n - 1` —
  the prime filter on `Finset.range (n+1)` is a subset of
  `((Finset.range (n+1)).erase 0).erase 1`, whose cardinality is
  `n - 1` (with `Nat` truncated subtraction handling `n = 0, 1`
  correctly).
* `pow_primeCounting_le_pow_pred (n : ℕ) (hn : 1 ≤ n) :
  n ^ Nat.primeCounting n ≤ n ^ (n - 1)` — one-line via
  `Nat.pow_le_pow_right`, analogous to Iter 13's
  `pow_primeCounting_le_pow_self`.
* `lcmRange_le_pow_pred (n : ℕ) : lcmRange n ≤ n ^ (n - 1)` —
  the strict improvement over Iter 13's
  `lcmRange_le_pow_self_via_primeCounting`. Saves one factor of `n`
  in the exponent — concretely: `n = 4` gives `lcmRange 4 = 12 ≤ 64`
  (Iter 14) vs `≤ 256` (Iter 13); `n = 10` gives `≤ 10⁹` vs `≤ 10¹⁰`.

Build pending; proof bodies use only Mathlib API already exercised
by Iter 13 (`Finset.card_erase_of_mem`, `Finset.card_le_card`,
`Nat.not_prime_zero`, `Nat.not_prime_one`, `Nat.pow_le_pow_right`).
File 560 → 657 lines (+97), theorems 40 → 43 (+3),
definitions/sorries/axiomCount unchanged.

----

Iteration 13 (2026-05-09, retained for context): **prime-counting
subordination chain**. Three new theorems make the dependency
`Iter 11 ⟹ Iter 13 ⟹ Part 3` explicit by establishing the chain
`lcmRange n ≤ n^π(n) ≤ n^n`. The middle step is the trivial
`π(n) ≤ n` bound (`primeCounting_le_self`), proved by observing
that the prime filter on `Finset.range (n+1)` excludes `0` and so
fits inside `(Finset.range (n+1)).erase 0`, which has `n` elements.
Build pending; proof bodies use only Mathlib API already exercised
by earlier iters (`Nat.count_eq_card_filter_range`,
`Finset.card_erase_of_mem`, `Nat.pow_le_pow_right`). File 488 → 560
lines (+72), theorems 37 → 40 (+3), definitions/sorries/axiomCount
unchanged.

----

Iteration 12 (2026-05-09, retained for context): **three independent
surgical fixes** to unblock the build for iters 5–11 (which all
merged with `(build pending)` status). Empirically discovered by
docker-build of iter 11 plus targeted re-investigation: the original
"single drift" diagnosis from the iter 11 PR was incomplete — only
one of the three errors is true Mathlib drift; the other two are
subtle elaboration issues introduced by iter 8 / iter 2 that survived
because the file has not had a clean build since iter 4.

### Fix 1 (line 118 — `pow_dvd_lcmRange`): true Mathlib drift

`Nat.pos_pow_of_pos` was removed from Mathlib (no longer present in
v4.26.0; absent from current docs). The replacement `Nat.pow_pos`
lives in core Lean's `Init.Prelude` with signature
`{a n : Nat} (h : 0 < a) : 0 < a ^ n`. One-line swap:

```diff
- dvd_lcmRange (Nat.pos_pow_of_pos k hb) hbkn
+ dvd_lcmRange (Nat.pow_pos hb) hbkn
```

### Fix 2 (line 262 — `lcmRange_dvd_prod_prime_powers`): `rw` cascade

Inside `have hm_eq : m = ∏ p ∈ P, p ^ m.factorization p`, the proof
opened with `rw [h1]` where
`h1 : m = ∏ p ∈ m.primeFactors, p ^ m.factorization p`. Because
`h1`'s RHS contains `m` itself, `rw [h1]` was rewriting `m` on
BOTH sides of the goal `m = ∏ p ∈ P, p ^ m.factorization p`,
mutating the RHS into
`∏ p ∈ P, p ^ (∏ p ∈ m.primeFactors, p ^ m.factorization p).factorization p`
— an unprovable nested expression. Targeted fix: rewrite LHS only.

```diff
-    rw [h1]
+    -- Rewrite only the LHS `m` — `rw [h1]` would also expand `m` inside
+    -- `m.factorization` on the RHS, leaving an unprovable nested goal.
+    conv_lhs => rw [h1]
```

### Fix 3 (line 376 — `lcmRange_succ` forward direction): elaboration

`Finset.dvd_lcm (Finset.mem_range.mpr hi')` had its function `f`
inferred ambiguously as `HAdd.hAdd i` (the curried `i + ·`) instead
of `(· + 1)`, because the goal post-`unfold lcmRange + Finset.lcm_dvd`
did not pin down `f`. The chain via `Nat.dvd_lcm_left _ _` then failed
to unify. Routed through the already-established `dvd_lcmRange` lemma
instead, which has fully-determined types:

```diff
-  · unfold lcmRange
-    apply Finset.lcm_dvd
+  · show (Finset.range (n + 1)).lcm (· + 1) ∣ Nat.lcm (lcmRange n) (n + 1)
+    apply Finset.lcm_dvd
     intro i hi
     have hi_lt : i < n + 1 := Finset.mem_range.mp hi
     by_cases hi_eq : i = n
     · subst hi_eq; exact Nat.dvd_lcm_right _ _
-    · have hi' : i < n := by omega
-      exact dvd_trans (Finset.dvd_lcm (Finset.mem_range.mpr hi'))
-        (Nat.dvd_lcm_left _ _)
+    · have hi' : i + 1 ≤ n := by omega
+      have h_dvd : i + 1 ∣ lcmRange n := dvd_lcmRange (Nat.succ_pos _) hi'
+      exact dvd_trans h_dvd (Nat.dvd_lcm_left _ _)
```

Reverse direction unchanged.

### Net delta

Three surgical edits totaling ~10 lines changed. No new theorems, no
new imports, no API redesign. Proof content of iters 5–11 (Chebyshev
decomposition forward + reverse + equality, prime-counting bound,
primeCounting reformulation) is preserved verbatim and verified-buildable
for the first time after iter 12 merges.

Iteration 11 (#17401 merged): reformulates Iter 10's prime-counting
bound in Mathlib's `Nat.primeCounting` vocabulary —
the literal published form of the bound:

- `lcmRange_le_pow_primeCounting (n : ℕ) :
   lcmRange n ≤ n ^ Nat.primeCounting n`

A one-line corollary of Iter 10's `lcmRange_le_pow_card_primes_le`
plus the standard identification
`Nat.primeCounting n = ((Finset.range (n+1)).filter Nat.Prime).card`
via `Nat.count_eq_card_filter_range` (cf. the analogous central-binomial
bound `(2n).choose n ≤ (2n) ^ π(2n)` in
`ChebyshevPNTBridgeOQ01.lean:140-147` for the pattern).

This is content-light but vocabulary-important: the bound now reads
in standard PNT-statement form $\\text{lcm}(1,...,n) \\leq n^{\\pi(n)}$
and is directly compatible with Mathlib's `Nat.primeCounting` API
(monotonicity, asymptotics, etc.) for downstream chaining. New import:
`Mathlib.NumberTheory.PrimeCounting`.

Iteration 10 (#17369 merged): extracted the **first non-trivial
published-bound** from the closed Chebyshev decomposition:

- `lcmRange_le_pow_card_primes_le (n : ℕ) :
   lcmRange n ≤ n ^ ((Finset.range (n+1)).filter Nat.Prime).card`

Equivalently `lcmRange n ≤ n ^ π(n)`, where `π(n)` is the
prime-counting function. Strictly weaker than Hanson's `3 ^ n` (since
`π(n) ~ n / log n` by PNT, so `n ^ π(n) ~ n ^ {n/log n}` grows
super-exponentially), but a non-trivial sharpening of the trivial
`n ^ n` bound (Part 3 of the file): this saves the contribution of
all *composite* `k ∈ {1,...,n}` via prime-power coalescing.

The proof is short (~15 lines) and follows immediately from the
Iter 9 Chebyshev identity:

1. `n = 0`: `lcmRange 0 = 1` and the prime-filter is empty
   (0 isn't prime), so RHS = `0 ^ 0 = 1`. Closes by `simp`-style
   `Finset.range_one + Finset.filter_singleton + Nat.not_prime_zero`.
2. `n ≥ 1`: rewrite via `lcmRange_eq_prod_prime_powers`; bound each
   factor `p ^ ⌊log_p n⌋ ≤ n` by `Nat.pow_log_le_self p hn.ne'`;
   collapse `∏ _ ∈ S, n = n ^ S.card` via `Finset.prod_const`.

Iteration 9 (#17333 merged): closed the antisymmetric **Chebyshev
prime-power equality** by `Nat.dvd_antisymm`:

- `lcmRange_eq_prod_prime_powers (n : ℕ) :
   lcmRange n = ∏ p ∈ (Finset.range (n+1)).filter Nat.Prime,
                 p ^ Nat.log p n`

Iteration 8 (#17312 merged): closed the **reverse direction of
Chebyshev's decomposition**, complementing Iter 7's forward direction:

- `lcmRange_dvd_prod_prime_powers (n : ℕ) :
   lcmRange n ∣ ∏ p ∈ (Finset.range (n+1)).filter Nat.Prime, p ^ Nat.log p n`

Routes through `Nat.factorization`: write
`m = ∏_{p ∈ m.primeFactors} p^(m.factorization p)` via
`Nat.factorization_prod_pow_eq_self`, extend the index set, and bound
each exponent by `Nat.log p n` using `Nat.le_log_of_pow_le`.

Iteration 7 (#17166 merged): closes the **easy direction of
Chebyshev's decomposition**, the major structural milestone of the
last six iterations:

- `prod_prime_powers_dvd_lcmRange (n : ℕ) :
   (∏ p ∈ (Finset.range (n+1)).filter Nat.Prime, p ^ Nat.log p n)
     ∣ lcmRange n`

The proof has two parts:
1. **Helper lemma** `prod_dvd_of_pairwise_coprime` (private; ~22 lines):
   for any Finset ℕ S and function f : ℕ → ℕ, if every f p (for p ∈ S)
   divides N and the f p are pairwise coprime, then ∏ f p ∣ N.
   Standard Finset.induction; combines `Nat.Coprime.prod_right` (lift
   pairwise to coprime-with-product) with `Nat.Coprime.mul_dvd_of_dvd_of_dvd`.
   Direct parallel of `Erdos1057Problem.prod_primes_dvd_of_each_dvd`,
   abstracted over f to support prime-power factors.
2. **Main theorem** (8 lines on top of helper): n=0 case dispatches via
   `Nat.not_prime_zero` (range 1 = {0}, 0 ∉ Prime ⇒ filter = ∅);
   n ≥ 1 case applies the helper with f = (· ^ Nat.log · n), feeding
   `prime_pow_dvd_lcmRange` (each-factor-divides) and
   `coprime_prime_pow_pow_of_ne` (pairwise-coprime).

Iteration 6 (#17128 merged): added `coprime_prime_pow_pow_of_ne :
∀ {p q}, p.Prime → q.Prime → p ≠ q → ∀ a b, Coprime (p^a) (q^b)`.

Iteration 5 (#17021 merged): added the prime-power
specialization on top of Iteration 3's `pow_dvd_lcmRange`:

- `prime_pow_dvd_lcmRange : ∀ {p n : ℕ}, p.Prime → 1 ≤ n →
   p ^ Nat.log p n ∣ lcmRange n`

The proof is a one-line specialization of `pow_dvd_lcmRange`, using
`Nat.pow_log_le_self p hn'` to discharge `p ^ Nat.log p n ≤ n`. New
imports: `Mathlib.Data.Nat.Log`, `Mathlib.Data.Nat.Prime.Basic`. This
is the maximal-prime-power half of Chebyshev's decomposition
`lcm(1,...,n) = ∏_{p prime ≤ n} p ^ ⌊log_p n⌋`.

Iteration 3 (#16772 merged): added `pow_dvd_lcmRange : 0 < b → b^k ≤ n
→ b^k ∣ lcmRange n` — the generic power-divisibility lemma whose prime
specialization Iteration 5 just discharged.

Iteration 2 (#16704 merged): added foundational structural lemmas:
- `lcmRange_succ`: lcm(1,...,n+1) = Nat.lcm (lcmRange n) (n+1).
- `lcmRange_dvd_lcmRange_of_le`: divisibility monotonicity.
- `lcmRange_monotone`: numerical monotonicity.

Iteration 1 (bootstrap, completed 2026-05-07):
- Provable elementary bounds: lcmRange n ≤ n!, lcmRange n ≤ n^n.
- Numerical verification of Hanson's bound for n ∈ {1..10, 12, 15, 20}.
- Axiom statement of the general claim with documentation of proof
  strategy and Mathlib gaps.

## Active Approach

**Approach (canonical, blocked on Mathlib infrastructure)**:
Hanson's 1972 Beta-integral approach. Use
`∫₀¹ x^k(1-x)^(n-k) dx = 1/((n+1)·C(n,k))` and
`lcmRange(n+1) · Beta(k, n-k) ∈ ℤ` to derive `3^n` via a
careful summing argument over k ∈ {0,...,n}.

Currently blocked on:
- Mathlib lacks Beta-integral identities in usable form for ℚ-valued
  bounds.
- Mathlib lacks the `primorial → lcm` bridge needed for the easier
  `4^n` intermediate.

## Attempt Count
- Total attempts: 18.
- Current approach attempts: 0 (Approach 1 not started; awaits Mathlib).
- Approaches tried: iters 1–17 as previously documented; iter 18
  (this PR, researcher-9, build pending) — per-prime numerical bounds
  on Iter-16 correction-factor terms: `prime_pow_pred_mul_eq_pow`
  (exponent recurrence `p^(log p n - 1) · p = p^(log p n)`),
  `prime_pow_pred_le_self` (coarse bound `p^(log p n - 1) ≤ n`), and
  `prime_pow_pred_le_div` (sharp bound `p^(log p n - 1) ≤ n / p`).
  These complete the per-prime inequality layer needed to chain
  Iter-16's algebraic factorisation through Iter-17's small-prime
  support filter and then bound the correction product by
  `∏_{p ≤ √n} (n/p)`.

## Blockers
- **Mathlib Beta-integral over ℚ**: not in usable form.
- **Mathlib primorial → lcm bridge**: missing.
- **Mathlib LCM-specific bounds**: none exist.

## Next Action

**Iteration 34a (this slug, researcher-3, merged 2026-05-15T18:06Z, PR #19208)**: **SHIPPED** — Lean ACT
of Iter 33 PREP §2 skeleton (28b-1 bridge bound + Lemma A helper). Build verified,
3066/3066 jobs clean. See `sessions/2026-05-14-iter34-act-28b1-bridge-bound.md`.

**Iteration 34b (this slug, researcher-8, merged 2026-05-15, PR #19258)**: **SHIPPED (doc-only)** — sibling-audit of Iter 32 PREP §4 (28b-2 witness saturation) Lean skeleton at lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. 8 findings; recommends Option A (Helper 2 generalized to `j` parameter; explicit Case A/B split). Audit-corrected LOC estimate: 45-60 LOC. See `sessions/2026-05-15-iter34b-prep-iter32-skeleton-audit.md`.

**Iteration 35 (this slug, researcher-3, merged 2026-05-15T18:01Z, PR #19293)**: **SHIPPED (doc-only)** — 28c assembly path Mathlib bearer audit at lake-pinned SHA. Pin-verifies 5 Mathlib bearers + 1 file-local bearer. Provides ~11-LOC drop-in tactic-mode body (no sorry, no axiom) for `choose_mul_succ_dvd_lcmRange`. Identifies 28c's **independence** from 28b-2 (28c depends only on 28b-1 + Iter 5). See `sessions/2026-05-15-iter35-prep-28c-assembly-path-bearer-audit.md`.

**Iteration 35c (researcher-11, merged 2026-05-15T22:55Z, PR #19316)**: **SHIPPED (doc-only)** — refreshed Current Focus + Next Action + `<slug>.json` `currentState` after the 3-PR drain wave. See `sessions/2026-05-15-iter35c-state-sync-after-drainwave.md`.

**Iteration 35b (researcher-11, merged 2026-05-16T03:53Z, PR #19372)**: **SHIPPED (Lean ACT, build verified)** — ships the Iter 35 PREP #19293 §4.1 drop-in body for `choose_mul_succ_dvd_lcmRange` (Theorem 28c). File state 1616 → 1642 LOC (+26 LOC incl. 14-line docstring + 12-line tactic body); 0 sorries; 1 axiom unchanged; Docker build verified 3066/3066 jobs clean. See `sessions/2026-05-15-iter35b-act-28c-assembly.md`.

**Iteration 36 (THIS PREP, researcher-6, 2026-05-16, post-#19372 merge)**: **SHIPPED (doc-only — paste-ready 28b-2 discharge)** — upgrades #19258 Option A from 3 `sorry`s to: §2 Helper 1 (25 LOC, no `sorry`), §3 Helper 2 (24 LOC, no `sorry`), §4 main lemma Case A (9 LOC, no `sorry`), §5 main lemma Case B sketch (27 LOC outer + 30 LOC residual; 2 nested `sorry`s for arithmetic + filter-card discharge). Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` re-confirmed unchanged. File-local bearer line-pins refreshed post-Iter-35b (Lemma A @ 1468, 28b-1 @ 1545, 28c @ 1598). ACT-readiness gate: **6/8 GREEN, 1/8 AMBER (Case B residual sorries), 1/8 RED (Docker unavailable — host disk 7.1Gi free / 100% capacity; `docker ps` timeout)**. ACT deferred until Docker recovers. Total LOC estimate revised 57→127 (vs #19258). See `sessions/2026-05-15-iter36-prep-28b2-paste-ready-discharge.md`.

**Iteration 35a candidate (next ACT, **paste-ready from Iter 36 PREP** §2-§5 — `exists_witness_choose_saturates_log_succ`)**:
ship the Lean implementation of the 28b-2 witness saturation lemma per
Iter 32 PREP §4 + #19258 §2.4 audit corrections + **Iter 36 PREP §2-§5
paste-ready discharge** (researcher-6, this iter): drop in Helper 1
(25 LOC, no `sorry`), Helper 2 (24 LOC, no `sorry`), main signature +
setup (12 LOC), Case A branch (9 LOC, no `sorry`), Case B body (27 LOC
outer + 30 LOC residual filter; 2 nested `sorry`s for arithmetic +
filter-card discharge). **Iter 36 PREP-revised LOC estimate: ~127 LOC**
(was 45-60 in #19258; ~2× overhead due to Case B `hmp` + `hpf_lt`
derivations + explicit filter-equality lemma). Uses the same
`Nat.factorization_choose` + `Nat.ordProj_dvd` API verified in Iter 34a.
**ACT-readiness**: 6/8 GREEN per Iter 36 PREP §6.2; awaiting Docker
recovery (host disk pressure clears) for build verification.

**Iteration 35b (SHIPPED this iter, assembly via drop-in body from Iter 35 PREP #19293 §4.1)**: combined
Iter 34a's `factorization_succ_mul_choose_le_log_succ` (file line 1545)
with Iter 5's `prime_pow_dvd_lcmRange` (file line 134) via Mathlib's
`Nat.factorization_prime_le_iff_dvd` to derive the Iter 28
ACT master target via unique factorization. **Actual LOC**: 12 LOC tactic body
+ 2 LOC signature + 12 LOC docstring = 26 LOC total (~13 LOC for body+sig
matches Iter 35 PREP estimate). Independent of Iter 35a (28b-2). The 28c assembly does
NOT need the witness existence; it needs only the bridge bound `≤`.

```lean
theorem choose_mul_succ_dvd_lcmRange {n k : ℕ} (hk : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1)
```

**Iteration 36+ candidate (Iter 29 ACT target — Beta-integral identity, original Iter 34 plan superseded by 34a/35a/35b sequencing)**:

```lean
theorem betaIntegral_kn (n k : ℕ) (hk : k ≤ n) :
    ∫ x in (0 : ℝ)..1, x ^ k * (1 - x) ^ (n - k) =
      1 / ((n + 1) * Nat.choose n k)
```

via `Real.betaIntegral` + `Real.Gamma_nat`. Combined with 35b's
divisibility statement, this gives Hanson's bridge identity directly.

**Synergy with the numerical floor**: any Iter 35+ Lean ACT yields
`lcmRange n ≤ 3^n` for `n ≥ n₀` for some threshold `n₀ ≥ 0`. The
existing floor `hanson_n1..hanson_n100` covers `n ≤ 100`, so the
operative slack budget for the remaining roadmap is `n₀ ≤ 100`.

**Anti-targets** (carried over from Iter 28 PREP §"Anti-targets"):

* ❌ Don't upstream Mathlib's tighter `θ`-bound from this slug
  (Routes A and C are PNT-blocked in Mathlib v4.26.0).
* ❌ Don't tighten the `(n/2)^√n` correction envelope (Iter 23/24 are
  loose by design; Iter 26 falsifies the asymptotic-threshold route).
* ❌ Don't extend `hanson_n*` numerical floor beyond `n ≤ 100`
  (Iter 27 margin already 7.4 × 10⁶; further numerical work is
  busywork — Iter 30 §"Honest gap 4" confirms).

**Long-term paths still open:**

1. **Intermediate `lcm(1..n) ≤ 4^n`** via primorial bridge: blocked on
   the Mathlib bridge `lcm(1..n) ≤ n · primorial(n)`. Note (Iteration 3
   insight): the literal `≤ n · primorial(n)` form is FALSE
   (counterexample n=9: 2520 > 1890). Correct route is via Chebyshev's
   prime-power formula above. **Update (Iter 25 + Iter 26)**: the
   structural Chebyshev envelope `lcmRange n ≤ 4^n · (n/2)^√n`
   (Iter 25) is strictly larger than `4^n` (since `(n/2)^√n ≥ 1`
   for `n ≥ 2`), so this envelope ALSO does not close the `≤ 4^n`
   intermediate without further refinement.

2. **Full Hanson `3^n`** (Beta-integral + Chebyshev, Route B): Iter
   28-33 PREP chain (Route B, this slug) reduces this to a ~250-LOC
   Lean ACT split across Iter 34a-37+ (**34a + 35b now shipped**; 35a + 36+ pending).

Either result discharges the parent file's `lcm_hanson_bound` axiom.

## (Historical) original Iter 34 plan (superseded by 34a/35a/35b sequencing above)

**Iteration 34 candidate (Route B, Iter 28 ACT — `choose_mul_succ_dvd_lcmRange`)**:
ship the Lean theorem

```lean
theorem choose_mul_succ_dvd_lcmRange (n k : ℕ) (hk : k ≤ n) :
    (n + 1) * Nat.choose n k ∣ lcmRange (n + 1)
```

The Iter 28-33 PREP chain reduces this to two key sub-lemmas (Iter 31 §4
decomposition), both PREP-proven on paper:

* **28b-1** (Iter 33 PREP, #18730): for any `n ≥ 1`, `0 ≤ k ≤ n`, and
  prime `p`, `v_p((n+1) · C(n,k)) ≤ ⌊log_p(n+1)⌋`. Residue-arithmetic
  proof; ~25-LOC Lean target.
* **28b-2** (Iter 32 PREP, #18682): the explicit witness
  `k₀ = (n+1) - p^e` (with `e = ⌊log_p(n+1)⌋`) saturates the 28b-1 bound
  for any prime `p ≤ n+1`. Residue-arithmetic proof (no `Nat.digits`).
* **28b-3** (assembly): combine 28b-1 with **Iter 5's**
  `prime_pow_dvd_lcmRange` (file line 133) and **Iter 16's**
  `lcmRange_eq_prod_prime_powers` to obtain the divisibility statement
  via unique factorization. Pen-and-paper sketch in Iter 31 §4.3.

**Estimated cost**: 80-120 Lean lines (Iter 28 PREP estimate) +
~25-LOC 28b-1 + ~25-LOC 28b-2 + ~30-LOC assembly. **Mathlib lemmas
needed** (audited at pinned rev `2df2f0150c2` = `v4.26.0` in Iter 31):

* `Nat.Prime.multiplicity_choose` (Kummer's theorem) at
  `Mathlib/Data/Nat/Choose/Factorization.lean:131`.
* `Nat.factorization_choose` (`v_p(C(n,k)) = #carries`).
* `Nat.factorization_mul` (`v_p(a·b) = v_p(a) + v_p(b)`).
* `Nat.pow_factorization_dvd` / `Nat.factorization_le_iff_dvd`.

**Iteration 35+ candidate (Iter 29 ACT — Beta-integral identity)**:

```lean
theorem betaIntegral_kn (n k : ℕ) (hk : k ≤ n) :
    ∫ x in (0 : ℝ)..1, x ^ k * (1 - x) ^ (n - k) =
      1 / ((n + 1) * Nat.choose n k)
```

via `Real.betaIntegral` + `Real.Gamma_nat`. Combined with Iter 34's
divisibility statement, this gives Hanson's bridge identity directly.
Subsequent ACT iters ship Hanson's polynomial-choice step
(`P(x) ∈ ℤ[x]` of degree `n`) and the analytic bound.

**Synergy with the numerical floor**: any Iter 34+ Lean ACT yields
`lcmRange n ≤ 3^n` for `n ≥ n₀` for some threshold `n₀ ≥ 0`. The
existing floor `hanson_n1..hanson_n100` covers `n ≤ 100`, so the
operative slack budget for the remaining roadmap is `n₀ ≤ 100`.

**Anti-targets** (carried over from Iter 28 PREP §"Anti-targets"):

* ❌ Don't upstream Mathlib's tighter `θ`-bound from this slug
  (Routes A and C are PNT-blocked in Mathlib v4.26.0).
* ❌ Don't tighten the `(n/2)^√n` correction envelope (Iter 23/24 are
  loose by design; Iter 26 falsifies the asymptotic-threshold route).
* ❌ Don't extend `hanson_n*` numerical floor beyond `n ≤ 100`
  (Iter 27 margin already 7.4 × 10⁶; further numerical work is
  busywork — Iter 30 §"Honest gap 4" confirms).

**Long-term paths still open:**

1. **Intermediate `lcm(1..n) ≤ 4^n`** via primorial bridge: blocked on
   the Mathlib bridge `lcm(1..n) ≤ n · primorial(n)`. Note (Iteration 3
   insight): the literal `≤ n · primorial(n)` form is FALSE
   (counterexample n=9: 2520 > 1890). Correct route is via Chebyshev's
   prime-power formula above. **Update (Iter 25 + Iter 26)**: the
   structural Chebyshev envelope `lcmRange n ≤ 4^n · (n/2)^√n`
   (Iter 25) is strictly larger than `4^n` (since `(n/2)^√n ≥ 1`
   for `n ≥ 2`), so this envelope ALSO does not close the `≤ 4^n`
   intermediate without further refinement.

2. **Full Hanson `3^n`** (Beta-integral + Chebyshev, Route B): Iter
   28-33 PREP chain (Route B, this slug) reduces this to a ~250-LOC
   Lean ACT split across Iter 34-37+; the integer-squeeze bridge
   (Iter 34) is the first Lean-amenable target.

Either result discharges the parent file's `lcm_hanson_bound` axiom.

## References

- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` — bootstrap file (HEAD: 1616 LOC, 1 axiom `hanson_bound`, 0 sorries, build verified 3066/3066 jobs since #19208).
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02.lean:410` — parent's
  `axiom lcm_hanson_bound` that this OQ targets.
- `src/data/proofs/basel-problem-oq-01-oq-01-oq-02-oq-03/meta.json` — gallery (note: `lineCount`/`theoremCount` are stale post-Iter-34a — auditor/mechanic-tracked, not in scope for STATE-SYNC).
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/problem.md` — full
  problem statement with three approaches and Mathlib gap analysis.
- **Drain wave PRs (2026-05-15T18:00–18:06Z)**:
  - PR #19208 (Iter 34a ACT, build verified) — 28b-1 bridge bound + Lemma A.
  - PR #19258 (Iter 34b PREP, doc-only) — sibling-audit of Iter 32 PREP §4; Option A audit corrections.
  - PR #19293 (Iter 35 PREP, doc-only) — 28c assembly bearer audit + ~11-LOC drop-in body.
- **Prior STATE-SYNC**: PR #18898 (2026-05-13) — covered Iter 28-33 PREP chain.
