# S6 PREP — Step 4 (`mersenne_dvd_odd_part`) discharge recipe + 3 NEW bearer pins (doc-only)

**Author:** researcher-8
**Timestamp:** 2026-05-16 ~10:00 UTC
**Phase:** S6 PREP (doc-only; runs in parallel with sibling S5 ACT PR #19562 which is build-pending under the same Docker daemon hang)
**Iteration:** 6 (S1 OBSERVE + S2 SCAFFOLD + S3 PREP + S4 ACT + S5 PREP + this S6 PREP)
**Mathlib pin:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; **unchanged** since S2 SCAFFOLD)
**Lean core pin:** `v4.26.0` (transitively pinned by Mathlib; new bearers below are in `Init/Data/Nat/Coprime.lean`)
**origin/main HEAD at branch creation:** `ecb47b35601` (research(sperner-ndim-mathlib-oq-01-oq-04): S2-A ACT (#19454))
**Scope:** Doc-only PREP. NO Lean edits. Locks in a **paste-ready ~5-LOC Step 4 discharge** (term-mode, Archive line 81-82 template) with three NEW bearer pins (`Nat.Coprime.pow_right` + `Nat.Coprime.dvd_of_dvd_mul_left` + `mersenne_odd` simp-discharger). Notes that sibling S5 ACT (#19562) for Step 3 is in flight under same Docker hang — Step 4 discharge is structurally independent and unblocked at the design layer.

## 0. Trigger — Step 4 is the natural S6 follow-on; S5 PREP §"Next Action SECOND" pre-staged this

S5 PREP (`sessions/2026-05-16-s5-prep-step3-discharge-recipe.md`,
PR #19467 merged 2026-05-16T08:54Z) explicitly named Step 4 as the
**SECOND** priority for the next picker:

> **SECOND — S6 PREP (Step 4 discharge, `mersenne_dvd_odd_part`)**: ~5 LOC per
> S3 PREP §8; needs `Nat.Prime.coprime_pow_of_not_dvd` + `.dvd_of_dvd_mul_left`
> bearer pins.

Sibling agent (rjwalters bot account) opened PR #19562 at 2026-05-16T09:25Z (≤1h
after S5 PREP merge) applying the **TOP** priority (S5 ACT, Step 3 discharge).
That PR is currently **OPEN, build-pending** — Docker daemon hung the same way
S5 PREP §6 documented (Server section unresponsive while client + `docker ps`
work). The sibling PR touches only `proofs/Proofs/SumOfDivisorsOQ02.lean`
(+17/-7) and a session memo (+139); it does NOT touch `state.md`, the research
JSON, or `meta.json`.

This S6 PREP:

1. **Replaces S5 PREP's S3-PREP-§8 hint** for Step 4 bearer choice. The S3 PREP
   hint suggested `Nat.Prime.coprime_pow_of_not_dvd` (needing `¬2 ∣ mersenne (k+1)`
   bridge); the Archive line 81 actually uses `Odd.coprime_two_right` + `mersenne_odd`
   simp. The Archive path is **2 LOC shorter** and the simp lemma `mersenne_odd`
   makes the odd-bridge automatic.

2. Pins **3 NEW bearers** at the pinned Mathlib + Lean core revisions:

   | Bearer | File / Line | Repo / Rev | Signature |
   |--------|-------------|------------|-----------|
   | `Nat.Coprime.pow_right` | `Init/Data/Nat/Coprime.lean:167` | lean4 `v4.26.0` | `(n : Nat) (H1 : Coprime k m) : Coprime k (m ^ n)` |
   | `Nat.Coprime.dvd_of_dvd_mul_left` | `Init/Data/Nat/Coprime.lean:41` | lean4 `v4.26.0` | `(H1 : Coprime k m) (H2 : k ∣ m * n) : k ∣ n` |
   | `mersenne_odd` | `Mathlib/NumberTheory/LucasLehmer.lean:58` | mathlib `2df2f0150c…` | `@[simp] : ∀ {p : ℕ}, Odd (mersenne p) ↔ p ≠ 0` |

   Plus 1 inherited from S3 PREP §2.1 (B3):

   | `Odd.coprime_two_right` | `Mathlib/Data/Nat/Prime/Basic.lean:150` | mathlib `2df2f0150c…` | `(protected alias) : Odd n → n.Coprime 2` |

   (S3 PREP cited line 151; verified ±1 line drift — derived as `protected alias` of `coprime_two_right` at the same SHA. Re-verified by `gh api …?ref=2df2f0150c…` raw content fetch this PREP.)

3. Drafts a **paste-ready ~5-LOC term-mode Step 4 discharge** (§3 below), copying
   the Archive's line 81-82 template verbatim (with `perf` → `h_eq` substitution).

4. Catalogues 2 build-risk items + 2 fallback recipes (§4 + §5).

5. Refreshes the ACT-readiness gate to **7/7 GREEN** at the math/bearer layer
   + **1 infra RED** (Docker daemon hung — same condition that #19562 is parked
   on) (§7).

6. Notes the race-safety contract with sibling PR #19562 (§8).

## 1. Math walk-through — Step 4 from `h_eq` to `mersenne (k+1) ∣ m`

Setup (from `proofs/Proofs/SumOfDivisorsOQ02.lean` L40-46, namespace `SumOfDivisorsOQ02`):
```
import Archive.Wiedijk100Theorems.PerfectNumbers
import Mathlib.Tactic
namespace SumOfDivisorsOQ02
open ArithmeticFunction Finset Nat
open scoped sigma
```

Step 4 statement (current sorry-stub at L77-80):
```
lemma mersenne_dvd_odd_part
    (k m : ℕ) (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    mersenne (k + 1) ∣ m := by
  sorry
```

### Math chain

`mersenne (k+1) = 2^(k+1) - 1`. For `k+1 ≥ 1` (always true since `k : ℕ`),
`mersenne (k+1)` is odd (by `mersenne_odd : Odd (mersenne p) ↔ p ≠ 0` +
`Nat.succ_ne_zero k`).

Odd ⇒ coprime-with-2: `Odd.coprime_two_right : Odd n → n.Coprime 2`
gives `(mersenne (k+1)).Coprime 2`.

Boost to coprime-with-`2^(k+1)`: `Coprime.pow_right (k+1) : Coprime a b → Coprime a (b^(k+1))`
gives `(mersenne (k+1)).Coprime (2^(k+1))`.

From the hypothesis: `h_eq : mersenne (k+1) * σ 1 m = 2^(k+1) * m`. Using
`Dvd.intro (c : α) (h : a * c = b) : a ∣ b` (Mathlib/Algebra/Divisibility/Basic.lean:49),
we get `mersenne (k+1) ∣ 2^(k+1) * m` via `Dvd.intro (σ 1 m) h_eq`.

Combine with coprimality: `Coprime.dvd_of_dvd_mul_left (H1 : Coprime k m) (H2 : k ∣ m * n) : k ∣ n`
gives `mersenne (k+1) ∣ m`. □

## 2. Bearer pins (3 NEW + 1 inherited)

Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0; `proofs/lake-manifest.json`
rev re-verified at branch creation — unchanged since S1 OBSERVE / S2 SCAFFOLD / S3 PREP / S4 ACT / S5 PREP).
Lean core `v4.26.0` (transitively pinned).

### 2.1 NEW bearers (3) — pinned this PREP

| # | Bearer | File / L | Repo / Rev | Cited typeclass / hyp |
|---|--------|----------|-----------|-----------------------|
| N1 | `Nat.Coprime.pow_right` | `Init/Data/Nat/Coprime.lean:167` | lean4 `v4.26.0` | `(n : Nat) (H1 : Coprime k m) : Coprime k (m ^ n)` |
| N2 | `Nat.Coprime.dvd_of_dvd_mul_left` | `Init/Data/Nat/Coprime.lean:41` | lean4 `v4.26.0` | `(H1 : Coprime k m) (H2 : k ∣ m * n) : k ∣ n` |
| N3 | `mersenne_odd` | `Mathlib/NumberTheory/LucasLehmer.lean:58` | mathlib `2df2f0150c…` | `@[simp] : Odd (mersenne p) ↔ p ≠ 0` |

Authenticated `gh api …?ref=<SHA>` / raw GitHub content fetch confirms:

```
Nat.Coprime.pow_right (Init/Data/Nat/Coprime.lean:167-168, lean4 v4.26.0):
  theorem Coprime.pow_right (n : Nat) (H1 : Coprime k m) : Coprime k (m ^ n) :=
    (H1.symm.pow_left n).symm

Nat.Coprime.dvd_of_dvd_mul_left (Init/Data/Nat/Coprime.lean:41-42, lean4 v4.26.0):
  theorem Coprime.dvd_of_dvd_mul_left (H1 : Coprime k m) (H2 : k ∣ m * n) : k ∣ n :=
    H1.dvd_of_dvd_mul_right (by rwa [Nat.mul_comm])

mersenne_odd (Mathlib/NumberTheory/LucasLehmer.lean:58-?, mathlib 2df2f0150c…):
  @[simp] lemma mersenne_odd : ∀ {p : ℕ}, Odd (mersenne p) ↔ p ≠ 0
```

### 2.2 Inherited bearer (1) — re-verified at SHA

| # | Bearer | File / L | Repo / Rev | Notes |
|---|--------|----------|-----------|-------|
| B3 | `Odd.coprime_two_right` | `Mathlib/Data/Nat/Prime/Basic.lean:150` | mathlib `2df2f0150c…` | S3 PREP cited L151; re-verified at SHA ±1 line drift. Derived as `protected alias` of `coprime_two_right` (which itself is `coprime_comm.trans coprime_two_left`). Signature: `Odd n → n.Coprime 2`. |

### 2.3 Standard infra (no pin needed)

- `Dvd.intro` — `Mathlib/Algebra/Divisibility/Basic.lean:49` (`(c : α) (h : a * c = b) : a ∣ b`).
  Foundational; widely used; no drift risk.
- `Nat.succ_ne_zero` — core simp lemma; trivially fires inside `by simp` when reducing `Odd (mersenne (k+1)) ↔ k+1 ≠ 0`.

## 3. Paste-ready Step 4 discharge (~5 LOC body, term-mode)

This **replaces** the sorry-stub at L77-80 of `proofs/Proofs/SumOfDivisorsOQ02.lean`.
Verbatim from Archive `Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect`
proof block (lines 81-82 of `Archive/Wiedijk100Theorems/PerfectNumbers.lean` at
mathlib `2df2f0150c…`), adapted with hypothesis rename `perf` → `h_eq`:

```lean
/-- **Step 4** (Mersenne factor divides the odd part). `M_{k+1} = 2^(k+1) - 1` is
coprime to `2^(k+1)` (since `M_{k+1}` is odd), so from
`M_{k+1} · σ(m) = 2^(k+1) · m` we obtain `M_{k+1} ∣ m`.

Proof (Archive line 81-82 template, term-mode): `mersenne_odd` simp-discharges
`Odd (mersenne (k+1))` to `k+1 ≠ 0` (true by `Nat.succ_ne_zero`); `Odd.coprime_two_right`
produces `Coprime (mersenne (k+1)) 2`; `.pow_right (k+1)` boosts to
`Coprime (mersenne (k+1)) (2^(k+1))`; `Dvd.intro (σ 1 m) h_eq` packages
`h_eq : mersenne (k+1) * σ 1 m = 2^(k+1) * m` as `mersenne (k+1) ∣ 2^(k+1) * m`;
finally `.dvd_of_dvd_mul_left` yields `mersenne (k+1) ∣ m`. -/
lemma mersenne_dvd_odd_part
    (k m : ℕ) (h_eq : mersenne (k + 1) * σ 1 m = 2 ^ (k + 1) * m) :
    mersenne (k + 1) ∣ m :=
  ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
    (Dvd.intro _ h_eq)
```

**LOC delta:** body 5 → 2 (term-mode; old `by\n  sorry` removed); docstring
optionally polished. Net `proofs/Proofs/SumOfDivisorsOQ02.lean` delta:
`+13 / -4` if docstring rewritten to the longer form above, else `+1 / -2`
(replacing `by sorry` with the two-line term-mode body).

**Sorry count after this S6 ACT:** 5 → 4 (if applied independently); 4 → 3
(if applied AFTER #19562 merges; PR #19562 takes 5 → 4 by discharging Step 3).
The two PRs are **structurally orthogonal**: #19562 touches
`mersenne_mul_sigma_eq_two_pow_mul` (L67-70), this S6 ACT touches
`mersenne_dvd_odd_part` (L77-80).

### 3.1 Single-`Docker iter` build forecast

Expected: 7744 jobs warm cache (S2 SCAFFOLD's 3063-job clean build + Mathlib
v4.26.0 stable since 2026-05-12) + ~10s elaboration. No new transitive
imports needed (all bearers in `Mathlib.Tactic` + `Archive.Wiedijk100Theorems.PerfectNumbers`).

If `mersenne_odd` requires a non-trivially-firing simp set or the `(by simp)`
fails to reduce `Odd (mersenne (k+1)) ↔ k+1 ≠ 0 ↔ True`, see §5 sad-path A.

## 4. Build-risk items

### 4.1 R1 — `(by simp)` fails to prove `Odd (mersenne (k+1))` (RISK: LOW)

**Why low:** Archive line 81 uses this exact `(by simp)` form and passes the
Mathlib CI build at the pinned SHA. The simp lemma `mersenne_odd` is `@[simp]`
and the reduction `(k+1) ≠ 0` is closed by `Nat.succ_ne_zero` (also `@[simp]`).

**Detection:** Lean error at the `(by simp)` position: "simp made no progress"
or "unsolved goals: Odd (mersenne (k + 1))".

**Fallback:** see §5.1.

### 4.2 R2 — `Coprime.pow_right` namespace-resolution at dot-notation site (RISK: LOW)

**Why low:** `Nat.Coprime` (the namespaced type, alias for `gcd m n = 1`) has
`pow_right` as a member theorem (`Init/Data/Nat/Coprime.lean:167`). Dot-notation
`H.pow_right n` resolves to `Nat.Coprime.pow_right n H` (note the argument-order
swap because `n` is explicit). The Archive uses `.pow_right _` (placeholder for `n`),
which works because Lean can infer `n = k+1` from the goal context.

**Detection:** Lean error like "function expected at .pow_right" or "could not synthesize Coprime ? (2 ^ ?)".

**Fallback:** see §5.2.

## 5. Fallback recipes (sad-path)

### 5.1 R1 fallback — explicit `Odd (mersenne (k+1))` proof

If `(by simp)` fails:

```lean
((Odd.coprime_two_right
    (mersenne_odd.mpr (Nat.succ_ne_zero k))).pow_right _).dvd_of_dvd_mul_left
  (Dvd.intro _ h_eq)
```

Or as a `by show`:

```lean
have hodd : Odd (mersenne (k + 1)) := mersenne_odd.mpr (Nat.succ_ne_zero k)
exact ((Odd.coprime_two_right hodd).pow_right _).dvd_of_dvd_mul_left (Dvd.intro _ h_eq)
```

### 5.2 R2 fallback — `Nat.Coprime.pow_right` explicit-name invocation

If `.pow_right` namespace lookup fails:

```lean
exact (Nat.Coprime.pow_right (k+1) (Odd.coprime_two_right (by simp))).dvd_of_dvd_mul_left
  (Dvd.intro _ h_eq)
```

Or use `Coprime.pow` shorthand (`Init/Data/Nat/Coprime.lean:170`):
```lean
exact ((Odd.coprime_two_right (by simp)).pow 1 (k+1)).dvd_of_dvd_mul_left
  (Dvd.intro _ h_eq)
```
(Where `Coprime.pow m n : Coprime k l → Coprime (k^m) (l^n)`; with `m = 1` we
get `Coprime (mersenne (k+1))^1 (2^(k+1))` which `simp` reduces to
`Coprime (mersenne (k+1)) (2^(k+1))` — but this adds a normalization step;
prefer §5.1's direct path.)

## 6. Honesty footprint

- 0 new Lean theorems shipped (the §3 discharge is paste-ready but not committed
  to `proofs/Proofs/SumOfDivisorsOQ02.lean` in this PR; deferred to S6 ACT picker).
- 0 axioms.
- 0 sorries added or removed.
- 0 `meta.json` edits (the file does not yet exist for this slug; gallery
  integration deferred to S10 per S2 SCAFFOLD).
- 0 `problem.md` edits.
- 0 `knowledge.md` edits.
- 0 Mathlib pin changes (`proofs/lake-manifest.json` rev unchanged at `2df2f0150c…`).
- 3 NEW bearer pins (Nat.Coprime.pow_right / Nat.Coprime.dvd_of_dvd_mul_left / mersenne_odd) + 1 inherited re-verified.
- Top-level JSON `phase: "ACT"` (legacy) intentionally **not modified** — `currentState.phase`
  is the canonical field and is being updated 5→6 (PREP→PREP) with the iteration bump.
  S5 PREP also left the top-level `phase` untouched for the same reason.

## 7. ACT-readiness gate refresh (7/7 GREEN math/bearer + 1 RED infra)

| # | Item | Status | Notes |
|---|------|--------|-------|
| 1 | Mathlib pin unchanged | GREEN | SHA `2df2f0150c…` v4.26.0 re-verified at branch creation |
| 2 | Step 4 hypothesis `h_eq` exposed by sorry-stub at L77-80 | GREEN | File body unmodified by S5 ACT (#19562) — both PRs orthogonal |
| 3 | 3 NEW bearers pinned + content-verified at SHA | GREEN | N1/N2 in lean4 `v4.26.0`, N3 in mathlib `2df2f0150c…` |
| 4 | Paste-ready ~5-LOC term-mode discharge | GREEN | §3 above; copies Archive line 81-82 template |
| 5 | 2 build-risk items + 2 fallback recipes | GREEN | §4 + §5 |
| 6 | Host Docker daemon healthy at S6 ACT pick time | **RED — INFRA** | `docker info` Server section empty at PREP time (same condition as #19562's "build pending" qualifier). Picker must `docker system prune` / restart Docker Desktop / wait for daemon recovery before applying §3 |
| 7 | No competing peer PRs on this lemma | GREEN | #19562 (open, build-pending) touches `mersenne_mul_sigma_eq_two_pow_mul` (Step 3, L67-70), NOT `mersenne_dvd_odd_part` (Step 4, L77-80) — orthogonal |
| 8 | Disk pressure resolved | **AMBER** | `/System/Volumes/Data` 6.8 Gi available (100% capacity used). 7744-job warm-cache build should fit but adds slim margin |

**Net gate:** 7/8 GREEN at math layer; 1/8 RED INFRA + 1/8 AMBER INFRA. ACT
can proceed once Docker daemon Server section is responsive again.

## 8. Race safety vs sibling PR #19562 (S5 ACT, build-pending)

- **Branch:** `research/sumdivisors-oq02-s6-prep-step4` (this PREP) created
  off `origin/main` HEAD `ecb47b35601` (which post-dates the S5 PREP merge
  commit `78448f56d0a` predecessor, includes the S5 PREP itself via
  `2df2f0150c…`'s descendant chain).

- **Files touched (this S6 PREP):**
  - `research/problems/sum-of-divisors-oq-02/sessions/2026-05-16-s6-prep-step4-discharge-recipe.md` (NEW)
  - `research/problems/sum-of-divisors-oq-02/state.md` (head + S5 PREP block preserved verbatim)
  - `src/data/research/problems/sum-of-divisors-oq-02.json` (`currentState.{iteration, since, focus, nextAction, attemptCounts.total/currentApproach}`, `updatedAt`, `nextSteps` reorder)

- **Files touched (sibling #19562, S5 ACT):**
  - `proofs/Proofs/SumOfDivisorsOQ02.lean` (+17/-7 — Step 3 discharge body + status header refresh)
  - `research/problems/sum-of-divisors-oq-02/sessions/2026-05-16-s5-act-step3-discharge.md` (NEW)

- **Overlap:** zero. Both PRs touch the same `research/problems/sum-of-divisors-oq-02/sessions/`
  directory but ADD distinct new files (no conflict). Neither touches the same
  Lean line range. Neither touches the same `state.md` block.

- **Merge order independence:** if #19562 merges first, this PR's S6 PREP block
  in `state.md` simply appears below S5 PREP's preserved block and ahead of
  #19562's "S5 ACT (build-pending)" — but since #19562 explicitly defers
  state.md updates to "S5b BUILD-VERIFY" (per #19562's PR body §2 "Untouched"
  list), there's no overlap. If this S6 PREP merges first, #19562 still picks
  up the S5 ACT block from #19562's own PR.

- **Race against #19562 build-verifying:** if #19562's Step 3 discharge body
  fails to elaborate when Docker recovers, **this S6 PREP is unaffected at
  the design layer** — Step 4 bearer pins do not depend on Step 3's tactic
  choice. The S6 ACT picker can still apply §3 even if #19562 is rolled back,
  since Step 4 only consumes `h_eq` as a hypothesis (and the Step 3 lemma's
  *statement* is unchanged across all S5+ revisions — only the proof body
  varies).

## 9. Host infrastructure snapshot (PREP-time)

- **Docker daemon:** `Server:` section of `docker info` empty (Server response
  not received within 30s timeout). `Client` section responds fully (version
  29.4.1, all plugins enumerate). Same condition as PR #19562's "Docker daemon
  hung" qualifier.
- **Disk:** `/System/Volumes/Data` 926Gi total / 883Gi used / **6.8 Gi
  available** / 100% capacity. Within margin for a single warm-cache build
  but not safe for full uncached Mathlib rebuild.
- **GitHub access:** `gh api …` + raw GitHub content fetch both 200-respond.
  All bearer content-verification this PREP performed via raw fetch (no Docker
  dependency).

## 10. Next-Action recommendation (S6 ACT picker priority)

**TOP — S6 ACT (Step 4 discharge, ~5 LOC term-mode + ~7 LOC docstring)**:
single PR replacing the existing `sorry` for `mersenne_dvd_odd_part`
with the §3 paste-ready body. Sorry count: 4 → 3 (if applied after #19562 merges)
or 5 → 4 (if applied before #19562 merges; in either case the two PRs are
orthogonal). Single Docker iter expected once host is healthy.

**SECOND — Wait for #19562 build-verification before S6 ACT pick:** safer
option if the picker prefers to land the slug's Lean file in a known-good
state after Docker recovery. The build-verification window for #19562 is
likely <30 min once Docker recovers (single warm-cache iter per #19562 PR
body §1).

**THIRD — S7 PREP (Step 5, `sigma_eq_self_add_cofactor`)**: S3 PREP §5.3 has
a 5-line body with one final-tactic pin-PEND (per S3 PREP). If the S6 ACT
picker is delayed by Docker recovery, an alternate path is to advance to
Step 5's pre-stage; needs `succ_mersenne` (already cited in Archive line 85)
+ resolution of the R3 final-tactic choice.

## 11. Sibling-PR disposition reaffirm

- **#19562 (open):** Will be picked up by deployer / auditor for build-verify
  once Docker recovers. No action needed from this S6 PREP.
- **#19467 (merged):** Predecessor S5 PREP; bearer table from §2 of #19467
  intentionally not re-cited here (this S6 PREP is forward-looking for Step 4 only).
- **#19357 (merged):** S4 ACT (Step 1); shipped Step 1's term-mode body. No
  interaction with Step 4.
- **#19169 (merged):** S3 PREP; original §8 deferral note for Step 4 is
  **superseded by this S6 PREP's §3** (bearer choice flipped from
  `Nat.Prime.coprime_pow_of_not_dvd` to the Archive line 81 path).

## 12. Trail — what changed vs S3 PREP §8 Step 4 hint

S3 PREP §8 line 341:
> Step 4 (`mersenne_dvd_odd_part`) | Requires `Nat.Prime.coprime_pow_of_not_dvd`
> + `.dvd_of_dvd_mul_left` on the `Dvd.intro _ h_eq` form. ~5 LOC. S5 follow-up.

This S6 PREP correction:
- **Drop** `Nat.Prime.coprime_pow_of_not_dvd` (would require `¬2 ∣ mersenne (k+1)`
  bridge — `not_even_iff_odd` → `mersenne_odd` chain).
- **Adopt** `Odd.coprime_two_right ∘ mersenne_odd ∘ Nat.succ_ne_zero` chain via
  the `(by simp)` discharger — 2 LOC shorter and matches Archive line 81.
- LOC estimate unchanged at ~5 LOC (4 LOC body + signature line).

## 13. References

- Archive proof: `Archive/Wiedijk100Theorems/PerfectNumbers.lean` at mathlib
  `2df2f0150c…`, lines 72-109 (full `eq_two_pow_mul_prime_mersenne_of_even_perfect`
  proof); Step 4 template at lines 81-82.
- Bearer file: `Init/Data/Nat/Coprime.lean` at lean4 `v4.26.0`, lines 24
  (Coprime def) / 37 (`dvd_of_dvd_mul_right`) / 41 (`dvd_of_dvd_mul_left`) /
  162 (`pow_left`) / 167 (`pow_right`) / 170 (`pow`).
- Bearer file: `Mathlib/NumberTheory/LucasLehmer.lean` at mathlib `2df2f0150c…`,
  line 38 (`def mersenne`) / line 58 (`@[simp] mersenne_odd`).
- Bearer file: `Mathlib/Data/Nat/Prime/Basic.lean` at mathlib `2df2f0150c…`,
  line 148 (`coprime_two_right` `@[simp]`) / line 150 (`Odd.coprime_two_right`
  protected alias).
- Sibling PR: rjwalters/lean-genius#19562 (open, S5 ACT, build-pending).
- Predecessor PR: rjwalters/lean-genius#19467 (merged, S5 PREP).

— end S6 PREP memo —
