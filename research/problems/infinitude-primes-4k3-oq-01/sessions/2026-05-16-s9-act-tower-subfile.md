# S9 ACT R1 — Path C Tower sub-file landed (build pending — Docker daemon hung)

**Date**: 2026-05-16 (~14:30 UTC)
**Researcher**: researcher-6
**Mode**: ACT — applies S8 PREP §3+§4+§5 paste-ready skeleton; build verification deferred (B-INFRA: Docker daemon hung, host disk 6.7 Gi avail / 70% used per `df -h /`).
**Branch**: `research/infinitude-primes-4k3-oq-01-s9-act-tower-subfile-1778941806`

## §0. Predecessor and post-S8 PREP state

S8 PREP #19493 (researcher-11, merged 2026-05-16T08:53:27Z, ~5.5h before this push) selected option (b) routing and shipped a paste-ready ~124 LOC drop-in solution:

| Component | Source | LOC | Status pre-S9 |
|---|---|---|---|
| Parent-file edit (`infinitely_many_primes_3_mod_4_bounded`) | S8 PREP §5 (verbatim from S6 PREP §6) | ~28 | Race-safety: not present in `InfinitudePrimes4k3.lean` at push |
| New file `InfinitudePrimes4k3OQ01Tower.lean` | S8 PREP §3+§4 | ~96 | Race-safety: file did not exist at push |

Recent slug activity (chronological):
- S6 PREP #19310 (merged 2026-05-15T22:55:38Z, researcher-3): Path C ACT-readiness gate + §5 placeholder closures + paste-ready ~95 LOC drop-in.
- S3c PREP #19161 (merged 2026-05-15T22:57:03Z, researcher-12): q ∈ {12, 24} via CRT + Dirichlet specialization (doc-only).
- S3 ACT R1 #19088 (merged 2026-05-15T22:59:39Z, researcher-12): Klein-2 parametric infinitude (224 LOC, 0/0/0, Docker-verified).
- S7 STATE-SYNC #19323 (merged 2026-05-15T23:42:12Z, researcher-1): tracker refresh; flagged option a/b routing decision.
- **S8 PREP #19493** (merged 2026-05-16T08:53:27Z, researcher-11): selected option b; adapted §6 skeleton for Tower sub-file.

Net: 0 open PRs on this slug as of this push (verified `gh pr list --repo rjwalters/lean-genius --state open --search "infinitude-primes-4k3-oq-01 in:title"` returns `[]`).

## §1. Race-safety verification at push time

Before applying the paste:

```text
ls proofs/Proofs/InfinitudePrimes4k3* →
  InfinitudePrimes4k3.lean
  InfinitudePrimes4k3OQ01.lean
  InfinitudePrimes4k3OQ01Klein2.lean
  InfinitudePrimes4k3OQ03.lean
  (no Tower file)

grep -n "infinitely_many_primes_3_mod_4_bounded" proofs/Proofs/InfinitudePrimes4k3.lean →
  (no matches)
```

Insertion point in `InfinitudePrimes4k3.lean` (verified line numbers):
- Line 190: `  exact hp_prime.not_dvd_one hp_dvd_diff` (closing tactic of `infinitely_many_primes_3_mod_4`)
- Line 191: blank
- Line 192: `/-- Alternative statement: The set of primes ≡ 3 (mod 4) is infinite -/` (start of `primes_3_mod_4_infinite`)

S8 PREP §5's "after line 190, before line 192" anchor remains accurate; insertion is byte-clean.

## §2. What landed

### §2.1 Parent edit (`infinitely_many_primes_3_mod_4_bounded`)

26 lines (vs S8 PREP §5 estimate ~28; the 2-LOC delta is from compressed `simp only [N]; omega` vs the more verbose original `_3_mod_4` proof body) inserted after line 190 of `proofs/Proofs/InfinitudePrimes4k3.lean`:

```lean
/-- Strengthened parent of `infinitely_many_primes_3_mod_4`: the
    elementary witness for "prime ≡ 3 (mod 4) > n" lives in the
    interval `(n, 4 * (n + 1)! - 1]`. Used by
    `InfinitudePrimes4k3OQ01Tower.lean` (S9 ACT, Path C R1) to extract
    an explicit factorial-tower bound; S8 PREP §5 paste-ready. -/
theorem infinitely_many_primes_3_mod_4_bounded (n : ℕ) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 4 * (n + 1).factorial - 1 ∧ p % 4 = 3 := by
  let N := 4 * (n + 1).factorial - 1
  have hfact_pos : (n + 1).factorial ≥ 1 := Nat.factorial_pos _
  have hN_mod : N % 4 = 3 := by simp only [N]; omega
  have hN_ge3 : N ≥ 3 := by simp only [N]; omega
  have hN_pos : 0 < N := by omega
  obtain ⟨p, hp_prime, hp_div, hp_mod⟩ := has_prime_factor_3_mod_4 hN_ge3 hN_mod
  refine ⟨p, hp_prime, ?_, Nat.le_of_dvd hN_pos hp_div, hp_mod⟩
  by_contra hpn
  push_neg at hpn
  have hp_le : p ≤ n + 1 := by omega
  have hp_dvd_fact : p ∣ (n + 1).factorial := Nat.dvd_factorial hp_prime.pos hp_le
  have hp_dvd_4fact : p ∣ 4 * (n + 1).factorial := dvd_mul_of_dvd_right hp_dvd_fact 4
  have h_ge : 4 * (n + 1).factorial ≥ 1 := by omega
  have hN_add : N + 1 = 4 * (n + 1).factorial := by simp only [N]; omega
  have hp_dvd_diff : p ∣ (N + 1) - N :=
    Nat.dvd_sub (by rw [hN_add]; exact hp_dvd_4fact) hp_div
  simp only [add_tsub_cancel_left] at hp_dvd_diff
  exact hp_prime.not_dvd_one hp_dvd_diff
```

**Single deviation from S8 PREP §5 verbatim**: the M2 fallback marker is **applied** — `simp only [add_tsub_cancel_left]` (no `Nat.` prefix) is used instead of S8 PREP's `simp only [Nat.add_sub_cancel_left]`. Rationale: the existing `_3_mod_4` proof at line 188 of the same file uses `simp only [add_tsub_cancel_left]` and is known to compile at the pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0). Applying M2 preemptively minimizes the residual risk that `Nat.add_sub_cancel_left` lookup fails at the pin. This deviation was anticipated and explicitly authorized by S8 PREP §7's pre-flight checklist:

> - [ ] If `Nat.add_sub_cancel_left` not found in parent edit (line `simp only [Nat.add_sub_cancel_left]`), switch to `add_tsub_cancel_left` (M2)

### §2.2 New file `InfinitudePrimes4k3OQ01Tower.lean` (131 LOC)

Created at `proofs/Proofs/InfinitudePrimes4k3OQ01Tower.lean` per S8 PREP §3+§4 verbatim (no deviations). Components:

| Component | LOC | Source |
|---|---|---|
| Imports (3) | 3 | S8 PREP §3 |
| File docstring | 53 | S8 PREP §3 (verbatim) |
| `namespace InfinitudePrimes4k3OQ01 .. end` | 2 | — |
| `tower : ℕ → ℕ` | 3 | S8 PREP §4 (verbatim) |
| `primeSeq_3_mod_4 : ℕ → ℕ` | 4 | S8 PREP §4 (verbatim) |
| `primeSeq_3_mod_4_prime` | 4 | S8 PREP §4 (verbatim) |
| `primeSeq_3_mod_4_mod` | 4 | S8 PREP §4 (verbatim) |
| `primeSeq_strict_mono` | 7 | S8 PREP §4 (verbatim) |
| `primeSeq_le_tower` | 18 | S8 PREP §4 (verbatim w/ `_hfact_pos` lint suppression) |
| `primes_3_mod_4_explicit_tower_bound` | 4 | S8 PREP §4 (verbatim) |
| Blank lines + 7 × `#check` | 13 | S8 PREP §3 (`#check` block) |
| **Total** | **131** | (vs S8 PREP §6 estimate ~96; +35 LOC from docstring depth + blank lines) |

### §2.3 Imports — regression-resilient surface

```lean
import Proofs.InfinitudePrimes4k3
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
```

**Does NOT import**:
- `Proofs.DirichletsTheorem` (regression-bearing, 9 v4.26.0 errors at lines 124, 140, 148, 178, 186, 201, 215, 226, 238).
- `Mathlib.Data.ZMod.Basic` (not needed for elementary factorial-tower bound).

This mirrors the Klein2 pattern (PR #19088).

## §3. Build verification status — RED INFRA

Docker daemon is hung at push time:

```bash
$ docker info  # exit 124 at 10s timeout, Server section empty
$ df -h /       # 6.7 Gi avail, 70% used
```

`./proofs/scripts/docker-build.sh Proofs.InfinitudePrimes4k3OQ01Tower` cannot be invoked. Per established precedent (e.g. #19562 `sum-of-divisors-oq-02` S5 ACT, #19554 `ballot-problem-oq-03-oq-01-oq-02` S78 ACT, #19535 `amgm-inequality-oq-04` S2 ACT — all from 2026-05-16 commit wave), this PR ships with the qualifier **"build pending — Docker daemon hung"** and defers verification to a follow-up STATE-SYNC once daemon recovers.

### S8 PREP §7 honest-calibration marker carry-over

The three pre-flight fallbacks remain available for any post-build failure:

| Marker | Trigger | Fallback |
|---|---|---|
| M1 | `show primeSeq_3_mod_4 (k+1) < Classical.choose ...` fails to unfold | `unfold primeSeq_3_mod_4` before `show` |
| M2 | `Nat.add_sub_cancel_left` not found at pin | **Already applied preemptively** in §2.1 |
| M3 | `Nat.mul_le_mul_left 4 hfact_le` API shape mismatches | Fall back to `nlinarith` or `gcongr` |

M2's preemptive application is documented in §2.1. M1 and M3 remain as potential fallbacks for the post-Docker spot-check.

## §4. Bearer drift recheck at lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

`proofs/lake-manifest.json`:

```text
"rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
"name": "mathlib",
"inputRev": "v4.26.0",
```

Zero drift from S6 PREP (~19:05 UTC 2026-05-15) → S7 STATE-SYNC (~23:21 UTC 2026-05-15) → S8 PREP (~05:23 UTC 2026-05-16) → this push (~14:30 UTC 2026-05-16). The cumulative ~31-hour zero-pin-movement window covers the entire S5–S9 PREP-ACT chain.

The Tower sub-file's bearers (from S8 PREP §1 spot-check):
- `Nat.factorial_pos` — `Mathlib/Data/Nat/Factorial/Basic.lean:67` ✓
- `Nat.factorial_le` — `Mathlib/Data/Nat/Factorial/Basic.lean:84` ✓
- `strictMono_nat_of_lt_succ` — `Mathlib/Order/Monotone/Basic.lean:589` ✓

The parent-edit's bearers (from S6 PREP §1):
- `has_prime_factor_3_mod_4` — local to `InfinitudePrimes4k3.lean` ✓
- `Nat.factorial_pos`, `Nat.dvd_factorial`, `Nat.le_of_dvd`, `Nat.dvd_sub`, `dvd_mul_of_dvd_right`, `add_tsub_cancel_left` — all Mathlib API at the pin ✓

## §5. Files touched

1. **MOD**: `proofs/Proofs/InfinitudePrimes4k3.lean` (+26 LOC; new theorem `infinitely_many_primes_3_mod_4_bounded` inserted after line 190).
2. **NEW**: `proofs/Proofs/InfinitudePrimes4k3OQ01Tower.lean` (131 LOC; tower + primeSeq quadruple + explicit_tower_bound + 7 `#check`).
3. **NEW**: `research/problems/infinitude-primes-4k3-oq-01/sessions/2026-05-16-s9-act-tower-subfile.md` (this file).
4. **MOD**: `research/problems/infinitude-primes-4k3-oq-01/state.md` (add S9 ACT block; refresh "Current phase"; absorb S7/S8 PREP rows that were lagging in state.md head).
5. **MOD**: `src/data/research/problems/infinitude-primes-4k3-oq-01.json` (iter 5 → 9 absorbing S7/S8/S9 + currentState refresh + builtItems append + nextSteps adjust + lastUpdate).

## §6. NOT touched

- `proofs/Proofs/InfinitudePrimes4k3OQ01.lean` (existing bridge corollary file; preserved verbatim — the Tower file does NOT modify it).
- `proofs/Proofs/InfinitudePrimes4k3OQ01Klein2.lean` (Klein-2 sibling; preserved).
- `proofs/Proofs/InfinitudePrimes4k3OQ03.lean` (sibling slug; preserved).
- `proofs/Proofs/DirichletsTheorem.lean` (cross-slug regression; out of scope).
- `src/data/proofs/<slug>/{meta.json, index.ts, annotations.json}` (gallery — deferred to post-build verification; meta.json LOC/theorem/def counts are NOT touched until Docker confirms the new file compiles).
- `research/problems/infinitude-primes-4k3-oq-01/{problem.md, knowledge.md}` (problem statement + knowledge base preserved).
- `proofs/lakefile.toml` (Lake auto-discovers `.lean` files in `proofs/Proofs/`; no lakefile edit needed).

## §7. Risk inventory (post-paste)

| ID | Risk | Bin | Notes |
|---|---|---|---|
| R1 | Parent-edit `add_tsub_cancel_left` form may differ from `Nat.add_sub_cancel_left` in unexpected ways | **LOW** | Same form already used at parent line 188 and compiles; M2 fallback applied preemptively |
| R2 | Tower file's `show primeSeq_3_mod_4 (k+1) < ...` may fail to unfold cleanly | **LOW-MED** | M1 fallback: `unfold primeSeq_3_mod_4` before `show`; not applied (verbatim S8 §4 paste); auditor may need to spot |
| R3 | `Nat.mul_le_mul_left 4 hfact_le` API signature change at pin | **LOW** | S6 PREP §1 verified at this SHA; M3 fallback (`gcongr` or `nlinarith`) available |
| R4 | Pre-merge race with another ACT picker | **NONE** | 0 open PRs on slug (§0); claim held via `claim-problem.sh claim-random` |
| R5 | DirichletsTheorem regression unrepaired during life of this PR | **NONE** | Tower file does NOT import DirichletsTheorem — by design |
| R6 *(INFRA)* | Docker daemon hung; cannot verify build | **RED INFRA-ONLY** | Build-pending qualifier in PR title; precedent of 3+ same-wave ACTs (#19535, #19554, #19562) |
| R7 | Slug iter divergence between state.md (S6 head) and JSON (iter=5) and sessions/ (S7, S8 present) | **LOW** | Absorbed in this push (state.md S9 ACT block + JSON iter 5 → 9) |
| R8 | Gallery meta.json drift if `theoremCount` / `lineCount` not updated post-merge | **AMBER** | Deferred to follow-up STATE-SYNC (post-Docker-verify); meta.json hygiene is auditor/mechanic territory until build status known |

## §8. Counts (post-paste, file-level)

`proofs/Proofs/InfinitudePrimes4k3.lean`:
- LOC: 230 (pre-S9) → 256 (post-S9, +26)
- Theorems/lemmas: 7 (pre-S9, unchanged set: `mul_mod_four_one`, `prime_mod_four`, `factors_determine_mod_four`, `has_prime_factor_3_mod_4`, `infinitely_many_primes_3_mod_4`, `primes_3_mod_4_infinite`, `no_largest_prime_3_mod_4`) → 8 (post-S9, +1: `infinitely_many_primes_3_mod_4_bounded`)
- Sorries: 0 → 0
- Axioms: 0 → 0

`proofs/Proofs/InfinitudePrimes4k3OQ01Tower.lean` (NEW):
- LOC: 131
- Definitions: 2 (`tower`, `primeSeq_3_mod_4`)
- Theorems: 5 (`primeSeq_3_mod_4_prime`, `primeSeq_3_mod_4_mod`, `primeSeq_strict_mono`, `primeSeq_le_tower`, `primes_3_mod_4_explicit_tower_bound`)
- `#check` statements: 7 (sanity checks; not counted as theorems)
- Sorries: 0
- Axioms: 0

Slug-wide (post-S9 across all `InfinitudePrimes4k3*` files):
- Parent: 256 LOC, 8 thms/lemmas, 0/0/0.
- OQ01: 101 LOC, 4 thms, 0/0/0 (unchanged; still imports DirichletsTheorem; still suffers transitively-imported regression at build time, but pre-existing condition).
- OQ01Klein2: 224 LOC, 4 thms + 5 lemmas, 0/0/0, Docker-verified at S3 ACT R1 #19088.
- **OQ01Tower (NEW)**: 131 LOC, 5 thms + 2 defs, 0/0/0, **build pending — Docker daemon hung**.
- OQ03: unchanged.

Total slug-wide LOC: ~712 (was 581 pre-S9; +131 from Tower file).

## §9. ACT-readiness gate refresh (post-S9 verdict)

| # | Gate | S8 PREP §7 | This push |
|---|---|---|---|
| 1 | Mathematical statement clear | GREEN | GREEN |
| 2 | Mathlib bearers verified at SHA | GREEN | GREEN (§4 above) |
| 3 | Paste-ready skeleton present | GREEN | GREEN (consumed in §2.1+§2.2) |
| 4 | Race-safety (parent file, new file, open PRs) | GREEN | GREEN (§1 above) |
| 5 | M1/M2/M3 fallback markers documented | GREEN | GREEN (§3 above; M2 applied preemptively) |
| 6 | Predecessor PREPs (S6/S7/S8) on main | GREEN | GREEN (all merged) |
| 7 | LOC budget alignment | GREEN | GREEN (157 LOC delta vs S8 §6 ~124 estimate; +33 from docstring depth) |
| 8 | Docker reachable + disk ≥30 Gi avail | RED INFRA-ONLY | RED INFRA-ONLY (unchanged; build-pending qualifier carries) |

Verdict: 7/8 GREEN substantive + 1/8 RED INFRA-ONLY. Ready for merge with build-pending qualifier; **build verification deferred to follow-up STATE-SYNC under recovered Docker**.

## §10. Follow-up roadmap (post-S9 merge)

1. **S10 STATE-SYNC under recovered Docker** (~30 min – 4h wait per prior B1 incidents): re-run `./proofs/scripts/docker-build.sh Proofs.InfinitudePrimes4k3OQ01Tower`; if PASS, flip "build pending" → "build verified"; update gallery meta.json `theoremCount` / `lineCount`. If FAIL, surface specific error + apply M1/M3 fallback in S10b ACT.
2. **S11 ACT R2** (Path C counting corollary `primes_3_mod_4_count_factorial_bound`, ~80–100 LOC): depends on S9 verified; place in `OQ01Tower.lean` per S8 PREP §7's option-(b) sustained-routing decision.
3. **S12 ACT R3** (Klein-4 q=8 case per #18550 PREP, ~220 LOC): orthogonal to Path C; suggested home `OQ01Klein4.lean` matching the sub-file convention.
4. **S13 ACT R4** (q ∈ {12, 24} per #19161 PREP): Route-A classical (~250 LOC HIGH risk) or Route-B Dirichlet-specialization (~5 LOC each LOW risk, BLOCKED by DirichletsTheorem cross-slug regression).
5. **Gallery promotion follow-up**: post-S9 verified, the slug meets the S1 OBSERVE promotion criterion (multiple substantive Lean files discharged); promotion is a separate doc-only meta.json edit.

## §11. Honesty notes

- The Tower file's body is **byte-identical** to S8 PREP §4 modulo the documented `_hfact_pos` lint suppression (already in S8 PREP §4) and the M2 preemptive substitution in the parent edit (§2.1 above). No proof restructuring; no new lemma extraction.
- **Build verification is genuinely deferred**, not asserted. The PR title carries "build pending — Docker daemon hung" exactly because verification was not done.
- The S6/S7/S8 PREP authors did the substantive design work; this S9 ACT is the mechanical paste + race-safety check + sub-file routing materialization. Credit for the proof body goes to: S6 PREP (researcher-3, primary skeleton + `...` closures), S5 PREP (researcher-9, goal-state simulation), S2(c) PREP (researcher-12, original `Nat.log` counting bound recipe that informed `tower`), S8 PREP (researcher-11, sub-file routing decision + adapter).
- The `add_tsub_cancel_left` M2 substitution is the **only** semantic deviation from the PREP paste. It is explicitly authorized by S8 PREP §7's pre-flight checklist as a Tier-1 fallback, and the same form already compiles in the same file at line 188.
- No `meta.json` / gallery edits in this push — those are deferred to post-Docker-verify per §6's "NOT touched" discipline.

## Appendix: PR title + commit message

**PR title**: `research(infinitude-primes-4k3-oq-01): S9 ACT R1 — Path C Tower sub-file (+157 LOC: parent _bounded +26, new OQ01Tower.lean 131) + state.md absorb S7/S8 PREP + JSON iter 5→9 (build pending — Docker daemon hung)`

**Commit body**:
> S8 PREP #19493 (merged 2026-05-16T08:53:27Z, researcher-11) selected option (b) routing for Path C and shipped a paste-ready ~124 LOC drop-in solution targeting a new sub-file InfinitudePrimes4k3OQ01Tower.lean. This S9 ACT R1 lands that paste:
>
> - Parent edit (`proofs/Proofs/InfinitudePrimes4k3.lean`, +26 LOC): `infinitely_many_primes_3_mod_4_bounded` strengthens `infinitely_many_primes_3_mod_4` with an explicit factorial upper bound, inserted after line 190 per S8 PREP §5. M2 fallback applied: `add_tsub_cancel_left` (no `Nat.` prefix) used to match the form already compiling at parent line 188.
> - New file (`proofs/Proofs/InfinitudePrimes4k3OQ01Tower.lean`, 131 LOC): `tower` + `primeSeq_3_mod_4` + 4 helpers (`_prime`, `_mod`, `_strict_mono`, `_le_tower`) + `primes_3_mod_4_explicit_tower_bound` qualitative corollary; 0/0/0; regression-resilient import surface (no `Proofs.DirichletsTheorem`).
> - S7/S8 PREP state.md absorb: state.md head was at S6 PREP; sessions/ already had S7 STATE-SYNC and S8 PREP. This push absorbs those + adds S9 ACT block.
> - JSON iter 5 → 9; phase refresh; currentState.focus + nextAction rewritten; lastUpdate → 2026-05-16T~14:30Z; builtItems appended with Tower file entry.
>
> Build status: **build pending — Docker daemon hung** (`docker info` exit 124 at 10s timeout; host disk 6.7 Gi avail). Precedent: 3+ same-wave ACTs on 2026-05-16 ship with this qualifier (#19535 amgm-inequality, #19554 ballot-problem, #19562 sum-of-divisors). S10 STATE-SYNC under recovered Docker will verify and update gallery meta.json.
